#![allow(unused)]

use std::{
    collections::{BTreeSet, HashMap},
    sync::{
        atomic::{AtomicUsize, Ordering},
        RwLock,
    },
};

use super::*;

const VERSION_BYTES: usize = std::mem::size_of::<usize>();

/// High-level transaction helpers
pub mod tx {
    /// An error type signalling how a transaction failed
    #[derive(Debug, Clone)]
    pub enum Error {
        /// This transaction failed due to a conflicting concurrent access
        Conflict,
        /// This transaction failed due to an explicit abort from the user
        Aborted,
    }

    /// The result of a transactional operation
    pub type Result<T> = std::result::Result<T, Error>;
}

#[derive(Debug, Clone)]
enum Update {
    Set(Vec<u8>),
    Merge(Vec<u8>),
    Del,
}

#[derive(Debug, Default)]
struct Vsn {
    stable_wts: AtomicUsize,
    pending_wts: AtomicUsize,
    rts: AtomicUsize,
}

/// A transaction
#[derive(Debug)]
pub struct Tx<'a> {
    id: usize,
    db: &'a Db,
    reads: HashMap<Vec<u8>, usize>,
    writes: HashMap<Vec<u8>, Update>,
    aborted: bool,
}

impl<'a> Tx<'a> {
    /// Complete the transaction
    pub fn commit(self) -> tx::Result<()> {
        Err(tx::Error::Aborted)
    }

    /// Give up
    pub fn abort(&mut self) {
        self.aborted = true;
    }

    /// Retrieve a value from the `Db` if it exists.
    pub fn get<K: AsRef<[u8]>>(
        &'a mut self,
        key: K,
    ) -> Result<Option<&'a [u8]>, ()> {
        // check writeset
        if let Some(update) = self.writes.get(key.as_ref()) {
            match update {
                Update::Del => return Ok(None),
                Update::Merge(..) => unimplemented!(
                    "transactional merges not supported yet"
                ),
                Update::Set(v) => return Ok(Some(v)),
            }
        }

        // check readset
        if let Some(observed) = self.reads.get(key.as_ref()) {
            return self.db.bounded_get(key, *observed).map(|opt| {
                opt.map(|(vsn, val)| unsafe {
                    std::slice::from_raw_parts(val.0, val.1)
                })
            });
        }

        // pull key from local cache
        unimplemented!()
    }

    /// Set a key to a new value, returning the old value if it
    /// was set.
    pub fn set<K: AsRef<[u8]>>(
        &mut self,
        key: K,
        value: Value,
    ) -> Result<Option<PinnedValue>, ()> {
        let last = self.get(key)?;

        self.writes
            .insert(key.as_ref().to_vec(), Update::Set(value));

        Ok(last)
    }
}

/// A `Tree` that supports transactional operations.
#[derive(Debug)]
pub struct Db {
    tree: Tree,
    versions: RwLock<HashMap<Vec<u8>, Vsn>>,
    gc_threshold: AtomicUsize,
}

impl Db {
    /// Load existing or create a new `Db` with a default configuration.
    pub fn start_default<P: AsRef<std::path::Path>>(
        path: P,
    ) -> Result<Db, ()> {
        let tree = Tree::start_default(path)?;

        Ok(Db {
            tree,
            versions: RwLock::new(HashMap::new()),
            gc_threshold: 0.into(),
        })
    }

    /// Load existing or create a new `Db`.
    pub fn start(config: Config) -> Result<Db, ()> {
        let tree = Tree::start(config)?;

        Ok(Db {
            tree,
            versions: RwLock::new(HashMap::new()),
            gc_threshold: 0.into(),
        })
    }

    /// Flushes all dirty IO buffers and calls fsync.
    /// If this succeeds, it is guaranteed that
    /// all previous writes will be recovered if
    /// the system crashes.
    pub fn flush(&self) -> Result<(), ()> {
        self.tree.flush()
    }

    /// Run a transaction, retrying if a concurrent transaction
    /// causes a `Conflict`.
    pub fn tx<'a, F, R>(&'a self, f: F) -> Result<tx::Result<R>, ()>
    where
        F: Fn(&mut Tx<'a>) -> tx::Result<R>,
    {
        loop {
            let guard = pin();

            let id = self.tree.generate_id()?;

            let mut tx = Tx {
                id,
                readset: BTreeSet::new(),
                writeset: BTreeSet::new(),
                db: &self,
                aborted: false,
            };

            let res = f(&mut tx);

            match tx.commit() {
                Ok(()) => return Ok(res),
                Err(tx::Error::Conflict) => {
                    // retry
                }
                Err(tx::Error::Aborted) => {
                    return Ok(Err(tx::Error::Aborted))
                }
            }
        }
    }

    /// Begin a new transaction.
    pub fn begin_tx(&self) -> Result<Tx<'_>, ()> {
        let id = self.tree.generate_id()?;

        Ok(Tx {
            id,
            readset: BTreeSet::new(),
            writeset: BTreeSet::new(),
            db: &self,
            aborted: false,
        })
    }

    fn bounded_get<K: AsRef<[u8]>>(
        &self,
        key: K,
        bound: usize,
    ) -> Result<Option<(usize, PinnedValue)>, ()> {
        let gc_threshold =
            self.gc_threshold.load(Ordering::Acquire) as usize;

        let versioned_key = version_key(&key, bound);

        let mut ret = None;

        for result in self.tree.range(key.as_ref()..&*versioned_key) {
            let (k, value) = result?;
            assert!(k.starts_with(key.as_ref()));
            if k.len() != versioned_key.len() {
                continue;
            }
            let version = version_of_key(&key);
            if version <= bound {
                if let Some((old_version, old_k, _)) = ret.take() {
                    // clean up old versions
                    if old_version <= gc_threshold {
                        self.tree.del(old_k)?;
                    }
                }
                ret = Some((version, k, value));
            } else {
                break;
            }
        }
        Ok(ret.map(|r| (r.0, r.2)))
    }
}

fn bump_gte(a: &AtomicUsize, to: usize) {
    let mut current = a.load(Ordering::Acquire);
    while current < to as usize {
        let last = a.compare_and_swap(
            current,
            to as usize,
            Ordering::SeqCst,
        );
        if last == current {
            // we succeeded.
            return;
        }
        current = last;
    }
}

fn version_key<K: AsRef<[u8]>>(key: K, version: usize) -> Vec<u8> {
    let target_len = key.as_ref().len() + VERSION_BYTES;
    let mut ret = Vec::with_capacity(target_len);
    unsafe {
        ret.set_len(target_len);
    }

    let version_buf: [u8; VERSION_BYTES] =
        unsafe { std::mem::transmute(version) };
    ret[0..key.as_ref().len()].copy_from_slice(key.as_ref());
    ret[key.as_ref().len()..target_len].copy_from_slice(&version_buf);
    ret
}

fn version_of_key<K: AsRef<[u8]>>(key: K) -> usize {
    let k = key.as_ref();
    assert!(k.len() >= VERSION_BYTES);
    let mut version_buf = [0u8; VERSION_BYTES];
    version_buf.copy_from_slice(&k[k.len() - VERSION_BYTES..]);

    unsafe { std::mem::transmute(version_buf) }
}

#[test]
fn basic_tx_functionality() -> Result<(), ()> {
    let config = ConfigBuilder::new().temporary(true).build();
    let db = Db::start(config)?;

    let mut tx1 = db.begin_tx()?;
    tx1.set(b"a", vec![1])?;
    tx1.commit().unwrap();

    let mut tx2 = db.begin_tx()?;
    let read = tx2.get(b"a").unwrap().unwrap();
    tx2.commit().unwrap();

    assert_eq!(*read, *vec![1u8]);

    Ok(())
}

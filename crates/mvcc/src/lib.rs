extern crate pagecache;
extern crate sled;

use std::sync::atomic::{AtomicUsize, Ordering};

use sled::Tree;

pub use sled::{Config, ConfigBuilder, PinnedValue, Result};

const VERSION_BYTES: usize = std::mem::size_of::<u64>();

pub struct Mvcc {
    tree: Tree,
    gc_threshold: AtomicUsize,
}

impl Mvcc {
    pub fn bounded_get<K: AsRef<[u8]>>(
        &self,
        key: K,
        bound: u64,
    ) -> Result<Option<(u64, PinnedValue)>, ()> {
        let gc_threshold =
            self.gc_threshold.load(Ordering::Acquire) as u64;

        let versioned_key = version_key(&key, bound);

        let mut ret = None;

        for result in self.tree.scan(&versioned_key) {
            let (k, value) = result?;
            if k.len() != versioned_key.len()
                || !k.starts_with(key.as_ref())
            {
                break;
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

fn bump_gte(a: &AtomicUsize, to: u64) {
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

fn version_key<K: AsRef<[u8]>>(key: K, version: u64) -> Vec<u8> {
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

fn version_of_key<K: AsRef<[u8]>>(key: K) -> u64 {
    let k = key.as_ref();
    assert!(k.len() >= VERSION_BYTES);
    let mut version_buf = [0u8; VERSION_BYTES];
    version_buf.copy_from_slice(&k[k.len() - VERSION_BYTES..]);

    unsafe { std::mem::transmute(version_buf) }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}

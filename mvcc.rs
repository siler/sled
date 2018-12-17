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

// TODO

    /// Clears the `Db`, removing all values.
    ///
    /// Note that this is not atomic.
    pub fn clear(&mut self) -> Result<(), ()> {
        for k in self.keys(b"") {
            let key = k?;
            // TODO
            // self.del(key)?;
        }
        Ok(())
    }

    /// Returns `true` if the `Db` contains a value for
    /// the specified key.
    pub fn contains_key<K: AsRef<[u8]>>(
        &mut self,
        key: K,
    ) -> Result<bool, ()> {
        self.get(key).map(|r| r.is_some())
    }

    /// Retrieve the key and value before the provided key,
    /// if one exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use sled::{ConfigBuilder, Error};
    /// let config = ConfigBuilder::new().temporary(true).build();
    ///
    /// let tree = sled::Db::start(config).unwrap();
    ///
    /// for i in 0..10 {
    ///     tree.set(vec![i], vec![i]).expect("should write successfully");
    /// }
    ///
    /// assert!(tree.get_lt(vec![]).unwrap().is_none());
    /// assert!(tree.get_lt(vec![0]).unwrap().is_none());
    /// assert!(tree.get_lt(vec![1]).unwrap().unwrap().1 == vec![0]);
    /// assert!(tree.get_lt(vec![9]).unwrap().unwrap().1 == vec![8]);
    /// assert!(tree.get_lt(vec![10]).unwrap().unwrap().1 == vec![9]);
    /// assert!(tree.get_lt(vec![255]).unwrap().unwrap().1 == vec![9]);
    /// ```
    pub fn get_lt<K: AsRef<[u8]>>(
        &mut self,
        key: K,
    ) -> Result<Option<(Key, PinnedValue)>, ()> {
        unimplemented!()
    }

    /// Retrieve the next key and value from the `Db` after the
    /// provided key.
    ///
    /// # Examples
    ///
    /// ```
    /// use sled::{ConfigBuilder, Error};
    /// let config = ConfigBuilder::new().temporary(true).build();
    ///
    /// let tree = sled::Db::start(config).unwrap();
    ///
    /// for i in 0..10 {
    ///     tree.set(vec![i], vec![i]).expect("should write successfully");
    /// }
    ///
    /// assert!(tree.get_gt(vec![]).unwrap().unwrap().1 == vec![0]);
    /// assert!(tree.get_gt(vec![0]).unwrap().unwrap().1 == vec![1]);
    /// assert!(tree.get_gt(vec![1]).unwrap().unwrap().1 == vec![2]);
    /// assert!(tree.get_gt(vec![8]).unwrap().unwrap().1 == vec![9]);
    /// assert!(tree.get_gt(vec![9]).unwrap().is_none());
    /// ```
    pub fn get_gt<K: AsRef<[u8]>>(
        &mut self,
        key: K,
    ) -> Result<Option<(Key, PinnedValue)>, ()> {
        unimplemented!()
    }

    /// Compare and swap. Capable of unique creation, conditional modification,
    /// or deletion. If old is None, this will only set the value if it doesn't
    /// exist yet. If new is None, will delete the value if old is correct.
    /// If both old and new are Some, will modify the value if old is correct.
    /// If Db is read-only, will do nothing.
    ///
    /// # Examples
    ///
    /// ```
    /// use sled::{ConfigBuilder, Error};
    /// let config = ConfigBuilder::new().temporary(true).build();
    /// let t = sled::Db::start(config).unwrap();
    ///
    /// // unique creation
    /// assert_eq!(t.cas(&[1], None, Some(vec![1])), Ok(()));
    /// // assert_eq!(t.cas(&[1], None, Some(vec![1])), Err(Error::CasFailed(Some(vec![1]))));
    ///
    /// // conditional modification
    /// assert_eq!(t.cas(&[1], Some(&*vec![1]), Some(vec![2])), Ok(()));
    /// // assert_eq!(t.cas(&[1], Some(vec![1]), Some(vec![2])), Err(Error::CasFailed(Some(vec![2]))));
    ///
    /// // conditional deletion
    /// assert_eq!(t.cas(&[1], Some(&[2]), None), Ok(()));
    /// assert_eq!(t.get(&[1]), Ok(None));
    /// ```
    pub fn cas<K: AsRef<[u8]>>(
        &mut self,
        key: K,
        old: Option<&[u8]>,
        new: Option<Value>,
    ) -> Result<(), Option<PinnedValue>> {
        unimplemented!()
    }

    /// Delete a value, returning the last result if it existed.
    ///
    /// # Examples
    ///
    /// ```
    /// let config = sled::ConfigBuilder::new().temporary(true).build();
    /// let t = sled::Db::start(config).unwrap();
    /// t.set(&[1], vec![1]);
    /// assert_eq!(t.del(&*vec![1]).unwrap().unwrap(), vec![1]);
    /// assert_eq!(t.del(&*vec![1]), Ok(None));
    /// ```
    pub fn del<K: AsRef<[u8]>>(
        &mut self,
        key: K,
    ) -> Result<Option<PinnedValue>, ()> {
        unimplemented!()
    }

    /// Merge state directly into a given key's value using the
    /// configured merge operator. This allows state to be written
    /// into a value directly, without any read-modify-write steps.
    /// Merge operators can be used to implement arbitrary data
    /// structures.
    ///
    /// # Panics
    ///
    /// Calling `merge` will panic if no merge operator has been
    /// configured.
    ///
    /// # Examples
    ///
    /// ```
    /// fn concatenate_merge(
    ///   _key: &[u8],               // the key being merged
    ///   old_value: Option<&[u8]>,  // the previous value, if one existed
    ///   merged_bytes: &[u8]        // the new bytes being merged in
    /// ) -> Option<Vec<u8>> {       // set the new value, return None to delete
    ///   let mut ret = old_value
    ///     .map(|ov| ov.to_vec())
    ///     .unwrap_or_else(|| vec![]);
    ///
    ///   ret.extend_from_slice(merged_bytes);
    ///
    ///   Some(ret)
    /// }
    ///
    /// let config = sled::ConfigBuilder::new()
    ///   .temporary(true)
    ///   .merge_operator(concatenate_merge)
    ///   .build();
    ///
    /// let tree = sled::Db::start(config).unwrap();
    ///
    /// let k = b"k1";
    ///
    /// tree.set(k, vec![0]);
    /// tree.merge(k, vec![1]);
    /// tree.merge(k, vec![2]);
    /// // assert_eq!(tree.get(k).unwrap().unwrap(), vec![0, 1, 2]);
    ///
    /// // sets replace previously merged data,
    /// // bypassing the merge function.
    /// tree.set(k, vec![3]);
    /// // assert_eq!(tree.get(k), Ok(Some(vec![3])));
    ///
    /// // merges on non-present values will add them
    /// tree.del(k);
    /// tree.merge(k, vec![4]);
    /// // assert_eq!(tree.get(k).unwrap().unwrap(), vec![4]);
    /// ```
    pub fn merge<K: AsRef<[u8]>>(
        &mut self,
        key: K,
        value: Value,
    ) -> Result<(), ()> {
        unimplemented!()
    }

    /// Iterate over the tuples of keys and values in this tree.
    ///
    /// # Examples
    ///
    /// ```
    /// let config = sled::ConfigBuilder::new().temporary(true).build();
    /// let t = sled::Db::start(config).unwrap();
    /// t.set(&[1], vec![10]);
    /// t.set(&[2], vec![20]);
    /// t.set(&[3], vec![30]);
    /// let mut iter = t.iter();
    /// // assert_eq!(iter.next(), Some(Ok((vec![1], vec![10]))));
    /// // assert_eq!(iter.next(), Some(Ok((vec![2], vec![20]))));
    /// // assert_eq!(iter.next(), Some(Ok((vec![3], vec![30]))));
    /// // assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&mut self) -> Iter<'_> {
        self.scan(b"")
    }

    /// Iterate over tuples of keys and values, starting at the provided key.
    ///
    /// # Examples
    ///
    /// ```
    /// let config = sled::ConfigBuilder::new().temporary(true).build();
    /// let t = sled::Db::start(config).unwrap();
    /// t.set(&[1], vec![10]);
    /// t.set(&[2], vec![20]);
    /// t.set(&[3], vec![30]);
    /// let mut iter = t.scan(&*vec![2]);
    /// // assert_eq!(iter.next(), Some(Ok((vec![2], vec![20]))));
    /// // assert_eq!(iter.next(), Some(Ok((vec![3], vec![30]))));
    /// // assert_eq!(iter.next(), None);
    /// ```
    pub fn scan<K: AsRef<[u8]>>(&mut self, key: K) -> Iter<'_> {
        unimplemented!()
    }

    /// Iterate over keys, starting at the provided key.
    ///
    /// # Examples
    ///
    /// ```
    /// let config = sled::ConfigBuilder::new().temporary(true).build();
    /// let t = sled::Db::start(config).unwrap();
    /// t.set(&[1], vec![10]);
    /// t.set(&[2], vec![20]);
    /// t.set(&[3], vec![30]);
    /// let mut iter = t.scan(&*vec![2]);
    /// // assert_eq!(iter.next(), Some(Ok(vec![2])));
    /// // assert_eq!(iter.next(), Some(Ok(vec![3])));
    /// // assert_eq!(iter.next(), None);
    /// ```
    pub fn keys<K: AsRef<[u8]>>(&mut self, key: K) -> Keys<'_> {
        self.scan(key).keys()
    }

    /// Iterate over values, starting at the provided key.
    ///
    /// # Examples
    ///
    /// ```
    /// let config = sled::ConfigBuilder::new().temporary(true).build();
    /// let t = sled::Db::start(config).unwrap();
    /// t.set(&[1], vec![10]);
    /// t.set(&[2], vec![20]);
    /// t.set(&[3], vec![30]);
    /// let mut iter = t.scan(&*vec![2]);
    /// // assert_eq!(iter.next(), Some(Ok(vec![20])));
    /// // assert_eq!(iter.next(), Some(Ok(vec![30])));
    /// // assert_eq!(iter.next(), None);
    /// ```
    pub fn values<K: AsRef<[u8]>>(&mut self, key: K) -> Values<'_> {
        self.scan(key).values()
    }

    /// Returns the number of elements in this tree.
    ///
    /// Beware: performs a full O(n) scan under the hood.
    pub fn len(&mut self) -> usize {
        self.iter().count()
    }

    /// Returns `true` if the `Db` contains no elements.
    pub fn is_empty(&mut self) -> bool {
        self.iter().next().is_none()
    }

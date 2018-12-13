#![allow(unused)]

use std::collections::HashMap;

use super::*;

pub mod tx {
    pub struct Aborted;

    pub type Result<T> = std::result::Result<T, Aborted>;
}

enum Update {
    Set,
    Merge,
    Del,
}

pub struct Tx<'a> {
    id: usize,
    tree: &'a Tree,
    cache: HashMap<Vec<u8>, ()>,
    aborted: bool,
}

impl<'a> Tx<'a> {
    fn commit(self) -> Result<bool, ()> {
        Ok(self.aborted)
    }

    pub fn abort(&mut self) {
        self.aborted = true;
    }

    /// Clears the `Db`, removing all values.
    ///
    /// Note that this is not atomic.
    pub fn clear(&mut self) -> Result<(), ()> {
        for k in self.keys(b"") {
            let key = k?;
            self.del(key)?;
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

    /// Retrieve a value from the `Db` if it exists.
    pub fn get<K: AsRef<[u8]>>(
        &mut self,
        key: K,
    ) -> Result<Option<PinnedValue>, ()> {
        unimplemented!()
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

    /// Set a key to a new value, returning the old value if it
    /// was set.
    pub fn set<K: AsRef<[u8]>>(
        &mut self,
        key: K,
        value: Value,
    ) -> Result<Option<PinnedValue>, ()> {
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
}

pub struct Db {
    tree: Tree,
}

impl Db {
    /// Load existing or create a new `Db` with a default configuration.
    pub fn start_default<P: AsRef<std::path::Path>>(
        path: P,
    ) -> Result<Db, ()> {
        let tree = Tree::start_default(path)?;

        Ok(Db { tree })
    }

    /// Load existing or create a new `Db`.
    pub fn start(config: Config) -> Result<Db, ()> {
        let tree = Tree::start(config)?;

        Ok(Db { tree })
    }

    /// Flushes all dirty IO buffers and calls fsync.
    /// If this succeeds, it is guaranteed that
    /// all previous writes will be recovered if
    /// the system crashes.
    pub fn flush(&self) -> Result<(), ()> {
        self.tree.flush()
    }

    pub fn tx<'a, F, R>(&'a self, f: F) -> Result<R, ()>
    where
        F: FnMut(&mut Tx<'a>) -> R,
    {
        loop {
            let guard = pin();

            let id = self.tree.generate_id()?;

            let tx = Tx {
                id,
                cache: HashMap::new(),
                tree: &self.tree,
                aborted: false,
            };

            let res = f(&mut tx);

            if tx.commit()? {
                return Ok(res);
            }
        }
    }
}

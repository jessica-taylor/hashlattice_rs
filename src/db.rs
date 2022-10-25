use std::sync::Arc;

use async_trait::async_trait;

use crate::crypto::{HashCode, hash_of_bytes};
use crate::tagged_mapping::TaggedMapping;
use crate::lattice::{LatticeLibrary, ComputationLibrary, ImmutComputationContext, MutComputationContext};

pub trait DBMapping<K, V> : Send + Sync {

    fn get(&self, key: &K) -> Option<V>;

    fn put(&mut self, key: K, value: Option<V>);
}

pub struct HashStore {
    db: Box<dyn DBMapping<HashCode, Vec<u8>>>,
}

impl HashStore {
    pub fn new(db: impl DBMapping<HashCode, Vec<u8>> + 'static) -> HashStore {
        HashStore { db: Box::new(db) }
    }
    pub fn hash_lookup(&self, hash: HashCode) -> Result<Vec<u8>, String> {
        match self.db.get(&hash) {
            Some(value) => Ok(value),
            None => Err(format!("Hash not found: {:?}", hash)),
        }
    }
    pub fn hash_put(&mut self, value: Vec<u8>) -> Result<HashCode, String> {
        let hash = hash_of_bytes(&value);
        self.db.put(hash, Some(value));
        Ok(hash)
    }
}

pub struct ComputationStore<CI: TaggedMapping, CM: TaggedMapping> {
    lib: Arc<dyn ComputationLibrary<CI, CM>>,
    hash_store: HashStore,
    immut_db: Box<dyn DBMapping<CI::Key, CI::Value>>,
    mut_db: Box<dyn DBMapping<CM::Key, CM::Value>>,
}

impl<CI: TaggedMapping, CM: TaggedMapping> ComputationStore<CI, CM> {
    pub fn new(lib: impl ComputationLibrary<CI, CM> + 'static,
               hash_store: HashStore,
               immut_db: impl DBMapping<CI::Key, CI::Value> + 'static,
               mut_db: impl DBMapping<CM::Key, CM::Value> + 'static) -> ComputationStore<CI, CM> {
        ComputationStore {
            lib: Arc::new(lib),
            hash_store,
            immut_db: Box::new(immut_db),
            mut_db: Box::new(mut_db)
        }
    }
}

impl<CI: TaggedMapping, CM: TaggedMapping> ImmutComputationContext<CI> for ComputationStore<CI, CM> {
    fn hash_lookup(&self, hash: HashCode) -> Result<Vec<u8>, String> {
        self.hash_store.hash_lookup(hash)
    }

    fn eval_immut(&mut self, key: &CI::Key) -> Result<CI::Value, String> {
        if let Some(value) = self.immut_db.get(key) {
            return Ok(value);
        }
        let res = self.lib.clone().eval_immut(key, self)?;
        self.immut_db.put(key.clone(), Some(res.clone()));
        Ok(res)
    }
}

impl<CI: TaggedMapping, CM: TaggedMapping> MutComputationContext<CI, CM> for ComputationStore<CI, CM> {

    fn hash_put(&mut self, value: Vec<u8>) -> Result<HashCode, String> {
        self.hash_store.hash_put(value)
    }

    fn eval_mut(&mut self, key: &CM::Key) -> Result<CM::Value, String> {
        if let Some(value) = self.mut_db.get(key) {
            return Ok(value);
        }
        let res = self.lib.clone().eval_mut(key, self)?;
        self.mut_db.put(key.clone(), Some(res.clone()));
        Ok(res)
    }
}

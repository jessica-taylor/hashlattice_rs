use crate::crypto::{HashCode, hash_of_bytes};
use crate::tagged_mapping::TaggedMapping;
use crate::lattice::{LatticeLibrary, ComputationLibrary, ComputationContext};

pub trait DBMapping<K, V> {

    fn get(&self, key: &K) -> Option<V>;

    fn put(&mut self, value: Option<V>);
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
        self.db.put(Some(value));
        Ok(hash)
    }
}

pub struct ComputationStore<CI: TaggedMapping, CM: TaggedMapping> {
    lib: Box<dyn ComputationLibrary<CI, CM>>,
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
            lib: Box::new(lib),
            hash_store,
            immut_db: Box::new(immut_db),
            mut_db: Box::new(mut_db)
        }
    }
}

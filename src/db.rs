use std::sync::Arc;

use async_trait::async_trait;

use crate::crypto::{HashCode, hash_of_bytes};
use crate::tagged_mapping::TaggedMapping;
use crate::lattice::{LatticeLibrary, ComputationLibrary, ImmutComputationContext, MutComputationContext, LatticeContext};
use serde::{Serialize, Deserialize, de::DeserializeOwned};

pub trait LatDB<CI: TaggedMapping, L: TaggedMapping> : Send + Sync {

    fn get_hash(&self, key: HashCode) -> Result<Option<Vec<u8>>, String>;
    fn put_hash(&mut self, key: HashCode, value: HashCode) -> Result<(), String>;
    fn remove_hash(&mut self, key: HashCode) -> Result<(), String>;

    fn get_immut(&self, key: &CI::Key) -> Result<Option<CI::Value>, String>;
    fn put_immut(&mut self, key: CI::Key, value: CI::Value) -> Result<(), String>;
    fn remove_immut(&mut self, key: &CI::Key) -> Result<(), String>;

    fn get_immut_hash_deps(&self, key: &CI::Key) -> Result<Vec<HashCode>, String>;
    fn put_immut_hash_deps(&mut self, key: CI::Key, deps: HashCode) -> Result<(), String>;
    fn remove_immut_hash_dep(&mut self, key: &CI::Key) -> Result<(), String>;

    fn depless_hashes(&self) -> Result<Vec<HashCode>, String>;

    fn get_immut_immut_deps(&self, key: &CI::Key) -> Result<Vec<CI::Key>, String>;
    fn put_immut_immut_dep(&mut self, key: CI::Key, dep: CI::Key) -> Result<(), String>;
    fn remove_immut_immut_dep(&mut self, key: &CI::Key, dep: &CI::Key) -> Result<(), String>;

    fn depless_immuts(&self) -> Result<Vec<CI::Key>, String>;

    fn get_lat(&self, key: &L::Key) -> Result<Option<L::Value>, String>;
    fn put_lat(&mut self, key: L::Key, value: L::Value) -> Result<(), String>;
    fn remove_lat(&mut self, key: &L::Key) -> Result<(), String>;

    fn get_lat_immut_deps(&self, key: &L::Key) -> Result<Vec<CI::Key>, String>;
    fn put_lat_immut_dep(&mut self, key: L::Key, dep: CI::Key) -> Result<(), String>;
    fn remove_lat_immut_dep(&mut self, key: &L::Key, dep: &CI::Key) -> Result<(), String>;
}

pub struct LatStore<CI: TaggedMapping, L: TaggedMapping> {
    db: Box<dyn LatDB<CI, L>>,
    comp_lib: Arc<dyn ComputationLibrary<CI>>,
    lat_lib: Arc<dyn LatticeLibrary<L>>,
}

impl<CI: TaggedMapping, L: TaggedMapping> LatStore<CI, L> {
    pub fn new(db: impl LatDB<CI, L> + 'static,
               comp_lib: impl ComputationLibrary<CI> + 'static,
               lat_lib: impl LatticeLibrary<L> + 'static) -> Self {
        Self { db: Box::new(db), comp_lib: Arc::new(comp_lib), lat_lib: Arc::new(lat_lib) }
    }
}

impl<CI: TaggedMapping, L: TaggedMapping> ImmutComputationContext<CI> for LatStore<CI, L> {
    fn hash_lookup(&mut self, hash: HashCode) -> Result<Vec<u8>, String> {
        self.db.get_hash(hash)?.ok_or_else(|| format!("Hash not found: {:?}", hash))
    }

    fn eval_immut(&mut self, key: &CI::Key) -> Result<CI::Value, String> {
        if let Some(value) = self.db.get_immut(key) {
            return Ok(value);
        }
        let res = self.lib.clone().eval_immut(key, self)?;
        self.db.put_immut(key.clone(), Some(res.clone()));
        Ok(res)
    }
}


pub struct HashStore {
    db: Box<dyn TypedDB<HashCode, Vec<u8>>>,
}

impl HashStore {
    pub fn new(db_fac: &mut impl DBFactory) -> HashStore {
        HashStore { db: Box::new(TypedDB::new(db_fac.new_db("hash_store"))) }
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

pub struct ComputationDeps<CI: TaggedMapping> {
    hashes: Vec<HashCode>,
    immuts: Vec<CI::Key>,
}

pub struct ComputationStore<CI: TaggedMapping, CM: TaggedMapping> {
    lib: Arc<dyn ComputationLibrary<CI, CM>>,
    hash_store: HashStore,
    immut_db: TypedDB<CI::Key, CI::Value>,
    immut_deps: TypedDB<CI::Key, ComputationDeps<CI>>,
    curr_key: Option<CI::Key>,
}

impl<CI: TaggedMapping, CM: TaggedMapping> ComputationStore<CI, CM> {
    pub fn new(lib: impl ComputationLibrary<CI, CM> + 'static,
               db_fac: &mut impl DBFactory) -> ComputationStore<CI, CM> {
        ComputationStore {
            lib: Arc::new(lib),
            hash_store: HashStore::new(db_fac),
            immut_db: Box::new(TypedDB::new(db_fac.new_db("immut_store"))),
            immut_deps: Box::new(TypedDB::new(db_fac.new_db("immut_deps"))),
        }
    }
}

impl<CI: TaggedMapping, CM: TaggedMapping> ImmutComputationContext<CI> for ComputationStore<CI, CM> {
    fn hash_lookup(&mut self, hash: HashCode) -> Result<Vec<u8>, String> {
        if let Some(ck) = self.curr_key {
        }
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
        self.lib.clone().eval_mut(key, self);
    }
}

pub struct LatticeStore<CI: TaggedMapping, CM: TaggedMapping, L: TaggedMapping> {
    lib: Arc<dyn LatticeLibrary<CI, CM, L>>,
    comp_store: ComputationStore<CI, CM>,
    db: TypedDB<L::Key, L::Value>,
}

impl<CI: TaggedMapping, CM: TaggedMapping, L: TaggedMapping> LatticeStore<CI, CM, L> {
    pub fn new(lib: impl LatticeLibrary<CI, CM, L> + 'static,
               db_fac: &mut impl DBFactory) -> LatticeStore<CI, CM, L> {
        LatticeStore {
            lib: Arc::new(lib),
            comp_store: ComputationStore::new(db_fac),
            db: Box::new(TypedDB::new(db_fac.new_db("lattice_store"))),
        }
    }

    pub fn get_lat_max(&self, key: &L::Key) -> Option<L::Value> {
        self.db.get(key)
    }

    pub fn join_lat(&mut self, key: L::Key, value: L::Value) -> Result<L::Value, String> {
        self.lib.clone().check_elem(&key, &value, &mut self.comp_store)?;
        match self.get_lat_max(&key) {
            None => {
                self.db.put(key, value.clone());
                Ok(value)
            },
            Some(max) => {
                let new_max = self.lib.clone().join(&key, &max, &value, &mut self.comp_store)?;
                self.db.put(key, Some(new_max.clone()));
                Ok(new_max)
            }
        }
    }
}

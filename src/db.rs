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

    fn get_lat_hash_deps(&self, key: &L::Key) -> Result<Vec<HashCode>, String>;
    fn put_lat_hash_dep(&mut self, key: L::Key, dep: HashCode) -> Result<(), String>;
    fn remove_lat_Hash_dep(&mut self, key: &L::Key, dep: HashCode) -> Result<(), String>;

    fn get_lat_immut_deps(&self, key: &L::Key) -> Result<Vec<CI::Key>, String>;
    fn put_lat_immut_dep(&mut self, key: L::Key, dep: CI::Key) -> Result<(), String>;
    fn remove_lat_immut_dep(&mut self, key: &L::Key, dep: &CI::Key) -> Result<(), String>;
}

pub struct LatStore<CI: TaggedMapping, L: TaggedMapping> {
    db: Box<dyn LatDB<CI, L>>,
    comp_lib: Arc<dyn ComputationLibrary<CI>>,
    lat_lib: Arc<dyn LatticeLibrary<CI, L>>,
}

impl<CI: TaggedMapping, L: TaggedMapping> LatStore<CI, L> {
    pub fn new(db: impl LatDB<CI, L> + 'static,
               comp_lib: impl ComputationLibrary<CI> + 'static,
               lat_lib: impl LatticeLibrary<CI, L> + 'static) -> Self {
        Self { db: Box::new(db), comp_lib: Arc::new(comp_lib), lat_lib: Arc::new(lat_lib) }
    }
}

impl<CI: TaggedMapping, L: TaggedMapping> ImmutComputationContext<CI> for LatStore<CI, L> {
    fn hash_lookup(&mut self, hash: HashCode) -> Result<Vec<u8>, String> {
        self.db.get_hash(hash)?.ok_or_else(|| format!("Hash not found: {:?}", hash))
    }

    fn eval_immut(&mut self, key: &CI::Key) -> Result<CI::Value, String> {
        if let Some(value) = self.db.get_immut(key)? {
            return Ok(value);
        }
        let res = self.comp_lib.clone().eval_immut(key, self)?;
        self.db.put_immut(key.clone(), res.clone());
        Ok(res)
    }
}

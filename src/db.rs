use std::sync::Arc;

use core::fmt::{Debug, Formatter};

use async_trait::async_trait;

use crate::crypto::{HashCode, hash_of_bytes};
use crate::tagged_mapping::TaggedMapping;
use crate::lattice::{LatticeLibrary, ComputationLibrary, ImmutComputationContext, MutComputationContext, LatticeContext};
use serde::{Serialize, Deserialize, de::DeserializeOwned};

pub trait DepDB<M: TaggedMapping>: Send + Sync {

    fn get_value(&self, key: &M::Key) -> Result<Option<M::Value>, String>;

    fn set_value_deps(&self, key: M::Key, value: M::Value, deps: Vec<M::Key>) -> Result<(), String>;

    fn clear_value_deps(&self, key: &M::Key) -> Result<(), String>;
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub enum LatDBKey<IK, LK> {
    Hash(HashCode),
    Immut(IK),
    Lattice(LK),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub enum LatDBValue<IV, LV> {
    Hash(Vec<u8>),
    Immut(IV),
    Lattice(LV),
}

pub struct LatDBMapping<CI: TaggedMapping, L: TaggedMapping> {
    immut: CI,
    lat: L
}

impl<CI: TaggedMapping, L: TaggedMapping> TaggedMapping for LatDBMapping<CI, L> {
    type Key = LatDBKey<CI::Key, L::Key>;
    type Value = LatDBValue<CI::Value, L::Value>;
}

pub struct LatStore<CI: TaggedMapping, L: TaggedMapping> {
    db: Box<dyn DepDB<LatDBMapping<CI, L>>>,
    comp_lib: Arc<dyn ComputationLibrary<CI>>,
    lat_lib: Arc<dyn LatticeLibrary<CI, L>>,
    deps_stack: Vec<Vec<LatDBKey<CI::Key, L::Key>>>,
}

impl<CI: TaggedMapping, L: TaggedMapping> LatStore<CI, L> {
    pub fn new(db: impl DepDB<LatDBMapping<CI, L>> + 'static,
               comp_lib: impl ComputationLibrary<CI> + 'static,
               lat_lib: impl LatticeLibrary<CI, L> + 'static) -> Self {
        Self {
            db: Box::new(db),
            comp_lib: Arc::new(comp_lib),
            lat_lib: Arc::new(lat_lib),
            deps_stack: Vec::new(),
        }
    }
}

impl<CI: TaggedMapping, L: TaggedMapping> ImmutComputationContext<CI> for LatStore<CI, L> {
    fn hash_lookup(&mut self, hash: HashCode) -> Result<Vec<u8>, String> {
        if let Some(deps) = self.deps_stack.last_mut() {
            deps.push(LatDBKey::Hash(hash));
        }
        match self.db.get_value(&LatDBKey::Hash(hash))? {
            Some(LatDBValue::Hash(bytes)) => Ok(bytes),
            _ => Err(format!("Hash not found: {:?}", hash)),
        }
    }

    fn eval_immut(&mut self, key: &CI::Key) -> Result<CI::Value, String> {
        if let Some(deps) = self.deps_stack.last_mut() {
            deps.push(LatDBKey::Immut(key.clone()));
        }
        let immut_key = LatDBKey::Immut(key.clone());
        if let Some(LatDBValue::Immut(value)) = self.db.get_value(&immut_key)? {
            return Ok(value);
        }
        self.deps_stack.push(Vec::new());
        match self.comp_lib.clone().eval_immut(key, self) {
            Err(err) => {
                self.deps_stack.pop();
                Err(err)
            }
            Ok(value) => {
                let deps = self.deps_stack.pop().unwrap();
                self.db.set_value_deps(immut_key, LatDBValue::Immut(value.clone()), deps)?;
                Ok(value)
            }
        }
    }
}

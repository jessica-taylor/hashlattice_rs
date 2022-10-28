use std::sync::{Arc, Mutex, MutexGuard};


use core::fmt::{Debug, Formatter};

use async_trait::async_trait;

use crate::crypto::{HashCode, hash_of_bytes};
use crate::tagged_mapping::TaggedMapping;
use crate::lattice::{HashLookup, LatticeLibrary, ComputationLibrary, ImmutComputationContext, MutComputationContext, LatticeContext};
use serde::{Serialize, Deserialize, de::DeserializeOwned};

/// a key-value store with key-key dependencies; auto-removes unpinned, non-depended-on keys
pub trait DepDB<M: TaggedMapping> : Send {

    fn has_value(&self, key: &M::Key) -> Result<bool, String>;

    fn get_value(&self, key: &M::Key) -> Result<Option<M::Value>, String>;

    fn set_value_deps(&mut self, key: M::Key, value: M::Value, deps: Vec<M::Key>) -> Result<(), String>;

    fn is_pinned(&self, key: &M::Key) -> Result<bool, String>;

    fn set_pin(&mut self, key: &M::Key, pin: bool) -> Result<(), String>;

    fn clear_value_deps(&mut self, key: &M::Key) -> Result<(), String>;

    fn clear_unpinned(&mut self) -> Result<(), String>;
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
    db: Box<Mutex<dyn DepDB<LatDBMapping<CI, L>>>>,
    comp_lib: Arc<dyn ComputationLibrary<CI>>,
    lat_lib: Arc<dyn LatticeLibrary<CI, L>>,
    backup_hashlookup: Box<dyn HashLookup>,
    deps_stack: Vec<Vec<LatDBKey<CI::Key, L::Key>>>,
}

impl<CI: TaggedMapping, L: TaggedMapping> LatStore<CI, L> {
    pub fn new(db: impl DepDB<LatDBMapping<CI, L>> + 'static,
               comp_lib: impl ComputationLibrary<CI> + 'static,
               lat_lib: impl LatticeLibrary<CI, L> + 'static,
               backup_hashlookup: impl HashLookup + 'static) -> Self {
        Self {
            db: Box::new(Mutex::new(db)),
            comp_lib: Arc::new(comp_lib),
            lat_lib: Arc::new(lat_lib),
            backup_hashlookup: Box::new(backup_hashlookup),
            deps_stack: Vec::new(),
        }
    }

    fn get_db(&self) -> MutexGuard<dyn DepDB<LatDBMapping<CI, L>> + 'static> {
        self.db.lock().unwrap()
    }

    pub fn set_hash_pin(&mut self, hash: &HashCode, pin: bool) -> Result<(), String> {
        self.get_db().set_pin(&LatDBKey::Hash(hash.clone()), pin)
    }
    pub fn set_immut_pin(&mut self, key: &CI::Key, pin: bool) -> Result<(), String> {
        self.get_db().set_pin(&LatDBKey::Immut(key.clone()), pin)
    }
    pub fn set_lattice_pin(&mut self, key: &L::Key, pin: bool) -> Result<(), String> {
        self.get_db().set_pin(&LatDBKey::Lattice(key.clone()), pin)
    }
    pub fn clear_unpinned(&mut self) -> Result<(), String> {
        self.get_db().clear_unpinned()
    }
}

impl<CI: TaggedMapping, L: TaggedMapping> HashLookup for LatStore<CI, L> {
    fn hash_lookup(&mut self, hash: HashCode) -> Result<Vec<u8>, String> {
        if let Some(deps) = self.deps_stack.last_mut() {
            deps.push(LatDBKey::Hash(hash));
        }
        let res = self.get_db().get_value(&LatDBKey::Hash(hash))?;
        match res {
            Some(LatDBValue::Hash(bytes)) => Ok(bytes),
            _ => {
                let val = self.backup_hashlookup.hash_lookup(hash)?;
                if hash_of_bytes(&val) != hash {
                    return Err(format!("hash lookup returned wrong value for hash {:?}", hash));
                }
                self.hash_put(val.clone())?;
                Ok(val)
            }
        }
    }
}

impl<CI: TaggedMapping, L: TaggedMapping> ImmutComputationContext<CI> for LatStore<CI, L> {

    fn eval_immut(&mut self, key: &CI::Key) -> Result<CI::Value, String> {
        if let Some(deps) = self.deps_stack.last_mut() {
            deps.push(LatDBKey::Immut(key.clone()));
        }
        let immut_key = LatDBKey::Immut(key.clone());
        if let Some(LatDBValue::Immut(value)) = self.get_db().get_value(&immut_key)? {
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
                self.get_db().set_value_deps(immut_key, LatDBValue::Immut(value.clone()), deps)?;
                Ok(value)
            }
        }
    }
}

impl<CI: TaggedMapping, L: TaggedMapping> MutComputationContext<CI> for LatStore<CI, L> {
    fn hash_put(&mut self, value: Vec<u8>) -> Result<HashCode, String> {
        let hash = hash_of_bytes(&value);
        let key = LatDBKey::Hash(hash);
        if !self.get_db().has_value(&key)? {
            self.get_db().set_value_deps(key.clone(), LatDBValue::Hash(value), Vec::new())?;
        }
        Ok(hash)
    }
}

impl<CI: TaggedMapping, L: TaggedMapping> LatticeContext<CI, L> for LatStore<CI, L> {
    fn get_lattice(&self, key: &L::Key) -> Option<L::Value> {
        match self.get_db().get_value(&LatDBKey::Lattice(key.clone())) {
            Ok(Some(LatDBValue::Lattice(value))) => Some(value),
            _ => None,
        }
    }

    fn join_lattice(&mut self, key: &L::Key, value: L::Value) -> Result<L::Value, String> {
        let new_value = match self.get_lattice(key) {
            None => value,
            Some(old_value) => {
                let joined = self.lat_lib.clone().join(key, &old_value, &value, self)?;
                if joined == old_value {
                    return Ok(old_value);
                }
                joined
            }
        };
        self.deps_stack.push(Vec::new());
        match self.lat_lib.clone().check_elem(key, &new_value, self) {
            Err(err) => {
                self.deps_stack.pop();
                Err(err)
            }
            Ok(()) => {
                let deps = self.deps_stack.pop().unwrap();
                self.get_db().set_value_deps(LatDBKey::Lattice(key.clone()), LatDBValue::Lattice(new_value.clone()), deps)?;
                Ok(new_value)
            }
        }
    }
}

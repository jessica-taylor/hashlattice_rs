use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex, MutexGuard};

use core::fmt::{Debug};

use crate::error::{Res, str_error};
use crate::crypto::{HashCode, hash_of_bytes, Hash, hash};
use crate::tagged_mapping::TaggedMapping;
use crate::lattice::{HashLookup, LatticeLibrary, ComputationLibrary, ComputationImmutContext, ComputationMutContext, LatticeImmutContext, LatticeMutContext};
use serde::{Serialize, Deserialize, de::DeserializeOwned};

/// a key-value store with key-key dependencies; auto-removes unpinned, non-depended-on keys
pub trait DepDB<M: TaggedMapping> : Send {

    fn has_value(&self, key: &M::Key) -> Res<bool>;

    fn get_value(&self, key: &M::Key) -> Res<Option<M::Value>>;

    fn set_value_deps(&mut self, key: M::Key, value: M::Value, deps: Vec<M::Key>) -> Res<()>;

    fn is_pinned(&self, key: &M::Key) -> Res<bool>;

    fn set_pin(&mut self, key: &M::Key, pin: bool) -> Res<()>;

    fn clear_value_deps(&mut self, key: &M::Key) -> Res<()>;

    fn clear_dead(&mut self) -> Res<()>;

    fn get_dirty(&mut self) -> Res<Vec<M::Key>>;
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub struct LatMerkleNodeDeps<LK: Ord, LV, LCK: Ord, LCV> {
    pub lat_deps: BTreeMap<LK, Hash<LatMerkleNode<LK, LV, LCK, LCV, LV>>>,
    pub lat_comp_deps: BTreeMap<LCK, Hash<LatMerkleNode<LK, LV, LCK, LCV, LCV>>>,
}

impl<LK: Ord, LV, LCK: Ord, LCV> LatMerkleNodeDeps<LK, LV, LCK, LCV> {
    pub fn new() -> Self {
        LatMerkleNodeDeps {
            lat_deps: BTreeMap::new(),
            lat_comp_deps: BTreeMap::new(),
        }
    }
}

type LatMerkleNodeDepsM<L: TaggedMapping, LC: TaggedMapping> = LatMerkleNodeDeps<L::Key, L::Value, LC::Key, LC::Value>;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub struct LatMerkleNode<LK: Ord, LV, LCK: Ord, LCV, V> {
    pub value: V,
    pub deps: LatMerkleNodeDeps<LK, LV, LCK, LCV>,
}

type LatMerkleNodeM<L: TaggedMapping, LC: TaggedMapping> = LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>;
type LatComputationMerkleNodeM<L: TaggedMapping, LC: TaggedMapping> = LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, LC::Value>;


#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub enum LatDBKey<CK, LK, LCK> {
    Hash(HashCode),
    Computation(CK),
    Lattice(LK),
    LatComputation(LCK),
}

type LatDBKeyM<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> = LatDBKey<C::Key, L::Key, LC::Key>;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub enum LatDBValue<CV, LK: Ord, LV, LCK: Ord, LCV> {
    Hash(Vec<u8>),
    Computation(CV),
    Lattice(Hash<LatMerkleNode<LK, LV, LCK, LCV, LV>>),
    LatComputation(Hash<LatMerkleNode<LK, LV, LCK, LCV, LCV>>),
}

type LatDBValueM<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> = LatDBValue<C::Value, L::Key, L::Value, LC::Key, LC::Value>;

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub struct LatDeps<CK: Ord, LK: Ord, LV, LCK: Ord, LCV> {
    hash_deps: BTreeSet<HashCode>,
    comp_deps: BTreeSet<CK>,
    lat_deps: BTreeMap<LK, Hash<LatMerkleNode<LK, LV, LCK, LCV, LV>>>,
    lat_comp_deps: BTreeMap<LCK, Hash<LatMerkleNode<LK, LV, LCK, LCV, LCV>>>,
}

type LatDepsM<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> = LatDeps<C::Key, L::Key, L::Value, LC::Key, LC::Value>;

impl<CK: Ord, LK: Ord + Clone, LV, LCK: Ord + Clone, LCV> LatDeps<CK, LK, LV, LCK, LCV> {
    pub fn to_merkle_deps(&self) -> LatMerkleNodeDeps<LK, LV, LCK, LCV> {
        LatMerkleNodeDeps {
            lat_deps: self.lat_deps.clone(),
            lat_comp_deps: self.lat_comp_deps.clone(),
        }
    }
}

impl<CK: Ord + Clone, LK: Ord + Clone, LV, LCK: Ord + Clone, LCV> LatDeps<CK, LK, LV, LCK, LCV> {
    pub fn new() -> Self {
        LatDeps {
            hash_deps: BTreeSet::new(),
            comp_deps: BTreeSet::new(),
            lat_deps: BTreeMap::new(),
            lat_comp_deps: BTreeMap::new(),
        }
    }
    pub fn to_keys(&self) -> Vec<LatDBKey<CK, LK, LCK>> {
        let mut keys: Vec<LatDBKey<CK, LK, LCK>> = Vec::new();
        for hash in self.hash_deps.iter() {
            keys.push(LatDBKey::Hash(hash.clone()));
        }
        for comp in self.comp_deps.iter() {
            keys.push(LatDBKey::Computation(comp.clone()));
        }
        for (lat, _) in self.lat_deps.iter() {
            keys.push(LatDBKey::Lattice(lat.clone()));
        }
        for (lat_comp, _) in self.lat_comp_deps.iter() {
            keys.push(LatDBKey::LatComputation(lat_comp.clone()));
        }
        keys
    }
}

pub struct LatDBMapping<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> {
    computation: C,
    lat: L,
    lat_comp: LC,
}

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> TaggedMapping for LatDBMapping<C, L, LC> {
    type Key = LatDBKeyM<C, L, LC>;
    type Value = LatDBValueM<C, L, LC>;
}

pub struct LatStore<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> {
    db: Box<Mutex<dyn DepDB<LatDBMapping<C, L, LC>>>>,
    comp_lib: Arc<dyn ComputationLibrary<C>>,
    lat_lib: Arc<dyn LatticeLibrary<C, L, LC>>,
    deps_stack: Mutex<Vec<LatDepsM<C, L, LC>>>,
}

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> LatStore<C, L, LC> {
    pub fn new(db: impl DepDB<LatDBMapping<C, L, LC>> + 'static,
               comp_lib: impl ComputationLibrary<C> + 'static,
               lat_lib: impl LatticeLibrary<C, L, LC> + 'static) -> Self {
        Self {
            db: Box::new(Mutex::new(db)),
            comp_lib: Arc::new(comp_lib),
            lat_lib: Arc::new(lat_lib),
            deps_stack: Mutex::new(Vec::new()),
        }
    }

    fn get_db(&self) -> MutexGuard<dyn DepDB<LatDBMapping<C, L, LC>> + 'static> {
        self.db.lock().unwrap()
    }

    pub fn set_hash_pin(&mut self, hash: &HashCode, pin: bool) -> Res<()> {
        self.get_db().set_pin(&LatDBKey::Hash(hash.clone()), pin)
    }
    pub fn set_computation_pin(&mut self, key: &C::Key, pin: bool) -> Res<()> {
        self.get_db().set_pin(&LatDBKey::Computation(key.clone()), pin)
    }
    pub fn set_lattice_pin(&mut self, key: &L::Key, pin: bool) -> Res<()> {
        self.get_db().set_pin(&LatDBKey::Lattice(key.clone()), pin)
    }
    pub fn clear_dead(&mut self) -> Res<()> {
        self.get_db().clear_dead()
    }

    fn with_get_deps<T>(&self, f: impl FnOnce(&Self) -> Res<T>) -> Res<(T, LatDeps<C::Key, L::Key, L::Value, LC::Key, LC::Value>)> {
        self.deps_stack.lock().unwrap().push(LatDeps::new());
        let res = f(self);
        let deps = self.deps_stack.lock().unwrap().pop().unwrap();
        res.map(|x| (x, deps))
    }

    fn hash_lookup_generic<T: DeserializeOwned>(&self, hsh: Hash<T>) -> Res<T> {
        let bs = self.hash_lookup(hsh.code)?;
        Ok(rmp_serde::from_slice(&bs)?)
    }

    fn hash_put_generic<T: Serialize>(&self, value: &T) -> Res<Hash<T>> {
        let bs = rmp_serde::to_vec(&value)?;
        Ok(Hash::from_hashcode(self.hash_put(bs)?))
    }

    fn update_dirty(&self) -> Res<()> {
        loop {
            let dirty = self.get_db().get_dirty()?;
            if dirty.is_empty() {
                return Ok(());
            }
            for key in dirty {
                match &key {
                    LatDBKey::Lattice(lat_key) => {
                        let merkle_hash = match self.get_db().get_value(&key)? {
                            Some(LatDBValue::Lattice(merkle_hash)) => merkle_hash,
                            _ => return Err(format!("Lattice key {:?} has no merkle hash", lat_key).into()),
                        };
                        let merkle = self.hash_lookup_generic(merkle_hash)?;
                        let old_ctx = LatStoreImmutCtx {
                            store: self,
                            deps: merkle.deps
                        };
                        let tr_value = self.lat_lib.clone().transport(&lat_key, &merkle.value, &old_ctx, self)?;
                        let ((), tr_deps) = self.with_get_deps(|this| this.lat_lib.clone().check_elem(&lat_key, &tr_value, this))?;
                        let merkle_hash = self.hash_put_generic(&LatMerkleNode {
                            value: tr_value,
                            deps: tr_deps.to_merkle_deps(),
                        })?;
                        self.get_db().set_value_deps(key.clone(), LatDBValue::Lattice(merkle_hash), tr_deps.to_keys())?;
                    }
                    LatDBKey::LatComputation(lat_comp_key) => {
                        let (value, deps) = self.with_get_deps(|this| this.lat_lib.clone().eval_lat_computation(lat_comp_key, this))?;
                        let merkle_hash = self.hash_put_generic(&LatMerkleNode {
                            value,
                            deps: deps.to_merkle_deps(),
                        })?;
                        self.get_db().set_value_deps(key.clone(), LatDBValue::LatComputation(merkle_hash), deps.to_keys())?;
                    }
                    _ => {}
                }
            }
        }
    }
}

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> HashLookup for LatStore<C, L, LC> {

    fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>> {
        if let Some(deps) = self.deps_stack.lock().unwrap().last_mut() {
            deps.hash_deps.insert(hash);
        }
        let res = self.get_db().get_value(&LatDBKey::Hash(hash))?;
        match res {
            Some(LatDBValue::Hash(bytes)) => Ok(bytes),
            _ => Err(format!("Hash {:?} not found", hash).into()),
        }
    }
}

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> ComputationImmutContext<C> for LatStore<C, L, LC> {

    fn eval_computation(&self, key: &C::Key) -> Res<C::Value> {
        if let Some(deps) = self.deps_stack.lock().unwrap().last_mut() {
            deps.comp_deps.insert(key.clone());
        }
        let computation_key = LatDBKey::Computation(key.clone());
        if let Some(LatDBValue::Computation(value)) = self.get_db().get_value(&computation_key)? {
            return Ok(value);
        }
        let (value, deps) = self.with_get_deps(|this| this.comp_lib.clone().eval_computation(key, this))?;
        self.get_db().set_value_deps(computation_key, LatDBValue::Computation(value.clone()), deps.to_keys())?;
        Ok(value)
    }

}

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> ComputationMutContext<C> for LatStore<C, L, LC> {

    fn hash_put(&self, value: Vec<u8>) -> Res<HashCode> {
        let hash = hash_of_bytes(&value);
        let key = LatDBKey::Hash(hash);
        if !self.get_db().has_value(&key)? {
            self.get_db().set_value_deps(key.clone(), LatDBValue::Hash(value), Vec::new())?;
        }
        Ok(hash)
    }

}

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> LatticeImmutContext<C, L, LC> for LatStore<C, L, LC> {

    fn lattice_lookup<'a>(&'a self, key: &L::Key) -> Res<Option<(L::Value, Box<dyn 'a + LatticeImmutContext<C, L, LC>>)>> {
        match self.get_db().get_value(&LatDBKey::Lattice(key.clone()))? {
            Some(LatDBValue::Lattice(merkle_hash)) => {
                let merkle = self.hash_lookup_generic(merkle_hash)?;
                if let Some(deps) = self.deps_stack.lock().unwrap().last_mut() {
                    deps.lat_deps.insert(key.clone(), hash(&merkle));
                }
                Ok(Some((merkle.value, Box::new(LatStoreImmutCtx {
                    store: self,
                    deps: merkle.deps
                }))))
            }
            _ => { return Ok(None); }
        }
    }

    fn eval_lat_computation<'a>(&'a self, key: &LC::Key) -> Res<(LC::Value, Box<dyn 'a + LatticeImmutContext<C, L, LC>>)> {
        let merkle = match self.get_db().get_value(&LatDBKey::LatComputation(key.clone()))? {
            Some(LatDBValue::LatComputation(merkle_hash)) => self.hash_lookup_generic(merkle_hash)?,
            _ => {
                let (value, deps) = self.with_get_deps(|this| this.lat_lib.clone().eval_lat_computation(key, self))?;
                let merkle = LatMerkleNode {
                    value: value,
                    deps: deps.to_merkle_deps()
                };
                self.get_db().set_value_deps(LatDBKey::LatComputation(key.clone()), LatDBValue::LatComputation(self.hash_put_generic(&merkle)?), deps.to_keys())?;
                merkle
            }
        };
        if let Some(deps) = self.deps_stack.lock().unwrap().last_mut() {
            deps.lat_comp_deps.insert(key.clone(), hash(&merkle));
        }
        Ok((merkle.value, Box::new(LatStoreImmutCtx {
            store: self,
            deps: merkle.deps
        })))
    }
}

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> LatticeMutContext<C, L, LC> for LatStore<C, L, LC> {

    fn lattice_join(&self, key: &L::Key, value: &L::Value, ctx_other: &mut dyn LatticeImmutContext<C, L, LC>) -> Res<L::Value> {
        let value = self.lat_lib.clone().transport(key, value, ctx_other, self)?;
        let db_value = self.get_db().get_value(&LatDBKey::Lattice(key.clone()))?;
        let new_value = match db_value {
            None => value.clone(),
            Some(LatDBValue::Lattice(old_merkle_hash)) => {
                let old_merkle = self.hash_lookup_generic(old_merkle_hash)?;
                let ((), old_deps) = self.with_get_deps(|this| this.lat_lib.clone().check_elem(key, &old_merkle.value, this))?;
                // assume it's already been transported??
                let joined = self.lat_lib.clone().join(key, &old_merkle.value, &value, self)?;
                if joined == old_merkle.value {
                    return Ok(old_merkle.value);
                }
                joined
            }
            _ => return Err("lattice value is not a lattice".into())
        };
        let ((), deps) = self.with_get_deps(|this| this.lat_lib.clone().check_elem(key, &new_value, this))?;
        let merkle_hash = self.hash_put_generic(&LatMerkleNode {
            value: new_value.clone(),
            deps: deps.to_merkle_deps()
        })?;
        self.get_db().set_value_deps(LatDBKey::Lattice(key.clone()), LatDBValue::Lattice(merkle_hash), deps.to_keys())?;
        self.update_dirty();
        Ok(new_value)
    }
}

pub struct LatStoreImmutCtx<'a, C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> {
    store: &'a LatStore<C, L, LC>,
    deps: LatMerkleNodeDepsM<L, LC>,
}

impl<'a, C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> HashLookup for LatStoreImmutCtx<'a, C, L, LC> {
    fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>> {
        self.store.hash_lookup(hash)
    }
}

impl<'a, C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> ComputationImmutContext<C> for LatStoreImmutCtx<'a, C, L, LC> {

    fn eval_computation(&self, key: &C::Key) -> Res<C::Value> {
        self.store.eval_computation(key)
    }
}

impl<'a, C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> LatticeImmutContext<C, L, LC> for LatStoreImmutCtx<'a, C, L, LC> {
    fn lattice_lookup<'b>(&'b self, key: &L::Key) -> Res<Option<(L::Value, Box<dyn 'b + LatticeImmutContext<C, L, LC>>)>> {
        match self.deps.lat_deps.get(key) {
            None => Ok(None),
            Some(merkle_hash) => {
                let merkle = self.store.hash_lookup_generic(merkle_hash.clone())?;
                Ok(Some((merkle.value, Box::new(LatStoreImmutCtx {
                    store: self.store,
                    deps: merkle.deps,
                }))))
            }
        }
    }

    fn eval_lat_computation<'b>(&'b self, key: &LC::Key) -> Res<(LC::Value, Box<dyn 'b + LatticeImmutContext<C, L, LC>>)> {
        match self.deps.lat_comp_deps.get(key) {
            None => str_error("lattice computation dependency not found"),
            Some(merkle_hash) => {
                let merkle = self.store.hash_lookup_generic(merkle_hash.clone())?;
                Ok((merkle.value, Box::new(LatStoreImmutCtx {
                    store: self.store,
                    deps: merkle.deps,
                })))
            }
        }
    }
}

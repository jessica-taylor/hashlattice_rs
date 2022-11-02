use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex, MutexGuard};

use core::pin::Pin;
use core::fmt::{Debug};

use futures::Future;
use anyhow::bail;
use async_trait::async_trait;

use crate::error::Res;
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
    pub fn is_empty(&self) -> bool {
        self.lat_deps.is_empty() && self.lat_comp_deps.is_empty()
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

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatStore<C, L, LC> {
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

    async fn with_get_deps<'a, T, F: Future<Output = Res<T>>>(self: &Arc<Self>, f: impl FnOnce(Arc<Self>) -> F) -> Res<(T, LatDeps<C::Key, L::Key, L::Value, LC::Key, LC::Value>)> {
        self.deps_stack.lock().unwrap().push(LatDeps::new());
        let res = f(self.clone()).await;
        let deps = self.deps_stack.lock().unwrap().pop().unwrap();
        res.map(|x| (x, deps))
    }

    async fn hash_lookup_generic<T: DeserializeOwned>(self: &Arc<Self>, hsh: Hash<T>) -> Res<T> {
        let bs = self.clone().hash_lookup(hsh.code).await?;
        Ok(rmp_serde::from_slice(&bs)?)
    }

    async fn hash_put_generic<T: Serialize>(self: &Arc<Self>, value: &T) -> Res<Hash<T>> {
        let bs = rmp_serde::to_vec(&value)?;
        Ok(Hash::from_hashcode(self.clone().hash_put(bs).await?))
    }

    async fn update_dirty(self: &Arc<Self>) -> Res<()> {
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
                            _ => bail!("Lattice key {:?} has no merkle hash", lat_key),
                        };
                        let merkle = self.hash_lookup_generic(merkle_hash).await?;
                        let old_ctx = Arc::new(LatStoreImmutCtx {
                            store: self.clone(),
                            deps: merkle.deps
                        });
                        let tr_value = self.lat_lib.clone().transport(&lat_key, &merkle.value, old_ctx, self.clone()).await?;
                        let bot = self.lat_lib.clone().bottom(&lat_key).await?;
                        let tr_value2 = tr_value.clone();
                        let ((), tr_deps) = self.with_get_deps(move |this| async move {
                            this.lat_lib.clone().check_elem(&lat_key, &tr_value2, this).await
                        }).await?;
                        let merkle_deps = tr_deps.to_merkle_deps();
                        if tr_value == bot && merkle_deps.is_empty() {
                            self.get_db().clear_value_deps(&key)?;
                        } else {
                            let merkle_hash = self.hash_put_generic(&LatMerkleNode {
                                value: tr_value,
                                deps: tr_deps.to_merkle_deps(),
                            }).await?;
                            self.get_db().set_value_deps(key.clone(), LatDBValue::Lattice(merkle_hash), tr_deps.to_keys())?;
                        }
                    }
                    LatDBKey::LatComputation(lat_comp_key) => {
                        let (value, deps) = self.with_get_deps(move |this| async move {
                            this.lat_lib.clone().eval_lat_computation(lat_comp_key, this).await
                        }).await?;
                        let merkle_hash = self.hash_put_generic(&LatMerkleNode {
                            value,
                            deps: deps.to_merkle_deps(),
                        }).await?;
                        self.get_db().set_value_deps(key.clone(), LatDBValue::LatComputation(merkle_hash), deps.to_keys())?;
                    }
                    _ => {}
                }
            }
        }
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> HashLookup for LatStore<C, L, LC> {

    async fn hash_lookup(self: Arc<Self>, hash: HashCode) -> Res<Vec<u8>> {
        if let Some(deps) = self.deps_stack.lock().unwrap().last_mut() {
            deps.hash_deps.insert(hash);
        }
        let res = self.get_db().get_value(&LatDBKey::Hash(hash))?;
        match res {
            Some(LatDBValue::Hash(bytes)) => Ok(bytes),
            _ => bail!("Hash {:?} not found", hash),
        }
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> ComputationImmutContext<C> for LatStore<C, L, LC> {

    async fn eval_computation(self: Arc<Self>, key: &C::Key) -> Res<C::Value> {
        if let Some(deps) = self.deps_stack.lock().unwrap().last_mut() {
            deps.comp_deps.insert(key.clone());
        }
        let computation_key = LatDBKey::Computation(key.clone());
        if let Some(LatDBValue::Computation(value)) = self.get_db().get_value(&computation_key)? {
            return Ok(value);
        }
        let key2 = key.clone();
        let (value, deps) = self.with_get_deps(move |this| async move {
            this.comp_lib.clone().eval_computation(&key2, this).await
        }).await?;
        self.get_db().set_value_deps(computation_key, LatDBValue::Computation(value.clone()), deps.to_keys())?;
        Ok(value)
    }

}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> ComputationMutContext<C> for LatStore<C, L, LC> {

    async fn hash_put(self: Arc<Self>, value: Vec<u8>) -> Res<HashCode> {
        let hash = hash_of_bytes(&value);
        let key = LatDBKey::Hash(hash);
        if !self.get_db().has_value(&key)? {
            self.get_db().set_value_deps(key.clone(), LatDBValue::Hash(value), Vec::new())?;
        }
        Ok(hash)
    }

}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeImmutContext<C, L, LC> for LatStore<C, L, LC> {

    async fn lattice_lookup(self: Arc<Self>, key: &L::Key) -> Res<(L::Value, Arc<dyn LatticeImmutContext<C, L, LC>>)> {
        let db_value = self.get_db().get_value(&LatDBKey::Lattice(key.clone()))?;
        match db_value {
            Some(LatDBValue::Lattice(merkle_hash)) => {
                let merkle = self.hash_lookup_generic(merkle_hash).await?;
                if let Some(deps) = self.deps_stack.lock().unwrap().last_mut() {
                    deps.lat_deps.insert(key.clone(), hash(&merkle));
                }
                Ok((merkle.value, Arc::new(LatStoreImmutCtx {
                    store: self,
                    deps: merkle.deps
                })))
            }
            None => {
                let bot = self.lat_lib.clone().bottom(key).await?;
                Ok((bot, Arc::new(LatStoreImmutCtx {
                    store: self,
                    deps: LatMerkleNodeDeps::new()
                })))
            }
            _ => bail!("Lattice key has no lattice value"),
        }
    }

    async fn eval_lat_computation(self: Arc<Self>, key: &LC::Key) -> Res<(LC::Value, Arc<dyn LatticeImmutContext<C, L, LC>>)> {
        let db_value = self.get_db().get_value(&LatDBKey::LatComputation(key.clone()))?;
        let merkle = match db_value {
            Some(LatDBValue::LatComputation(merkle_hash)) => self.hash_lookup_generic(merkle_hash).await?,
            _ => {
                let key2 = key.clone();
                let (value, deps) = self.with_get_deps(move |this| async move {
                    this.lat_lib.clone().eval_lat_computation(&key2, this).await
                }).await?;
                let merkle = LatMerkleNode {
                    value: value,
                    deps: deps.to_merkle_deps()
                };
                let merkle_hash = self.hash_put_generic(&merkle).await?;
                self.get_db().set_value_deps(LatDBKey::LatComputation(key.clone()), LatDBValue::LatComputation(merkle_hash), deps.to_keys())?;
                merkle
            }
        };
        if let Some(deps) = self.deps_stack.lock().unwrap().last_mut() {
            deps.lat_comp_deps.insert(key.clone(), hash(&merkle));
        }
        Ok((merkle.value, Arc::new(LatStoreImmutCtx {
            store: self,
            deps: merkle.deps
        })))
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeMutContext<C, L, LC> for LatStore<C, L, LC> {

    async fn lattice_join(self: Arc<Self>, key: &L::Key, value: &L::Value, ctx_other: Arc<dyn LatticeImmutContext<C, L, LC>>) -> Res<L::Value> {
        let value = self.lat_lib.clone().transport(key, value, ctx_other, self.clone()).await?;
        let db_value = self.get_db().get_value(&LatDBKey::Lattice(key.clone()))?;
        let new_value = match db_value {
            None => value.clone(),
            Some(LatDBValue::Lattice(old_merkle_hash)) => {
                let old_merkle = self.hash_lookup_generic(old_merkle_hash).await?;
                let old_merkle_value2 = old_merkle.value.clone();
                let ((), old_deps) = self.with_get_deps(move |this| async move {
                    this.lat_lib.clone().check_elem(key, &old_merkle_value2, this).await
                }).await?;
                // assume it's already been transported??
                let joined = self.lat_lib.clone().join(key, &old_merkle.value, &value, self.clone()).await?;
                if joined == old_merkle.value {
                    return Ok(old_merkle.value);
                }
                joined
            }
            _ => bail!("lattice value is not a lattice")
        };
        let bot = self.lat_lib.clone().bottom(key).await?;
        let new_value2 = new_value.clone();
        let ((), deps) = self.with_get_deps(move |this| async move {
            this.lat_lib.clone().check_elem(key, &new_value2, this).await
        }).await?;
        let merkle_deps = deps.to_merkle_deps();
        if new_value == bot && merkle_deps.is_empty() {
            self.get_db().clear_value_deps(&LatDBKey::Lattice(key.clone()))?;
        } else {
            let merkle_hash = self.hash_put_generic(&LatMerkleNode {
                value: new_value.clone(),
                deps: deps.to_merkle_deps()
            }).await?;
            self.get_db().set_value_deps(LatDBKey::Lattice(key.clone()), LatDBValue::Lattice(merkle_hash), deps.to_keys())?;
            self.update_dirty().await?;
        }
        Ok(new_value)
    }
}

pub struct LatStoreImmutCtx<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> {
    store: Arc<LatStore<C, L, LC>>,
    deps: LatMerkleNodeDepsM<L, LC>,
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> HashLookup for LatStoreImmutCtx<C, L, LC> {
    async fn hash_lookup(self: Arc<Self>, hash: HashCode) -> Res<Vec<u8>> {
        self.store.clone().hash_lookup(hash).await
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> ComputationImmutContext<C> for LatStoreImmutCtx<C, L, LC> {

    async fn eval_computation(self: Arc<Self>, key: &C::Key) -> Res<C::Value> {
        self.store.clone().eval_computation(key).await
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeImmutContext<C, L, LC> for LatStoreImmutCtx<C, L, LC> {
    async fn lattice_lookup(self: Arc<Self>, key: &L::Key) -> Res<(L::Value, Arc<dyn LatticeImmutContext<C, L, LC>>)> {
        match self.deps.lat_deps.get(key) {
            None => {
                let bot = self.store.lat_lib.clone().bottom(key).await?;
                Ok((bot, Arc::new(LatStoreImmutCtx {
                    store: self.store.clone(),
                    deps: LatMerkleNodeDeps::new()
                })))
            }
            Some(merkle_hash) => {
                let merkle = self.store.hash_lookup_generic(merkle_hash.clone()).await?;
                Ok((merkle.value, Arc::new(LatStoreImmutCtx {
                    store: self.store.clone(),
                    deps: merkle.deps,
                })))
            }
        }
    }

    async fn eval_lat_computation(self: Arc<Self>, key: &LC::Key) -> Res<(LC::Value, Arc<dyn LatticeImmutContext<C, L, LC>>)> {
        match self.deps.lat_comp_deps.get(key) {
            None => bail!("lattice computation dependency not found"),
            Some(merkle_hash) => {
                let merkle = self.store.hash_lookup_generic(merkle_hash.clone()).await?;
                Ok((merkle.value, Arc::new(LatStoreImmutCtx {
                    store: self.store.clone(),
                    deps: merkle.deps,
                })))
            }
        }
    }
}

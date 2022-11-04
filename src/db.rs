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
use crate::lattice::{HashLookup, hash_lookup_generic, hash_put_generic, LatticeLibrary, ComputationLibrary, ComputationImmutContext, HashPut, LatticeImmutContext, LatticeMutContext, LatMerkleDeps, LatMerkleNode, EmptyContext};
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
pub enum LatDBKey<CK, LK, LCK> {
    Hash(HashCode),
    Computation(CK),
    Lattice(LK),
    LatComputation(LCK),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub enum LatDBValue<CV, LK: Ord, LV, LCK: Ord, LCV> {
    Hash(Vec<u8>),
    Computation(CV),
    Lattice(Hash<LatMerkleNode<LK, LV, LCK, LCV, LV>>),
    LatComputation(Hash<LatMerkleNode<LK, LV, LCK, LCV, LCV>>),
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub struct LatDeps<CK: Ord, LK: Ord, LV, LCK: Ord, LCV> {
    hash_deps: BTreeSet<HashCode>,
    comp_deps: BTreeSet<CK>,
    lat_deps: BTreeMap<LK, Hash<LatMerkleNode<LK, LV, LCK, LCV, LV>>>,
    lat_comp_deps: BTreeMap<LCK, Hash<LatMerkleNode<LK, LV, LCK, LCV, LCV>>>,
}

impl<CK: Ord, LK: Ord + Clone, LV, LCK: Ord + Clone, LCV> LatDeps<CK, LK, LV, LCK, LCV> {
    pub fn to_merkle_deps(&self) -> LatMerkleDeps<LK, LV, LCK, LCV> {
        LatMerkleDeps {
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
    type Key = LatDBKey<C::Key, L::Key, LC::Key>;
    type Value = LatDBValue<C::Value, L::Key, L::Value, LC::Key, LC::Value>;
}

struct LatDepsTracker<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping, Ctx> {
    ctx: Arc<Ctx>,
    deps: Arc<Mutex<LatDeps<C::Key, L::Key, L::Value, LC::Key, LC::Value>>>,
}

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping, Ctx> LatDepsTracker<C, L, LC, Ctx> {
    fn new(ctx: &Arc<Ctx>) -> Self {
        LatDepsTracker {
            ctx: ctx.clone(),
            deps: Arc::new(Mutex::new(LatDeps::new())),
        }
    }
    fn get_deps(&self) -> LatDeps<C::Key, L::Key, L::Value, LC::Key, LC::Value> {
        self.deps.lock().unwrap().clone()
    }
    async fn with_get_deps<'a, T, F: Future<Output = Res<T>>>(ctx: &Arc<Ctx>, f: impl FnOnce(Arc<Self>) -> F) -> Res<(T, LatDeps<C::Key, L::Key, L::Value, LC::Key, LC::Value>)> {
        let tracker = Arc::new(Self::new(ctx));
        let res = f(tracker.clone()).await?;
        let deps = tracker.get_deps();
        Ok((res, deps))
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static, Ctx: HashLookup> HashLookup for LatDepsTracker<C, L, LC, Ctx> {
    async fn hash_lookup(self: Arc<Self>, hash: HashCode) -> Res<Vec<u8>> {
        self.deps.lock().unwrap().hash_deps.insert(hash.clone());
        self.ctx.clone().hash_lookup(hash).await
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static, Ctx: ComputationImmutContext<C>> ComputationImmutContext<C> for LatDepsTracker<C, L, LC, Ctx> {
    async fn eval_computation(self: Arc<Self>, key: &C::Key) -> Res<C::Value> {
        self.deps.lock().unwrap().comp_deps.insert(key.clone());
        self.ctx.clone().eval_computation(key).await
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static, Ctx: LatticeImmutContext<C, L, LC>> LatticeImmutContext<C, L, LC> for LatDepsTracker<C, L, LC, Ctx> {
    async fn lattice_lookup(self: Arc<Self>, key: &L::Key) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>> {
        let res = self.ctx.clone().lattice_lookup(key).await?;
        if let Some(value) = res {
            self.deps.lock().unwrap().lat_deps.insert(key.clone(), value);
        }
        Ok(res)
    }

    async fn eval_lat_computation(self: Arc<Self>, key: &LC::Key) -> Res<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, LC::Value>>> {
        let res = self.ctx.clone().eval_lat_computation(key).await?;
        self.deps.lock().unwrap().lat_comp_deps.insert(key.clone(), res.clone());
        Ok(res)
    }
}


pub struct LatStore<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> {
    db: Arc<Mutex<dyn DepDB<LatDBMapping<C, L, LC>>>>,
    comp_lib: Arc<dyn ComputationLibrary<C>>,
    lat_lib: Arc<dyn LatticeLibrary<C, L, LC>>,
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> Clone for LatStore<C, L, LC> {
    fn clone(&self) -> Self {
        LatStore {
            db: self.db.clone(),
            comp_lib: self.comp_lib.clone(),
            lat_lib: self.lat_lib.clone(),
        }
    }
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatStore<C, L, LC> {
    pub fn new(db: impl DepDB<LatDBMapping<C, L, LC>> + 'static,
               comp_lib: impl ComputationLibrary<C> + 'static,
               lat_lib: impl LatticeLibrary<C, L, LC> + 'static) -> Self {
        Self {
            db: Arc::new(Mutex::new(db)),
            comp_lib: Arc::new(comp_lib),
            lat_lib: Arc::new(lat_lib),
        }
    }

    fn get_db(&self) -> MutexGuard<dyn DepDB<LatDBMapping<C, L, LC>> + 'static> {
        self.db.lock().unwrap()
    }

    pub fn set_hash_pin(&mut self, hash: HashCode, pin: bool) -> Res<()> {
        self.get_db().set_pin(&LatDBKey::Hash(hash), pin)
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

    async fn update_dirty(self: Arc<Self>) -> Res<()> {
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
                        let merkle = hash_lookup_generic(&self, merkle_hash).await?;
                        let new_ctx = self.clone();
                        let old_ctx = Arc::new(LatStoreJoinedCtx::from_store(new_ctx.clone()));
                        let opt_tr_value = self.lat_lib.clone().transport(&lat_key, &merkle.value, old_ctx, new_ctx).await?;
                        match opt_tr_value {
                            None => {
                                self.get_db().clear_value_deps(&key)?;
                            }
                            Some(tr_value) => {
                                let tr_value2 = tr_value.clone();
                                let lat_lib = self.lat_lib.clone();
                                let ((), tr_deps) = LatDepsTracker::with_get_deps(&self, move |this| async move {
                                    lat_lib.check_elem(&lat_key, &tr_value2, this).await
                                }).await?;
                                let merkle_deps = tr_deps.to_merkle_deps();
                                let merkle_hash = hash_put_generic(&self, &LatMerkleNode {
                                    value: tr_value,
                                    deps: tr_deps.to_merkle_deps(),
                                }).await?;
                                self.get_db().set_value_deps(key.clone(), LatDBValue::Lattice(merkle_hash), tr_deps.to_keys())?;
                            }
                        }
                    }
                    LatDBKey::LatComputation(lat_comp_key) => {
                        let lat_lib = self.lat_lib.clone();
                        let (value, deps) = LatDepsTracker::with_get_deps(&self, move |this| async move {
                            lat_lib.eval_lat_computation(lat_comp_key, this).await
                        }).await?;
                        let merkle_hash = hash_put_generic(&self, &LatMerkleNode {
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
        let res = self.get_db().get_value(&LatDBKey::Hash(hash))?;
        match res {
            Some(LatDBValue::Hash(bytes)) => Ok(bytes),
            _ => bail!("Hash {:?} not found", hash),
        }
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> HashPut for LatStore<C, L, LC> {

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
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> ComputationImmutContext<C> for LatStore<C, L, LC> {

    async fn eval_computation(self: Arc<Self>, key: &C::Key) -> Res<C::Value> {
        let computation_key = LatDBKey::Computation(key.clone());
        if let Some(LatDBValue::Computation(value)) = self.get_db().get_value(&computation_key)? {
            return Ok(value);
        }
        let key2 = key.clone();
        let comp_lib = self.comp_lib.clone();
        let (value, deps) = LatDepsTracker::<C, L, LC, _>::with_get_deps(&self, move |this| async move {
            comp_lib.eval_computation(&key2, this).await
        }).await?;
        self.get_db().set_value_deps(computation_key, LatDBValue::Computation(value.clone()), deps.to_keys())?;
        Ok(value)
    }

}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeImmutContext<C, L, LC> for LatStore<C, L, LC> {

    async fn lattice_lookup(self: Arc<Self>, key: &L::Key) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>> {
        let db_value = self.get_db().get_value(&LatDBKey::Lattice(key.clone()))?;
        match db_value {
            Some(LatDBValue::Lattice(merkle_hash)) => Ok(Some(merkle_hash)),
            None => Ok(None),
            _ => bail!("Lattice key has no lattice value"),
        }
    }

    async fn eval_lat_computation(self: Arc<Self>, key: &LC::Key) -> Res<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, LC::Value>>> {
        let db_value = self.get_db().get_value(&LatDBKey::LatComputation(key.clone()))?;
        match db_value {
            Some(LatDBValue::LatComputation(merkle_hash)) => Ok(merkle_hash),
            None => {
                let key2 = key.clone();
                let lat_lib = self.lat_lib.clone();
                let (value, deps) = LatDepsTracker::with_get_deps(&self, move |this| async move {
                    lat_lib.eval_lat_computation(&key2, this).await
                }).await?;
                let merkle = LatMerkleNode {
                    value: value,
                    deps: deps.to_merkle_deps()
                };
                let merkle_hash = hash_put_generic(&self, &merkle).await?;
                self.get_db().set_value_deps(LatDBKey::LatComputation(key.clone()), LatDBValue::LatComputation(merkle_hash), deps.to_keys())?;
                Ok(merkle_hash)
            },
            _ => bail!("Lattice computation key has no lattice computation value"),
        }
    }
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeMutContext<C, L, LC> for LatStore<C, L, LC> {}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatStore<C, L, LC> {

    async fn lattice_join(self: Arc<Self>, key: &L::Key, other_merkle_hash: Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>, other_hashlookup: Arc<dyn HashLookup>) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>> {
        let mut other_deps = LatMerkleDeps::new();
        other_deps.lat_deps.insert(key.clone(), other_merkle_hash);
        let join_ctx = LatStoreJoinedCtx {
            store: self,
            other_hashlookup,
            other_deps: Arc::new(Mutex::new(other_deps)),
            use_store_lattices: true
        };
        Arc::new(join_ctx).lattice_lookup(key).await
    }
}

pub struct LatStoreJoinedCtx<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> {
    store: Arc<LatStore<C, L, LC>>,
    other_hashlookup: Arc<dyn HashLookup>,
    other_deps: Arc<Mutex<LatMerkleDeps<L::Key, L::Value, LC::Key, LC::Value>>>,
    use_store_lattices: bool,
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatStoreJoinedCtx<C, L, LC> {
    fn from_store(store: Arc<LatStore<C, L, LC>>) -> Self {
        LatStoreJoinedCtx {
            store: store,
            other_hashlookup: Arc::new(EmptyContext),
            other_deps: Arc::new(Mutex::new(LatMerkleDeps::new())),
            use_store_lattices: true,
        }
    }
    fn only_other_deps(&self) -> Self {
        Self {
            store: self.store.clone(),
            other_hashlookup: self.other_hashlookup.clone(),
            other_deps: self.other_deps.clone(),
            use_store_lattices: false,
        }
    }
    fn only_store_deps(&self) -> Self {
        Self {
            store: self.store.clone(),
            other_hashlookup: self.other_hashlookup.clone(),
            other_deps: Arc::new(Mutex::new(LatMerkleDeps::new())),
            use_store_lattices: true,
        }
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> Clone for LatStoreJoinedCtx<C, L, LC> {
    fn clone(&self) -> Self {
        LatStoreJoinedCtx {
            store: self.store.clone(),
            other_hashlookup: self.other_hashlookup.clone(),
            other_deps: self.other_deps.clone(),
            use_store_lattices: self.use_store_lattices
        }
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> HashLookup for LatStoreJoinedCtx<C, L, LC> {
    async fn hash_lookup(self: Arc<Self>, hash: HashCode) -> Res<Vec<u8>> {
        match self.store.clone().hash_lookup(hash).await {
            Ok(value) => Ok(value),
            Err(_) => {
                let other_bs = self.other_hashlookup.clone().hash_lookup(hash).await?;
                if hash_of_bytes(&other_bs) == hash {
                    Ok(other_bs)
                } else {
                    bail!("hash lookup failed")
                }
            }
        }
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> HashPut for LatStoreJoinedCtx<C, L, LC> {
    async fn hash_put(self: Arc<Self>, value: Vec<u8>) -> Res<HashCode> {
        self.store.clone().hash_put(value).await
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> ComputationImmutContext<C> for LatStoreJoinedCtx<C, L, LC> {
    async fn eval_computation(self: Arc<Self>, key: &C::Key) -> Res<C::Value> {
        let computation_key = LatDBKey::Computation(key.clone());
        if let Some(LatDBValue::Computation(value)) = self.store.get_db().get_value(&computation_key)? {
            return Ok(value);
        }
        let key2 = key.clone();
        let comp_lib = self.store.comp_lib.clone();
        let (value, deps) = LatDepsTracker::<C, L, LC, _>::with_get_deps(&self, move |this| async move {
            comp_lib.eval_computation(&key2, this).await
        }).await?;
        self.store.get_db().set_value_deps(computation_key, LatDBValue::Computation(value.clone()), deps.to_keys())?;
        Ok(value)
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeImmutContext<C, L, LC> for LatStoreJoinedCtx<C, L, LC> {
    async fn lattice_lookup(self: Arc<Self>, key: &L::Key) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>> {
        let store_dep = if self.use_store_lattices {
            self.store.clone().lattice_lookup(key).await?
        } else {
            None
        };
        let other_dep = self.other_deps.lock().unwrap().lat_deps.get(key).cloned();
        if store_dep == other_dep || other_dep.is_none() {
            return Ok(store_dep);
        }
        let other_dep = other_dep.unwrap();
        let other_merkle = hash_lookup_generic(&self.other_hashlookup, other_dep).await?;
        self.other_deps.lock().unwrap().try_union(other_merkle.deps)?;
        let lat_lib = self.store.lat_lib.clone();
        let (joined, deps) = match store_dep {
            None => {
                let value2 = other_merkle.value.clone();
                let ((), deps) = LatDepsTracker::<C, L, LC, _>::with_get_deps(&self, move |this| async move {
                    lat_lib.check_elem(&key, &value2, this).await
                }).await?;
                (other_merkle.value, deps)
            },
            Some(store_dep) => {
                let store_merkle = hash_lookup_generic(&self.store, store_dep).await?;
                // TODO check_elem other??
                let store_tr = lat_lib.clone().transport(key, &store_merkle.value, Arc::new(self.only_store_deps()), self.clone()).await?;
                let other_tr = lat_lib.clone().transport(key, &other_merkle.value, Arc::new(self.only_other_deps()), self.clone()).await?;
                let joined = match store_tr {
                    None => other_tr,
                    Some(store_tr) => match other_tr {
                        None => Some(store_tr),
                        Some(other_tr) => lat_lib.clone().join(key, &store_tr, &other_tr, self.clone()).await?
                    }
                };
                match joined {
                    None => {
                        self.store.get_db().clear_value_deps(&LatDBKey::Lattice(key.clone()))?;
                        return Ok(None)
                    },
                    Some(joined) => {
                        LatDepsTracker::<C, L, LC, _>::with_get_deps(&self, move |this| async move {
                            lat_lib.check_elem(&key, &joined, this).await?;
                            Ok(joined)
                        }).await?
                    }
                }
            }
        };
        let merkle = LatMerkleNode {
            value: joined,
            deps: deps.to_merkle_deps()
        };
        let merkle_hash = hash_put_generic(&self.store, &merkle).await?;
        if store_dep != Some(merkle_hash) {
            self.store.get_db().set_value_deps(LatDBKey::Lattice(key.clone()), LatDBValue::Lattice(merkle_hash), deps.to_keys())?;
            self.store.clone().update_dirty().await?;
        }
        Ok(Some(merkle_hash))
    }

    async fn eval_lat_computation(self: Arc<Self>, key: &LC::Key) -> Res<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, LC::Value>>> {
        // TODO: track redundant paths to same key, invalidate if other uses different ones?
        let store_dep = if self.use_store_lattices {
            Some(self.store.clone().eval_lat_computation(key).await?)
        } else {
            None
        };
        let other_dep = self.other_deps.lock().unwrap().lat_comp_deps.get(key).cloned();
        if store_dep.is_some() && store_dep == other_dep {
            return Ok(store_dep.unwrap());
        }
        let other_deps = match other_dep {
            None => LatMerkleDeps::new(),
            Some(other_dep) => hash_lookup_generic(&self.other_hashlookup, other_dep).await?.deps
        };
        self.other_deps.lock().unwrap().try_union(other_deps)?;
        let lat_lib = self.store.lat_lib.clone();
        let (value, deps) = LatDepsTracker::<C, L, LC, _>::with_get_deps(&self, move |this| async move {
            lat_lib.eval_lat_computation(&key, this).await
        }).await?;
        let merkle = LatMerkleNode {value, deps: deps.to_merkle_deps()};
        let merkle_hash = hash_put_generic(&self.store, &merkle).await?;
        if store_dep.is_none() || store_dep.unwrap() != merkle_hash {
            self.store.get_db().set_value_deps(LatDBKey::LatComputation(key.clone()), LatDBValue::LatComputation(merkle_hash), deps.to_keys())?;
            self.store.clone().update_dirty().await?;
        }
        Ok(merkle_hash)
    }
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeMutContext<C, L, LC> for LatStoreJoinedCtx<C, L, LC> {}

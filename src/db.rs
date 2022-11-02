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
use crate::lattice::{HashLookup, LatticeLibrary, ComputationLibrary, ComputationImmutContext, ComputationMutContext, LatticeImmutContext, LatticeMutContext, LatMerkleNodeDeps, LatMerkleNode, EmptyContext};
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
    type Key = LatDBKey<C::Key, L::Key, LC::Key>;
    type Value = LatDBValue<C::Value, L::Key, L::Value, LC::Key, LC::Value>;
}

struct LatDepsTracker<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping, Ctx> {
    ctx: Arc<Ctx>,
    deps: Arc<Mutex<LatDeps<C::Key, L::Key, L::Value, LC::Key, LC::Value>>>,
}

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping, Ctx: Clone> LatDepsTracker<C, L, LC, Ctx> {
    fn new(ctx: &Ctx) -> Self {
        LatDepsTracker {
            ctx: Arc::new(ctx.clone()),
            deps: Arc::new(Mutex::new(LatDeps::new())),
        }
    }
    fn get_deps(&self) -> LatDeps<C::Key, L::Key, L::Value, LC::Key, LC::Value> {
        self.deps.lock().unwrap().clone()
    }
    async fn with_get_deps<'a, T, F: Future<Output = Res<T>>>(ctx: &Ctx, f: impl FnOnce(Arc<Self>) -> F) -> Res<(T, LatDeps<C::Key, L::Key, L::Value, LC::Key, LC::Value>)> {
        let tracker = Arc::new(Self::new(ctx));
        let res = f(tracker.clone()).await?;
        let deps = tracker.get_deps();
        Ok((res, deps))
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static, Ctx: HashLookup> HashLookup for LatDepsTracker<C, L, LC, Ctx> {
    async fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>> {
        self.deps.lock().unwrap().hash_deps.insert(hash.clone());
        self.ctx.hash_lookup(hash).await
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static, Ctx: ComputationImmutContext<C>> ComputationImmutContext<C> for LatDepsTracker<C, L, LC, Ctx> {
    async fn eval_computation(&self, key: &C::Key) -> Res<C::Value> {
        self.deps.lock().unwrap().comp_deps.insert(key.clone());
        self.ctx.eval_computation(key).await
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static, Ctx: LatticeImmutContext<C, L, LC>> LatticeImmutContext<C, L, LC> for LatDepsTracker<C, L, LC, Ctx> {
    async fn lattice_lookup(&self, key: &L::Key) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>> {
        let res = self.ctx.lattice_lookup(key).await?;
        if let Some(value) = res {
            self.deps.lock().unwrap().lat_deps.insert(key.clone(), value);
        }
        Ok(res)
    }

    async fn eval_lat_computation(&self, key: &LC::Key) -> Res<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, LC::Value>>> {
        let res = self.ctx.eval_lat_computation(key).await?;
        self.deps.lock().unwrap().lat_comp_deps.insert(key.clone(), res.clone());
        Ok(res)
    }
}


pub struct LatStore<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> {
    db: Arc<Mutex<dyn DepDB<LatDBMapping<C, L, LC>>>>,
    comp_lib: Arc<dyn ComputationLibrary<C>>,
    lat_lib: Arc<dyn LatticeLibrary<C, L, LC>>,
    deps_stack: Arc<Mutex<Vec<LatDeps<C::Key, L::Key, L::Value, LC::Key, LC::Value>>>>,
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> Clone for LatStore<C, L, LC> {
    fn clone(&self) -> Self {
        LatStore {
            db: self.db.clone(),
            comp_lib: self.comp_lib.clone(),
            lat_lib: self.lat_lib.clone(),
            deps_stack: self.deps_stack.clone(),
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
            deps_stack: Arc::new(Mutex::new(Vec::new())),
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

    async fn hash_lookup_generic<T: DeserializeOwned>(&self, hsh: Hash<T>) -> Res<T> {
        let bs = self.hash_lookup(hsh.code).await?;
        Ok(rmp_serde::from_slice(&bs)?)
    }

    async fn hash_put_generic<T: Serialize>(&self, value: &T) -> Res<Hash<T>> {
        let bs = rmp_serde::to_vec(&value)?;
        Ok(Hash::from_hashcode(self.hash_put(bs).await?))
    }

    async fn update_dirty(&self) -> Res<()> {
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
                        let new_ctx = Arc::new(self.clone());
                        let old_ctx = Arc::new(LatStoreJoinedCtx::from_store(new_ctx.clone(), merkle.deps));
                        let opt_tr_value = self.lat_lib.transport(&lat_key, &merkle.value, old_ctx, new_ctx).await?;
                        match opt_tr_value {
                            None => {
                                self.get_db().clear_value_deps(&key)?;
                            }
                            Some(tr_value) => {
                                let tr_value2 = tr_value.clone();
                                let lat_lib = self.lat_lib.clone();
                                let ((), tr_deps) = LatDepsTracker::with_get_deps(self, move |this| async move {
                                    lat_lib.check_elem(&lat_key, &tr_value2, this).await
                                }).await?;
                                let merkle_deps = tr_deps.to_merkle_deps();
                                let merkle_hash = self.hash_put_generic(&LatMerkleNode {
                                    value: tr_value,
                                    deps: tr_deps.to_merkle_deps(),
                                }).await?;
                                self.get_db().set_value_deps(key.clone(), LatDBValue::Lattice(merkle_hash), tr_deps.to_keys())?;
                            }
                        }
                    }
                    LatDBKey::LatComputation(lat_comp_key) => {
                        let lat_lib = self.lat_lib.clone();
                        let (value, deps) = LatDepsTracker::with_get_deps(self, move |this| async move {
                            lat_lib.eval_lat_computation(lat_comp_key, this).await
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

    async fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>> {
        let res = self.get_db().get_value(&LatDBKey::Hash(hash))?;
        match res {
            Some(LatDBValue::Hash(bytes)) => Ok(bytes),
            _ => bail!("Hash {:?} not found", hash),
        }
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> ComputationImmutContext<C> for LatStore<C, L, LC> {

    async fn eval_computation(&self, key: &C::Key) -> Res<C::Value> {
        let computation_key = LatDBKey::Computation(key.clone());
        if let Some(LatDBValue::Computation(value)) = self.get_db().get_value(&computation_key)? {
            return Ok(value);
        }
        let key2 = key.clone();
        let comp_lib = self.comp_lib.clone();
        let (value, deps) = LatDepsTracker::<C, L, LC, _>::with_get_deps(self, move |this| async move {
            comp_lib.eval_computation(&key2, this).await
        }).await?;
        self.get_db().set_value_deps(computation_key, LatDBValue::Computation(value.clone()), deps.to_keys())?;
        Ok(value)
    }

}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> ComputationMutContext<C> for LatStore<C, L, LC> {

    async fn hash_put(&self, value: Vec<u8>) -> Res<HashCode> {
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

    async fn lattice_lookup(&self, key: &L::Key) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>> {
        let db_value = self.get_db().get_value(&LatDBKey::Lattice(key.clone()))?;
        match db_value {
            Some(LatDBValue::Lattice(merkle_hash)) => Ok(Some(merkle_hash)),
            None => Ok(None),
            _ => bail!("Lattice key has no lattice value"),
        }
    }

    async fn eval_lat_computation(&self, key: &LC::Key) -> Res<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, LC::Value>>> {
        let db_value = self.get_db().get_value(&LatDBKey::LatComputation(key.clone()))?;
        match db_value {
            Some(LatDBValue::LatComputation(merkle_hash)) => Ok(merkle_hash),
            None => {
                let key2 = key.clone();
                let lat_lib = self.lat_lib.clone();
                let (value, deps) = LatDepsTracker::with_get_deps(self, move |this| async move {
                    lat_lib.eval_lat_computation(&key2, this).await
                }).await?;
                let merkle = LatMerkleNode {
                    value: value,
                    deps: deps.to_merkle_deps()
                };
                let merkle_hash = self.hash_put_generic(&merkle).await?;
                self.get_db().set_value_deps(LatDBKey::LatComputation(key.clone()), LatDBValue::LatComputation(merkle_hash), deps.to_keys())?;
                Ok(merkle_hash)
            },
            _ => bail!("Lattice computation key has no lattice computation value"),
        }
    }
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeMutContext<C, L, LC> for LatStore<C, L, LC> {}

// impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatStore<C, L, LC> {
// 
//     async fn lattice_join(&self, key: &L::Key, merkle: LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>, ctx_other: Arc<dyn HashLookup>) -> Res<L::Value> {
//         // TODO: we need to unify the dependencies of the two contexts
//         let db_value = self.get_db().get_value(&LatDBKey::Lattice(key.clone()))?;
//         let new_value = match db_value {
//             None => value.clone(),
//             Some(LatDBValue::Lattice(old_merkle_hash)) => {
//                 let old_merkle = self.hash_lookup_generic(old_merkle_hash).await?;
//                 let old_merkle_value2 = old_merkle.value.clone();
//                 let ((), old_deps) = self.with_get_deps(move |this| async move {
//                     this.lat_lib.clone().check_elem(key, &old_merkle_value2, this).await
//                 }).await?;
//                 // assume it's already been transported??
//                 let joined = self.lat_lib.join(key, &old_merkle.value, &value, Arc::new(self.clone())).await?;
//                 if joined == old_merkle.value {
//                     return Ok(old_merkle.value);
//                 }
//                 joined
//             }
//             _ => bail!("lattice value is not a lattice")
//         };
//         let value = self.lat_lib.transport(key, value, ctx_other, Arc::new(self.clone())).await?;
//         let bot = self.lat_lib.bottom(key).await?;
//         let new_value2 = new_value.clone();
//         let ((), deps) = self.with_get_deps(move |this| async move {
//             this.lat_lib.clone().check_elem(key, &new_value2, this).await
//         }).await?;
//         let merkle_deps = deps.to_merkle_deps();
//         if new_value == bot && merkle_deps.is_empty() {
//             self.get_db().clear_value_deps(&LatDBKey::Lattice(key.clone()))?;
//         } else {
//             let merkle_hash = self.hash_put_generic(&LatMerkleNode {
//                 value: new_value.clone(),
//                 deps: deps.to_merkle_deps()
//             }).await?;
//             self.get_db().set_value_deps(LatDBKey::Lattice(key.clone()), LatDBValue::Lattice(merkle_hash), deps.to_keys())?;
//             self.update_dirty().await?;
//         }
//         Ok(new_value)
//     }
// }
pub struct LatStoreJoinedCtx<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> {
    store: Arc<LatStore<C, L, LC>>,
    store_deps: Arc<LatMerkleNodeDeps<L::Key, L::Value, LC::Key, LC::Value>>,
    other_hashlookup: Arc<dyn HashLookup>,
    other_deps: Arc<LatMerkleNodeDeps<L::Key, L::Value, LC::Key, LC::Value>>,
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatStoreJoinedCtx<C, L, LC> {
    fn from_store(store: Arc<LatStore<C, L, LC>>, store_deps: LatMerkleNodeDeps<L::Key, L::Value, LC::Key, LC::Value>) -> Self {
        LatStoreJoinedCtx {
            store: store,
            store_deps: Arc::new(store_deps),
            other_hashlookup: Arc::new(EmptyContext),
            other_deps: Arc::new(LatMerkleNodeDeps::new())
        }
    }
    fn no_store_deps(&self) -> Self {
        Self {
            store: self.store.clone(),
            store_deps: Arc::new(LatMerkleNodeDeps::new()),
            other_hashlookup: self.other_hashlookup.clone(),
            other_deps: self.other_deps.clone(),
        }
    }
    fn no_other_deps(&self) -> Self {
        Self {
            store: self.store.clone(),
            store_deps: self.store_deps.clone(),
            other_hashlookup: self.other_hashlookup.clone(),
            other_deps: Arc::new(LatMerkleNodeDeps::new()),
        }
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> Clone for LatStoreJoinedCtx<C, L, LC> {
    fn clone(&self) -> Self {
        LatStoreJoinedCtx {
            store: self.store.clone(),
            store_deps: self.store_deps.clone(),
            other_hashlookup: self.other_hashlookup.clone(),
            other_deps: self.other_deps.clone(),
        }
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> HashLookup for LatStoreJoinedCtx<C, L, LC> {
    async fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>> {
        match self.store.hash_lookup(hash).await {
            Ok(value) => Ok(value),
            Err(_) => {
                let other_bs = self.other_hashlookup.hash_lookup(hash).await?;
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
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> ComputationImmutContext<C> for LatStoreJoinedCtx<C, L, LC> {
    async fn eval_computation(&self, key: &C::Key) -> Res<C::Value> {
        if let Some(deps) = self.store.deps_stack.lock().unwrap().last_mut() {
            deps.comp_deps.insert(key.clone());
        }
        let computation_key = LatDBKey::Computation(key.clone());
        if let Some(LatDBValue::Computation(value)) = self.store.get_db().get_value(&computation_key)? {
            return Ok(value);
        }
        let key2 = key.clone();
        let comp_lib = self.store.comp_lib.clone();
        let (value, deps) = LatDepsTracker::<C, L, LC, _>::with_get_deps(self, move |this| async move {
            comp_lib.eval_computation(&key2, this).await
        }).await?;
        self.store.get_db().set_value_deps(computation_key, LatDBValue::Computation(value.clone()), deps.to_keys())?;
        Ok(value)
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> ComputationMutContext<C> for LatStoreJoinedCtx<C, L, LC> {
    async fn hash_put(&self, value: Vec<u8>) -> Res<HashCode> {
        self.store.hash_put(value).await
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeImmutContext<C, L, LC> for LatStoreJoinedCtx<C, L, LC> {
    async fn lattice_lookup(&self, key: &L::Key) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>> {
        let store_dep = self.store_deps.lat_deps.get(key);
        let other_dep = self.other_deps.lat_deps.get(key);
        if store_dep == other_dep || other_dep.is_none() {
            return Ok(store_dep.map(|x| *x));
        }
        let other_dep = other_dep.unwrap();
        let lat_lib = self.store.lat_lib.clone();
        let (joined, deps) = match store_dep {
            None => {
                let other_merkle: LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value> = rmp_serde::from_slice(&self.other_hashlookup.hash_lookup(other_dep.code).await?)?;
                let value2 = other_merkle.value.clone();
                let ((), deps) = LatDepsTracker::<C, L, LC, _>::with_get_deps(self, move |this| async move {
                    lat_lib.check_elem(&key, &value2, this).await
                }).await?;
                (other_merkle.value, deps)
            },
            Some(store_dep) => {
                let store_merkle: LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value> = rmp_serde::from_slice(&self.store.hash_lookup(store_dep.code).await?)?;
                let other_merkle: LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value> = rmp_serde::from_slice(&self.other_hashlookup.hash_lookup(other_dep.code).await?)?;
                // TODO check_elem other??
                let inner_join_ctx = Arc::new(LatStoreJoinedCtx {
                    store: self.store.clone(),
                    store_deps: Arc::new(store_merkle.deps.clone()),
                    other_hashlookup: self.other_hashlookup.clone(),
                    other_deps: Arc::new(other_merkle.deps.clone()),
                });
                let store_tr = self.store.lat_lib.transport(key, &store_merkle.value, Arc::new(inner_join_ctx.no_other_deps()), inner_join_ctx.clone()).await?;
                let other_tr = self.store.lat_lib.transport(key, &other_merkle.value, Arc::new(inner_join_ctx.no_store_deps()), inner_join_ctx.clone()).await?;
                let joined = match store_tr {
                    None => match other_tr {
                        None => {
                            self.store.get_db().clear_value_deps(&LatDBKey::Lattice(key.clone()))?;
                            return Ok(None)
                        }
                        Some(other_tr) => other_tr,
                    }
                    Some(store_tr) => match other_tr {
                        None => store_tr,
                        Some(other_tr) => self.store.lat_lib.join(key, &store_tr, &other_tr, inner_join_ctx.clone()).await?
                    }
                };
                let joined2 = joined.clone();
                let ((), deps) = LatDepsTracker::<C, L, LC, _>::with_get_deps(self, move |this| async move {
                    lat_lib.check_elem(&key, &joined2, inner_join_ctx).await
                }).await?;
                (joined, deps)
            }
        };
        let merkle = LatMerkleNode {
            value: joined,
            deps: deps.to_merkle_deps()
        };
        let merkle_hash = self.store.hash_put_generic(&merkle).await?;
        if store_dep.is_none() || *store_dep.unwrap() != merkle_hash {
            self.store.get_db().set_value_deps(LatDBKey::Lattice(key.clone()), LatDBValue::Lattice(merkle_hash), deps.to_keys())?;
            self.store.update_dirty().await?;
        }
        Ok(Some(merkle_hash))
    }

    async fn eval_lat_computation(&self, key: &LC::Key) -> Res<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, LC::Value>>> {
        let store_dep = self.store_deps.lat_comp_deps.get(key);
        let other_dep = self.other_deps.lat_comp_deps.get(key);
        if store_dep.is_some() && (other_dep.is_none() || store_dep == other_dep) {
            return Ok(*store_dep.unwrap());
        }
        let store_deps = match store_dep {
            None => LatMerkleNodeDeps::new(),
            Some(store_dep) => rmp_serde::from_slice(&self.store.hash_lookup(store_dep.code).await?)?
        };
        let other_deps = match other_dep {
            None => LatMerkleNodeDeps::new(),
            Some(other_dep) => rmp_serde::from_slice(&self.other_hashlookup.hash_lookup(other_dep.code).await?)?
        };
        let inner_join_ctx = Arc::new(LatStoreJoinedCtx {
            store: self.store.clone(),
            store_deps: Arc::new(store_deps),
            other_hashlookup: self.other_hashlookup.clone(),
            other_deps: Arc::new(other_deps),
        });
        let lat_lib = self.store.lat_lib.clone();
        let (value, deps) = LatDepsTracker::<C, L, LC, _>::with_get_deps(self, move |this| async move {
            lat_lib.eval_lat_computation(&key, inner_join_ctx).await
        }).await?;
        let merkle = LatMerkleNode {value, deps: deps.to_merkle_deps()};
        let merkle_hash = self.store.hash_put_generic(&merkle).await?;
        if store_dep.is_none() || *store_dep.unwrap() != merkle_hash {
            self.store.get_db().set_value_deps(LatDBKey::LatComputation(key.clone()), LatDBValue::LatComputation(merkle_hash), deps.to_keys())?;
            self.store.update_dirty().await?;
        }
        Ok(merkle_hash)
    }
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeMutContext<C, L, LC> for LatStoreJoinedCtx<C, L, LC> {}


// pub struct LatStoreImmutCtx<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> {
//     store: Arc<LatStore<C, L, LC>>,
//     deps: Arc<LatMerkleNodeDeps<L::Key, L::Value, LC::Key, LC::Value>>,
// }
// 
// impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> Clone for LatStoreImmutCtx<C, L, LC> {
//     fn clone(&self) -> Self {
//         LatStoreImmutCtx {
//             store: self.store.clone(),
//             deps: self.deps.clone()
//         }
//     }
// }
// 
// #[async_trait]
// impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> HashLookup for LatStoreImmutCtx<C, L, LC> {
//     async fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>> {
//         self.store.clone().hash_lookup(hash).await
//     }
// }
// 
// #[async_trait]
// impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> ComputationImmutContext<C> for LatStoreImmutCtx<C, L, LC> {
// 
//     async fn eval_computation(&self, key: &C::Key) -> Res<C::Value> {
//         self.store.clone().eval_computation(key).await
//     }
// }
// 
// #[async_trait]
// impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeImmutContext<C, L, LC> for LatStoreImmutCtx<C, L, LC> {
//     async fn lattice_lookup(&self, key: &L::Key) -> Res<(L::Value, Arc<dyn LatticeImmutContext<C, L, LC>>)> {
//         match self.deps.lat_deps.get(key) {
//             None => {
//                 let bot = self.store.lat_lib.bottom(key).await?;
//                 Ok((bot, Arc::new(LatStoreImmutCtx {
//                     store: self.store.clone(),
//                     deps: Arc::new(LatMerkleNodeDeps::new())
//                 })))
//             }
//             Some(merkle_hash) => {
//                 let merkle = self.store.hash_lookup_generic(merkle_hash.clone()).await?;
//                 Ok((merkle.value, Arc::new(LatStoreImmutCtx {
//                     store: self.store.clone(),
//                     deps: Arc::new(merkle.deps),
//                 })))
//             }
//         }
//     }
// 
//     async fn eval_lat_computation(&self, key: &LC::Key) -> Res<(LC::Value, Arc<dyn LatticeImmutContext<C, L, LC>>)> {
//         match self.deps.lat_comp_deps.get(key) {
//             None => bail!("lattice computation dependency not found"),
//             Some(merkle_hash) => {
//                 let merkle = self.store.hash_lookup_generic(merkle_hash.clone()).await?;
//                 Ok((merkle.value, Arc::new(LatStoreImmutCtx {
//                     store: self.store.clone(),
//                     deps: Arc::new(merkle.deps),
//                 })))
//             }
//         }
//     }
// }
// 

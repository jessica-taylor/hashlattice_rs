use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex, MutexGuard};
use std::marker::PhantomData;


use core::fmt::{Debug};

use futures::Future;
use anyhow::bail;
use async_trait::async_trait;
use async_recursion::async_recursion;

use crate::error::Res;
use crate::crypto::{HashCode, hash_of_bytes, Hash};
use crate::tagged_mapping::TaggedMapping;
use crate::lattice::{HashLookup, hash_lookup_generic, hash_put_generic, LatticeLibrary, ComputationLibrary, ComputationImmutContext, HashPut, LatticeImmutContext, LatticeMutContext, LatMerkleDeps, LatMerkleNode};
use serde::{Serialize, Deserialize};

/// a key-value store with key-key dependencies; auto-removes unpinned, non-depended-on keys
pub trait DepDB<M: TaggedMapping> : Send {

    fn has_value(&self, key: &M::Key) -> Res<bool>;

    fn get_value(&self, key: &M::Key) -> Res<Option<M::Value>>;

    fn set_value_deps(&mut self, key: M::Key, value: M::Value, deps: Vec<M::Key>) -> Res<()>;

    fn is_pinned(&self, key: &M::Key) -> Res<bool>;

    fn set_pin(&mut self, key: &M::Key, pin: bool) -> Res<()>;

    fn clear_value_deps(&mut self, key: &M::Key) -> Res<()>;

    fn clear_dead(&mut self) -> Res<()>;

    fn is_dirty(&self, key: &M::Key) -> Res<bool>;

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
    computation: PhantomData<C>,
    lat: PhantomData<L>,
    lat_comp: PhantomData<LC>,
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
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static, Ctx: HashPut> HashPut for LatDepsTracker<C, L, LC, Ctx> {
    async fn hash_put(self: Arc<Self>, data: Vec<u8>) -> Res<HashCode> {
        let hash = self.ctx.clone().hash_put(data).await?;
        self.deps.lock().unwrap().hash_deps.insert(hash.clone());
        Ok(hash)
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static, Ctx: ComputationImmutContext<C>> ComputationImmutContext<C> for LatDepsTracker<C, L, LC, Ctx> {
    async fn eval_computation(self: Arc<Self>, key: &C::Key) -> Res<C::Value> {
        self.deps.lock().unwrap().comp_deps.insert(key.clone());
        self.ctx.clone().eval_computation(key).await
    }
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static, Ctx: LatticeMutContext<C, L, LC> + 'static> LatticeMutContext<C, L, LC> for LatDepsTracker<C, L, LC, Ctx> {}

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
    extra_hashlookup: Arc<dyn HashLookup>,
    extra_hashlookup_cache: Arc<Mutex<BTreeMap<HashCode, Vec<u8>>>>,
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> Clone for LatStore<C, L, LC> {
    fn clone(&self) -> Self {
        LatStore {
            db: self.db.clone(),
            comp_lib: self.comp_lib.clone(),
            lat_lib: self.lat_lib.clone(),
            extra_hashlookup: self.extra_hashlookup.clone(),
            extra_hashlookup_cache: self.extra_hashlookup_cache.clone(),
        }
    }
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatStore<C, L, LC> {
    pub fn new(db: impl DepDB<LatDBMapping<C, L, LC>> + 'static,
               comp_lib: Arc<impl ComputationLibrary<C> + 'static>,
               lat_lib: Arc<impl LatticeLibrary<C, L, LC> + 'static>,
               extra_hashlookup: Arc<impl HashLookup + 'static>) -> Self {
        Self {
            db: Arc::new(Mutex::new(db)),
            comp_lib: comp_lib,
            lat_lib: lat_lib,
            extra_hashlookup: extra_hashlookup,
            extra_hashlookup_cache: Arc::new(Mutex::new(BTreeMap::new())),
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

    async fn transport_dirty_lat(self: &Arc<Self>, key: &L::Key) -> Res<()> {
        debug_assert!(self.get_db().is_dirty(&LatDBKey::Lattice(key.clone())).unwrap());
        let db_key = LatDBKey::Lattice(key.clone());
        let merkle_hash = match self.get_db().get_value(&db_key)? {
            Some(LatDBValue::Lattice(merkle_hash)) => merkle_hash,
            _ => bail!("Lattice key {:?} has no merkle hash", key),
        };
        let merkle = hash_lookup_generic(&self, merkle_hash).await?;
        let old_ctx = Arc::new(LatStoreDepsCtx::new(self.clone(), merkle.deps));
        let opt_tr_value = self.lat_lib.clone().transport(&key, &merkle.value, old_ctx, self.clone()).await?;
        match opt_tr_value {
            None => {
                self.get_db().clear_value_deps(&db_key)?;
            }
            Some(tr_value) => {
                let tr_value2 = tr_value.clone();
                let lat_lib = self.lat_lib.clone();
                let ((), tr_deps) = LatDepsTracker::with_get_deps(self, move |this| async move {
                    lat_lib.check_elem(&key, &tr_value2, this).await
                }).await?;
                let merkle_hash = hash_put_generic(self, &LatMerkleNode {
                    value: tr_value,
                    deps: tr_deps.to_merkle_deps(),
                }).await?;
                self.get_db().set_value_deps(db_key, LatDBValue::Lattice(merkle_hash), tr_deps.to_keys())?;
            }
        }
        Ok(())
    }

    async fn update_dirty(self: Arc<Self>) -> Res<()> {
        loop {
            let dirty = self.get_db().get_dirty()?;
            if dirty.is_empty() {
                return Ok(());
            }
            for key in dirty {
                match &key {
                    LatDBKey::Computation(_comp_key) => {
                        self.get_db().clear_value_deps(&key)?;
                    }
                    LatDBKey::Lattice(lat_key) => {
                        self.transport_dirty_lat(lat_key).await?;
                    }
                    LatDBKey::LatComputation(_lat_comp_key) => {
                        self.get_db().clear_value_deps(&key)?;
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
        {
            let cache = self.extra_hashlookup_cache.lock().unwrap();
            if let Some(value) = cache.get(&hash) {
                return Ok(value.clone());
            }
        }
        let res = self.get_db().get_value(&LatDBKey::Hash(hash))?;
        match res {
            Some(LatDBValue::Hash(bytes)) => Ok(bytes),
            _ => {
                let other_bs = self.extra_hashlookup.clone().hash_lookup(hash).await?;
                if hash_of_bytes(&other_bs) == hash {
                    self.extra_hashlookup_cache.lock().unwrap().insert(hash, other_bs.clone());
                    Ok(other_bs)
                } else {
                    bail!("hash lookup failed")
                }
            }
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
        if self.get_db().is_dirty(&computation_key)? {
            self.get_db().clear_value_deps(&computation_key)?;
        }
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
        let db_key = LatDBKey::Lattice(key.clone());
        if self.get_db().is_dirty(&db_key)? {
            self.transport_dirty_lat(key).await?;
        }
        let db_value = self.get_db().get_value(&db_key)?;
        match db_value {
            Some(LatDBValue::Lattice(merkle_hash)) => Ok(Some(merkle_hash)),
            None => Ok(None),
            _ => bail!("Lattice key has no lattice value"),
        }
    }

    async fn eval_lat_computation(self: Arc<Self>, key: &LC::Key) -> Res<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, LC::Value>>> {
        let lat_comp_key = LatDBKey::LatComputation(key.clone());
        if self.get_db().is_dirty(&lat_comp_key)? {
            self.get_db().clear_value_deps(&lat_comp_key)?;
        }
        let db_value = self.get_db().get_value(&lat_comp_key)?;
        if let Some(LatDBValue::LatComputation(merkle_hash)) = db_value {
            return Ok(merkle_hash);
        }
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
        self.get_db().set_value_deps(lat_comp_key, LatDBValue::LatComputation(merkle_hash), deps.to_keys())?;
        Ok(merkle_hash)
    }
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeMutContext<C, L, LC> for LatStore<C, L, LC> {}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatStore<C, L, LC> {

    #[async_recursion]
    async fn join_deps(self: &Arc<Self>, deps: &LatMerkleDeps<L::Key, L::Value, LC::Key, LC::Value>, other_ctx: Arc<LatStoreDepsCtx<C, L, LC>>) -> Res<()> {
        for (lat_key, lat_merkle_hash) in &deps.lat_deps {
            self.clone().lattice_join_rec(lat_key, *lat_merkle_hash, other_ctx.clone()).await?;
        }
        for (lat_comp_key, lat_comp_merkle_hash) in &deps.lat_comp_deps {
            let db_key = LatDBKey::LatComputation(lat_comp_key.clone());
            let db_value = self.get_db().get_value(&db_key)?;
            match db_value {
                Some(LatDBValue::LatComputation(store_merkle_hash)) => {
                    if !self.get_db().is_dirty(&db_key)? && store_merkle_hash == *lat_comp_merkle_hash {
                        continue;
                    }
                }
                _ => {}
            }
            let lat_comp_merkle = hash_lookup_generic(&self, *lat_comp_merkle_hash).await?;
            self.clone().join_deps(&lat_comp_merkle.deps, other_ctx.clone()).await?;
        }
        Ok(())
    }

    pub async fn lattice_join(self: &Arc<Self>, key: &L::Key, other_merkle_hash: Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>> {
        let mut lat_deps = BTreeMap::new();
        lat_deps.insert(key.clone(), other_merkle_hash);
        let other_ctx = Arc::new(LatStoreDepsCtx::new(self.clone(), LatMerkleDeps {
            lat_deps,
            lat_comp_deps: BTreeMap::new(),
        }));
        other_ctx.clone().lattice_lookup(key).await?;
        self.lattice_join_rec(key, other_merkle_hash, other_ctx).await
    }

    async fn lattice_join_rec(self: &Arc<Self>, key: &L::Key, other_merkle_hash: Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>, other_ctx: Arc<LatStoreDepsCtx<C, L, LC>>) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>> {
        let store_merkle_hash = self.clone().lattice_lookup(key).await?;
        if store_merkle_hash == Some(other_merkle_hash) {
            return Ok(store_merkle_hash);
        }
        let other_merkle = hash_lookup_generic(&self, other_merkle_hash).await?;
        self.join_deps(&other_merkle.deps, other_ctx.clone()).await?;
        let tr_other = self.lat_lib.clone().transport(key, &other_merkle.value, other_ctx, self.clone()).await?;
        let store_merkle_hash = self.clone().lattice_lookup(key).await?;
        if tr_other.is_none() {
            return Ok(store_merkle_hash);
        }
        let tr_other = tr_other.unwrap();
        let joined = match store_merkle_hash {
            None => tr_other,
            Some(store_merkle_hash) => {
                let store_merkle = hash_lookup_generic(&self, store_merkle_hash).await?;
                if tr_other == store_merkle.value {
                    return Ok(Some(store_merkle_hash));
                }
                let joined = self.lat_lib.clone().join(key, &store_merkle.value, &tr_other, self.clone()).await?;
                if joined.is_none() {
                    // this probably shouldn't happen...
                    return Ok(Some(store_merkle_hash));
                }
                joined.unwrap()
            }
        };
        let lat_lib = self.lat_lib.clone();
        let (joined, joined_deps) = LatDepsTracker::<C, L, LC, _>::with_get_deps(&self, move |this| async move {
            lat_lib.check_elem(&key, &joined, this).await?;
            Ok(joined)
        }).await?;
        let merkle = LatMerkleNode {
            value: joined,
            deps: joined_deps.to_merkle_deps()
        };
        let merkle_hash = hash_put_generic(&self, &merkle).await?;
        if Some(merkle_hash) != store_merkle_hash {
            self.get_db().set_value_deps(LatDBKey::Lattice(key.clone()), LatDBValue::Lattice(merkle_hash), joined_deps.to_keys())?;
        }
        Ok(Some(merkle_hash))
    }

    pub async fn lattice_join_elem(self: &Arc<Self>, key: &L::Key, value: L::Value) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>> {
        let lat_lib = self.lat_lib.clone();
        let (value, deps) = LatDepsTracker::<C, L, LC, _>::with_get_deps(&self, move |this| async move {
            lat_lib.check_elem(&key, &value, this).await?;
            Ok(value)
        }).await?;
        let merkle = LatMerkleNode {
            value: value,
            deps: deps.to_merkle_deps()
        };
        let merkle_hash = hash_put_generic(&self, &merkle).await?;
        self.lattice_join(key, merkle_hash).await
    }
}

pub struct LatStoreDepsCtx<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> {
    store: Arc<LatStore<C, L, LC>>,
    other_deps: Arc<Mutex<LatMerkleDeps<L::Key, L::Value, LC::Key, LC::Value>>>,
    lat_cache: Arc<Mutex<BTreeMap<L::Key, Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>>>>,
    lat_comp_cache: Arc<Mutex<BTreeMap<LC::Key, Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, LC::Value>>>>>,
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatStoreDepsCtx<C, L, LC> {
    fn new(store: Arc<LatStore<C, L, LC>>, other_deps: LatMerkleDeps<L::Key, L::Value, LC::Key, LC::Value>) -> Self {
        Self {
            store,
            other_deps: Arc::new(Mutex::new(other_deps)),
            lat_cache: Arc::new(Mutex::new(BTreeMap::new())),
            lat_comp_cache: Arc::new(Mutex::new(BTreeMap::new())),
        }
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> HashLookup for LatStoreDepsCtx<C, L, LC> {
    async fn hash_lookup(self: Arc<Self>, hash: HashCode) -> Res<Vec<u8>> {
        self.store.clone().hash_lookup(hash).await
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> HashPut for LatStoreDepsCtx<C, L, LC> {
    async fn hash_put(self: Arc<Self>, value: Vec<u8>) -> Res<HashCode> {
        self.store.clone().hash_put(value).await
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> ComputationImmutContext<C> for LatStoreDepsCtx<C, L, LC> {
    async fn eval_computation(self: Arc<Self>, key: &C::Key) -> Res<C::Value> {
        self.store.clone().eval_computation(key).await
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeImmutContext<C, L, LC> for LatStoreDepsCtx<C, L, LC> {
    async fn lattice_lookup(self: Arc<Self>, key: &L::Key) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>> {
        {
            let cache = self.lat_cache.lock().unwrap();
            if let Some(res) = cache.get(key) {
                return Ok(res.clone());
            }
        }
        let other_merkle_hash = self.other_deps.lock().unwrap().lat_deps.get(key).cloned();
        if other_merkle_hash.is_none() {
            return Ok(None);
        }
        let other_merkle = hash_lookup_generic(&self.store, other_merkle_hash.unwrap()).await?;
        self.other_deps.lock().unwrap().try_union(other_merkle.deps)?;
        self.lat_cache.lock().unwrap().insert(key.clone(), Some(other_merkle_hash.unwrap()));
        Ok(other_merkle_hash)
    }

    async fn eval_lat_computation(self: Arc<Self>, key: &LC::Key) -> Res<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, LC::Value>>> {
        {
            let cache = self.lat_comp_cache.lock().unwrap();
            if let Some(res) = cache.get(key) {
                return Ok(res.clone());
            }
        }
        let other_merkle_hash = self.other_deps.lock().unwrap().lat_comp_deps.get(key).cloned();
        {
            let db_key = LatDBKey::LatComputation(key.clone());
            let db_value = self.store.get_db().get_value(&db_key)?;
            if let Some(LatDBValue::LatComputation(store_merkle_hash)) = db_value {
                if !self.store.get_db().is_dirty(&db_key)? && Some(store_merkle_hash) == other_merkle_hash {
                    self.lat_comp_cache.lock().unwrap().insert(key.clone(), store_merkle_hash);
                    return Ok(store_merkle_hash);
                }
            }
        }
        if other_merkle_hash.is_none() {
            bail!("lattice computation used unexpected dependency");
        }
        let other_merkle = hash_lookup_generic(&self.store, other_merkle_hash.unwrap()).await?;
        self.other_deps.lock().unwrap().try_union(other_merkle.deps)?;
        let lat_lib = self.store.lat_lib.clone();
        let (value, deps) = LatDepsTracker::<C, L, LC, _>::with_get_deps(&self, move |this| async move {
            lat_lib.eval_lat_computation(&key, this).await
        }).await?;
        let merkle = LatMerkleNode {value, deps: deps.to_merkle_deps()};
        let merkle_hash = hash_put_generic(&self.store, &merkle).await?;
        // merkle_hash can differ from other_merkle_hash due to store containing extra hashes!
        self.lat_comp_cache.lock().unwrap().insert(key.clone(), merkle_hash);
        Ok(merkle_hash)
    }
}

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeMutContext<C, L, LC> for LatStoreDepsCtx<C, L, LC> {}

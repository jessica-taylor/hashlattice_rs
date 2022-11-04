
use std::collections::BTreeMap;
use std::sync::Arc;
use anyhow::bail;
use async_trait::async_trait;
use core::pin::Pin;

use serde::{Serialize, Deserialize, de::DeserializeOwned};

use crate::error::Res;
use crate::crypto::{HashCode, Hash};
use crate::tagged_mapping::{TaggedMapping};


#[async_trait]
pub trait HashLookup : Send + Sync {

    async fn hash_lookup(self: Arc<Self>, hash: HashCode) -> Res<Vec<u8>> {
        bail!("hash_lookup not implemented")
    }
}

pub async fn hash_lookup_generic<H: HashLookup + ?Sized, T: DeserializeOwned>(hl: &Arc<H>, hsh: Hash<T>) -> Res<T> {
    let bs = hl.clone().hash_lookup(hsh.code).await?;
    Ok(rmp_serde::from_slice(&bs)?)
}

pub async fn hash_put_generic<H: HashPut + ?Sized, T: Serialize>(hp: &Arc<H>, value: &T) -> Res<Hash<T>> {
    let bs = rmp_serde::to_vec(value)?;
    Ok(Hash::from_hashcode(hp.clone().hash_put(bs).await?))
}

#[async_trait]
pub trait HashPut : HashLookup + Send + Sync {

    async fn hash_put(self: Arc<Self>, value: Vec<u8>) -> Res<HashCode> {
        bail!("hash_put not implemented")
    }

}

#[async_trait]
pub trait ComputationImmutContext<C: TaggedMapping> : HashLookup + Send + Sync {

    async fn eval_computation(self: Arc<Self>, key: &C::Key) -> Res<C::Value> {
        bail!("eval_computation not implemented")
    }
}


#[async_trait]
pub trait ComputationLibrary<C: TaggedMapping + 'static> : Send + Sync {

    async fn eval_computation(self: Arc<Self>, key: &C::Key, ctx: Arc<dyn ComputationImmutContext<C>>) -> Res<C::Value> {
        bail!("eval_computation not implemented")
    }
}


#[async_trait]
pub trait LatticeLibrary<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> : Send + Sync {

    async fn check_elem(self: Arc<Self>, key: &L::Key, value: &L::Value, ctx: Arc<dyn LatticeImmutContext<C, L, LC>>) -> Res<()> {
        bail!("check_elem not implemented")
    }

    async fn join(self: Arc<Self>, key: &L::Key, a: &L::Value, b: &L::Value, ctx: Arc<dyn LatticeMutContext<C, L, LC>>) -> Res<Option<L::Value>> {
        bail!("join not implemented")
    }

    async fn transport(self: Arc<Self>, key: &L::Key, value: &L::Value, old_ctx: Arc<dyn LatticeImmutContext<C, L, LC>>, new_ctx: Arc<dyn LatticeMutContext<C, L, LC>>) -> Res<Option<L::Value>> {
        Ok(Some(value.clone()))
    }

    async fn eval_lat_computation(self: Arc<Self>, key: &LC::Key, ctx: Arc<dyn LatticeImmutContext<C, L, LC>>) -> Res<LC::Value> {
        bail!("eval_lat_computation not implemented")
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub struct LatMerkleDeps<LK: Ord, LV, LCK: Ord, LCV> {
    pub lat_deps: BTreeMap<LK, Hash<LatMerkleNode<LK, LV, LCK, LCV, LV>>>,
    pub lat_comp_deps: BTreeMap<LCK, Hash<LatMerkleNode<LK, LV, LCK, LCV, LCV>>>,
}

impl<LK: Ord, LV, LCK: Ord, LCV> LatMerkleDeps<LK, LV, LCK, LCV> {
    pub fn new() -> Self {
        LatMerkleDeps {
            lat_deps: BTreeMap::new(),
            lat_comp_deps: BTreeMap::new(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.lat_deps.is_empty() && self.lat_comp_deps.is_empty()
    }
    pub fn try_union(&mut self, other: Self) -> Res<()> {
        for (k, v) in other.lat_deps {
            if let Some(v2) = self.lat_deps.get(&k) {
                if v != *v2 {
                    bail!("lat_deps conflict")
                }
            } else {
                self.lat_deps.insert(k, v);
            }
        }
        for (k, v) in other.lat_comp_deps {
            if let Some(v2) = self.lat_comp_deps.get(&k) {
                if v != *v2 {
                    bail!("lat_comp_deps conflict")
                }
            } else {
                self.lat_comp_deps.insert(k, v);
            }
        }
        Ok(())
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
pub struct LatMerkleNode<LK: Ord, LV, LCK: Ord, LCV, V> {
    pub value: V,
    pub deps: LatMerkleDeps<LK, LV, LCK, LCV>,
}


#[async_trait]
pub trait LatticeImmutContext<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> : ComputationImmutContext<C> {

    async fn lattice_lookup(self: Arc<Self>, key: &L::Key) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>>;

    async fn eval_lat_computation(self: Arc<Self>, key: &LC::Key) -> Res<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, LC::Value>>>;

}

pub trait AsLatticeImmutContext<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> : LatticeImmutContext<C, L, LC> {
    fn as_lattice_immut_ctx(self: Arc<Self>) -> Arc<dyn LatticeImmutContext<C, L, LC>>;
}

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping, T: 'static + LatticeImmutContext<C, L, LC>> AsLatticeImmutContext<C, L, LC> for T {
    fn as_lattice_immut_ctx(self: Arc<Self>) -> Arc<dyn LatticeImmutContext<C, L, LC>> {
        self
    }
}

#[async_trait]
pub trait LatticeMutContext<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping>: HashPut + LatticeImmutContext<C, L, LC> + AsLatticeImmutContext<C, L, LC> {

}


#[derive(Clone)]
pub struct EmptyComputationLibrary;

impl<C: TaggedMapping + 'static> ComputationLibrary<C> for EmptyComputationLibrary {}

#[derive(Clone)]
pub struct EmptyLatticeLibrary;

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeLibrary<C, L, LC> for EmptyLatticeLibrary {}

#[derive(Clone)]
pub struct EmptyContext;

#[async_trait]
impl HashLookup for EmptyContext {
    async fn hash_lookup(self: Arc<Self>, hash: HashCode) -> Res<Vec<u8>> {
        bail!("EmptyHashLookup: no hash lookup for {:?}", hash)
    }
}

#[async_trait]
impl HashPut for EmptyContext {
    async fn hash_put(self: Arc<Self>, value: Vec<u8>) -> Res<HashCode> {
        bail!("EmptyComputationMutContext: no hash put for {:?}", value)
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static> ComputationImmutContext<C> for EmptyContext {
    async fn eval_computation(self: Arc<Self>, key: &C::Key) -> Res<C::Value> {
        bail!("EmptyComputationImmutContext: no computation for {:?}", key)
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeImmutContext<C, L, LC> for EmptyContext {

    async fn lattice_lookup(self: Arc<Self>, key: &L::Key) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, L::Value>>>> {
        bail!("EmptyLatticeImmutContext: no lattice lookup for {:?}", key)
    }

    async fn eval_lat_computation(self: Arc<Self>, key: &LC::Key) -> Res<Hash<LatMerkleNode<L::Key, L::Value, LC::Key, LC::Value, LC::Value>>> {
        bail!("EmptyLatticeImmutContext: no lattice computation for {:?}", key)
    }

}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeMutContext<C, L, LC> for EmptyContext {
}

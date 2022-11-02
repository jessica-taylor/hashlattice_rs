
use std::sync::Arc;
use anyhow::bail;
use async_trait::async_trait;

use crate::error::Res;
use crate::crypto::HashCode;
use crate::tagged_mapping::{TaggedMapping};

#[async_trait]
pub trait HashLookup : Send + Sync {

    async fn hash_lookup(self: Arc<Self>, hash: HashCode) -> Res<Vec<u8>> {
        bail!("hash_lookup not implemented")
    }
}

#[async_trait]
pub trait ComputationImmutContext<C: TaggedMapping> : HashLookup {

    async fn eval_computation(self: Arc<Self>, key: &C::Key) -> Res<C::Value> {
        bail!("eval_computation not implemented")
    }
}

#[async_trait]
pub trait ComputationMutContext<C: TaggedMapping> : ComputationImmutContext<C> {

    async fn hash_put(self: Arc<Self>, value: Vec<u8>) -> Res<HashCode> {
        bail!("hash_put not implemented")
    }

}

#[async_trait]
pub trait ComputationLibrary<C: TaggedMapping + 'static> : Send + Sync {

    async fn eval_computation(&self, key: &C::Key, ctx: Arc<dyn ComputationImmutContext<C>>) -> Res<C::Value> {
        bail!("eval_computation not implemented")
    }
}


#[async_trait]
pub trait LatticeLibrary<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> : Send + Sync {

    async fn check_elem(&self, key: &L::Key, value: &L::Value, ctx: Arc<dyn LatticeImmutContext<C, L, LC>>) -> Res<()> {
        bail!("check_elem not implemented")
    }

    async fn join(&self, key: &L::Key, a: &L::Value, b: &L::Value, ctx: Arc<dyn LatticeMutContext<C, L, LC>>) -> Res<L::Value> {
        bail!("join not implemented")
    }

    async fn bottom(&self, key: &L::Key) -> Res<L::Value> {
        bail!("bottom not implemented")
    }

    async fn transport(&self, key: &L::Key, value: &L::Value, old_ctx: Arc<dyn LatticeImmutContext<C, L, LC>>, new_ctx: Arc<dyn LatticeMutContext<C, L, LC>>) -> Res<L::Value> {
        Ok(value.clone())
    }

    async fn eval_lat_computation(&self, key: &LC::Key, ctx: Arc<dyn LatticeImmutContext<C, L, LC>>) -> Res<LC::Value> {
        bail!("eval_lat_computation not implemented")
    }
}

#[async_trait]
pub trait LatticeImmutContext<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> : ComputationImmutContext<C> {

    async fn lattice_lookup(self: Arc<Self>, key: &L::Key) -> Res<(L::Value, Arc<dyn LatticeImmutContext<C, L, LC>>)>;

    async fn eval_lat_computation(self: Arc<Self>, key: &LC::Key) -> Res<(LC::Value, Arc<dyn LatticeImmutContext<C, L, LC>>)>;

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
pub trait LatticeMutContext<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping>: ComputationMutContext<C> + LatticeImmutContext<C, L, LC> + AsLatticeImmutContext<C, L, LC> {

    async fn lattice_join(self: Arc<Self>, key: &L::Key, value: &L::Value, ctx_other: Arc<dyn LatticeImmutContext<C, L, LC>>) -> Res<L::Value>;

}


pub struct EmptyComputationLibrary;

impl<C: TaggedMapping + 'static> ComputationLibrary<C> for EmptyComputationLibrary {}

pub struct EmptyLatticeLibrary;

impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeLibrary<C, L, LC> for EmptyLatticeLibrary {}

pub struct EmptyContext;

#[async_trait]
impl HashLookup for EmptyContext {
    async fn hash_lookup(self: Arc<Self>, hash: HashCode) -> Res<Vec<u8>> {
        bail!("EmptyHashLookup: no hash lookup for {:?}", hash)
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static> ComputationImmutContext<C> for EmptyContext {
    async fn eval_computation(self: Arc<Self>, key: &C::Key) -> Res<C::Value> {
        bail!("EmptyComputationImmutContext: no computation for {:?}", key)
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static> ComputationMutContext<C> for EmptyContext {
    async fn hash_put(self: Arc<Self>, value: Vec<u8>) -> Res<HashCode> {
        bail!("EmptyComputationMutContext: no hash put for {:?}", value)
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeImmutContext<C, L, LC> for EmptyContext {

    async fn lattice_lookup(self: Arc<Self>, key: &L::Key) -> Res<(L::Value, Arc<dyn LatticeImmutContext<C, L, LC>>)> {
        bail!("EmptyLatticeImmutContext: no lattice lookup for {:?}", key)
    }

    async fn eval_lat_computation(self: Arc<Self>, key: &LC::Key) -> Res<(LC::Value, Arc<dyn LatticeImmutContext<C, L, LC>>)> {
        bail!("EmptyLatticeImmutContext: no lattice computation for {:?}", key)
    }
}

#[async_trait]
impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static> LatticeMutContext<C, L, LC> for EmptyContext {
    async fn lattice_join(self: Arc<Self>, key: &L::Key, value: &L::Value, ctx_other: Arc<dyn LatticeImmutContext<C, L, LC>>) -> Res<L::Value> {
        bail!("EmptyLatticeMutContext: no lattice join for {:?} {:?}", key, value)
    }
}

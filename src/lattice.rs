
use std::sync::{Arc, Mutex};

use crate::error::{str_error, Res};
use crate::crypto::HashCode;
use crate::tagged_mapping::{TaggedMapping};

pub trait HashLookup : Send + Sync {

    fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>> {
        str_error("hash_lookup not implemented")
    }
}

pub trait ComputationImmutContext<C: TaggedMapping> : HashLookup {

    fn eval_computation(&self, key: &C::Key) -> Res<C::Value> {
        str_error("eval_computation not implemented")
    }
}

pub trait ComputationMutContext<C: TaggedMapping> : ComputationImmutContext<C> {

    fn hash_put(&self, value: Vec<u8>) -> Res<HashCode> {
        str_error("hash_put not implemented")
    }

}

pub trait ComputationLibrary<C: TaggedMapping> : Send + Sync {

    fn eval_computation(&self, key: &C::Key, ctx: &dyn ComputationImmutContext<C>) -> Res<C::Value> {
        str_error("eval_computation not implemented")
    }
}


pub trait LatticeLibrary<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> : Send + Sync {

    fn check_elem(&self, key: &L::Key, value: &L::Value, ctx: &dyn LatticeImmutContext<C, L, LC>) -> Res<()> {
        str_error("check_elem not implemented")
    }

    fn join(&self, key: &L::Key, a: &L::Value, b: &L::Value, ctx: &dyn LatticeMutContext<C, L, LC>) -> Res<L::Value> {
        str_error("join not implemented")
    }

    fn bottom(&self, key: &L::Key) -> Res<L::Value> {
        str_error("bottom not implemented")
    }

    fn transport(&self, key: &L::Key, value: &L::Value, old_ctx: &dyn LatticeImmutContext<C, L, LC>, new_ctx: &dyn LatticeMutContext<C, L, LC>) -> Res<L::Value> {
        Ok(value.clone())
    }

    fn eval_lat_computation(&self, key: &LC::Key, ctx: &dyn LatticeImmutContext<C, L, LC>) -> Res<LC::Value> {
        str_error("eval_lat_computation not implemented")
    }
}

pub trait LatticeImmutContext<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> : ComputationImmutContext<C> {

    fn lattice_lookup<'a>(&'a self, key: &L::Key) -> Res<(L::Value, Box<dyn 'a + LatticeImmutContext<C, L, LC>>)>;

    fn eval_lat_computation<'a>(&'a self, key: &LC::Key) -> Res<(LC::Value, Box<dyn 'a + LatticeImmutContext<C, L, LC>>)>;

}

pub trait LatticeMutContext<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping>: ComputationMutContext<C> + LatticeImmutContext<C, L, LC> {

    fn lattice_join(&self, key: &L::Key, value: &L::Value, ctx_other: &dyn LatticeImmutContext<C, L, LC>) -> Res<L::Value>;

}

pub struct EmptyComputationLibrary;

impl<C: TaggedMapping> ComputationLibrary<C> for EmptyComputationLibrary {}

pub struct EmptyLatticeLibrary;

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> LatticeLibrary<C, L, LC> for EmptyLatticeLibrary {}

pub struct EmptyContext;

impl HashLookup for EmptyContext {
    fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>> {
        str_error(&format!("EmptyHashLookup: no hash lookup for {:?}", hash))
    }
}

impl<C: TaggedMapping> ComputationImmutContext<C> for EmptyContext {
    fn eval_computation(&self, key: &C::Key) -> Res<C::Value> {
        str_error(&format!("EmptyComputationImmutContext: no computation for {:?}", key))
    }
}

impl<C: TaggedMapping> ComputationMutContext<C> for EmptyContext {
    fn hash_put(&self, value: Vec<u8>) -> Res<HashCode> {
        str_error(&format!("EmptyComputationMutContext: no hash put for {:?}", value))
    }
}

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> LatticeImmutContext<C, L, LC> for EmptyContext {

    fn lattice_lookup<'a>(&'a self, key: &L::Key) -> Res<(L::Value, Box<dyn 'a + LatticeImmutContext<C, L, LC>>)> {
        str_error(&format!("EmptyLatticeImmutContext: no lattice lookup for {:?}", key))
    }

    fn eval_lat_computation<'a>(&'a self, key: &LC::Key) -> Res<(LC::Value, Box<dyn 'a + LatticeImmutContext<C, L, LC>>)> {
        str_error(&format!("EmptyLatticeImmutContext: no lattice computation for {:?}", key))
    }
}

impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> LatticeMutContext<C, L, LC> for EmptyContext {
    fn lattice_join(&self, key: &L::Key, value: &L::Value, ctx_other: &dyn LatticeImmutContext<C, L, LC>) -> Res<L::Value> {
        str_error(&format!("EmptyLatticeMutContext: no lattice join for {:?} {:?}", key, value))
    }
}

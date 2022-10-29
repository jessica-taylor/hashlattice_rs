
use std::sync::{Arc, Mutex};

use crate::error::{str_error, Res};
use crate::crypto::HashCode;
use crate::tagged_mapping::{TaggedMapping};

pub trait HashLookup : Send + Sync {

    fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>>;
}

pub struct EmptyHashLookup;

impl HashLookup for EmptyHashLookup {
    fn hash_lookup(&self, hash: HashCode) -> Res<Vec<u8>> {
        str_error(&format!("EmptyHashLookup: no hash lookup for {:?}", hash))
    }
}

pub trait ComputationImmutContext<C: TaggedMapping> : HashLookup {

    fn eval_computation(&self, key: &C::Key) -> Res<C::Value>;
}

pub trait ComputationMutContext<C: TaggedMapping> : ComputationImmutContext<C> {

    fn hash_put(&self, value: Vec<u8>) -> Res<HashCode>;

}

pub trait ComputationLibrary<C: TaggedMapping> : Send + Sync {

    fn eval_computation(&self, key: &C::Key, ctx: &dyn ComputationImmutContext<C>) -> Res<C::Value>;
}

pub struct EmptyComputationLibrary;

impl<C: TaggedMapping> ComputationLibrary<C> for EmptyComputationLibrary {
    fn eval_computation(&self, key: &C::Key, ctx: &dyn ComputationImmutContext<C>) -> Res<C::Value> {
        str_error(&format!("EmptyComputationLibrary: no computation for {:?}", key))
    }
}

pub trait LatticeLibrary<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> : Send + Sync {

    fn check_elem(&self, key: &L::Key, value: &L::Value, ctx: &dyn LatticeImmutContext<C, L, LC>) -> Res<()>;

    fn join(&self, key: &L::Key, a: &L::Value, b: &L::Value, ctx: &dyn LatticeMutContext<C, L, LC>) -> Res<L::Value>;

    fn bottom(&self, key: &L::Key, ctx: &dyn ComputationMutContext<C>) -> Res<L::Value>;

    fn transport(&self, key: &L::Key, value: &L::Value, old_ctx: &dyn LatticeImmutContext<C, L, LC>, new_ctx: &dyn LatticeMutContext<C, L, LC>) -> Res<L::Value> {
        Ok(value.clone())
    }

    fn eval_lat_computation(&self, key: &LC::Key, ctx: &dyn LatticeImmutContext<C, L, LC>) -> Res<LC::Value>;
}

// pub struct EmptyLatticeLibrary;
// 
// impl<C: TaggedMapping, L: TaggedMapping> LatticeLibrary<C, L> for EmptyLatticeLibrary {
//     fn check_elem(&self, key: &L::Key, value: &L::Value, ctx: &mut dyn LatticeImmutContext<C>) -> Res<()> {
//         str_error(&format!("EmptyLatticeLibrary: no check_elem for {:?} {:?}", key, value))
//     }
// 
//     fn join(&self, key: &L::Key, a: &L::Value, b: &L::Value, ctxa: &mut dyn LatticeImmutContext<C>, ctxb: &mut dyn LatticeImmutContext<C>) -> Res<L::Value> {
//         str_error(&format!("EmptyLatticeLibrary: no join for {:?} {:?} {:?}", key, a, b))
//     }
// }

pub trait LatticeImmutContext<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping> : ComputationImmutContext<C> {

    fn lattice_lookup<'a>(&'a self, key: &L::Key) -> Res<(L::Value, Box<dyn 'a + LatticeImmutContext<C, L, LC>>)>;

    fn eval_lat_computation<'a>(&'a self, key: &LC::Key) -> Res<(LC::Value, Box<dyn 'a + LatticeImmutContext<C, L, LC>>)>;

}

pub trait LatticeMutContext<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping>: ComputationMutContext<C> + LatticeImmutContext<C, L, LC> {

    fn lattice_join(&self, key: &L::Key, value: &L::Value, ctx_other: &mut dyn LatticeImmutContext<C, L, LC>) -> Res<L::Value>;

    fn lattice_bottom(&self, key: &L::Key) -> Res<L::Value>;

}

// impl<T: HashLookup> HashLookup for Arc<Mutex<T>> {
//     fn hash_lookup(&mut self, hash: HashCode) -> Res<Vec<u8>> {
//         self.lock().unwrap().hash_lookup(hash)
//     }
// }
// 
// impl<C: TaggedMapping, T: ComputationImmutContext<C>> ComputationImmutContext<C> for Arc<Mutex<T>> {
//     fn eval_computation(&mut self, key: &C::Key) -> Res<C::Value> {
//         self.lock().unwrap().eval_computation(key)
//     }
// }
// 
// impl<C: TaggedMapping, T: ComputationMutContext<C>> ComputationMutContext<C> for Arc<Mutex<T>> {
//     fn hash_put(&mut self, value: Vec<u8>) -> Res<HashCode> {
//         self.lock().unwrap().hash_put(value)
//     }
// }
// 
// impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping, T: LatticeImmutContext<C, L, LC>> LatticeImmutContext<C, L, LC> for Arc<Mutex<T>> {
//     fn lattice_lookup<'a>(&'a self, key: &L::Key) -> Res<(L::Value, Box<dyn 'a + LatticeImmutContext<C, L, LC>>)> {
//         self.lock().unwrap().lattice_lookup(key)
//     }
// 
//     fn eval_lat_computation<'a>(&'a self, key: &LC::Key) -> Res<(LC::Value, Box<dyn 'a + LatticeImmutContext<C, L, LC>>)> {
//         self.lock().unwrap().eval_lat_computation(key)
//     }
// }
// 
// impl<C: TaggedMapping, L: TaggedMapping, LC: TaggedMapping, T: LatticeMutContext<C, L, LC>> LatticeMutContext<C, L, LC> for Arc<Mutex<T>> {
//     fn lattice_join(&mut self, key: &L::Key, value: &L::Value, ctx_other: &mut dyn LatticeImmutContext<C, L, LC>) -> Res<L::Value> {
//         self.lock().unwrap().lattice_join(key, value, ctx_other)
//     }
// 
//     fn lattice_bottom(&mut self, key: &L::Key) -> Res<L::Value> {
//         self.lock().unwrap().lattice_bottom(key)
//     }
// }

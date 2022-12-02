
use std::collections::{BTreeSet, BTreeMap};
use std::sync::Arc;

use anyhow::bail;
use async_trait::async_trait;
use serde::{Serialize, Deserialize, de::DeserializeOwned};

use crate::error::Res;
use crate::crypto::{HashCode, Hash};
use crate::tagged_mapping::{TaggedMapping};

// enum Pattern {
//     Any,
//     Data(Vec<u8>),
//     Branch(String, Vec<Pattern>),
// }
// 
// enum TreeValue {
//     Data(Vec<u8>),
//     Branch(String, Vec<TreeValue>),
// }

#[async_trait]
pub trait HashLookup : Send + Sync {

    async fn hash_lookup(self: Arc<Self>, _hash: HashCode) -> Res<Vec<u8>> {
        bail!("hash_lookup not implemented")
    }
}

pub async fn hash_lookup_generic<H: HashLookup + ?Sized, T: DeserializeOwned>(hl: &Arc<H>, hsh: Hash<T>) -> Res<T> {
    let bs = hl.clone().hash_lookup(hsh.code).await?;
    Ok(rmp_serde::from_slice(&bs)?)
}

#[async_trait]
pub trait HashPut : HashLookup + Send + Sync {

    async fn hash_put(self: Arc<Self>, _value: Vec<u8>) -> Res<HashCode> {
        bail!("hash_put not implemented")
    }

}

pub async fn hash_put_generic<H: HashPut + ?Sized, T: Serialize>(hp: &Arc<H>, value: &T) -> Res<Hash<T>> {
    let bs = rmp_serde::to_vec(value)?;
    Ok(Hash::from_hashcode(hp.clone().hash_put(bs).await?))
}


#[async_trait]
pub trait ComputationImmutContext<C: TaggedMapping> : HashLookup + Send + Sync {

    async fn eval_computation(self: Arc<Self>, _key: &C::Key) -> Res<C::Value> {
        bail!("eval_computation not implemented")
    }
}


#[async_trait]
pub trait ComputationLibrary<C: TaggedMapping + 'static> : Send + Sync {

    async fn eval_computation(self: Arc<Self>, _key: &C::Key, _ctx: Arc<dyn ComputationImmutContext<C>>) -> Res<C::Value> {
        bail!("eval_computation not implemented")
    }
}

// #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
// pub struct LatMerkleDeps<LK: Ord, LV, LPK: Ord, LPV> {
//     pub lat_deps: BTreeMap<LK, Hash<LatMerkleNode<LK, LV, LPK, LPV, LV>>>,
//     pub lat_comp_deps: BTreeMap<LPK, Hash<LatMerkleNode<LK, LV, LPK, LPV, LPV>>>,
// }
// 
// type LatMerkleDepsM<L: TaggedMapping, LP: TaggedMapping> = LatMerkleDeps<L::Key, L::Value, LP::Key, LP::Value>;
// 
// impl<LK: Ord, LV, LPK: Ord, LPV> LatMerkleDeps<LK, LV, LPK, LPV> {
//     pub fn new() -> Self {
//         LatMerkleDeps {
//             lat_deps: BTreeMap::new(),
//             lat_comp_deps: BTreeMap::new(),
//         }
//     }
//     pub fn is_empty(&self) -> bool {
//         self.lat_deps.is_empty() && self.lat_comp_deps.is_empty()
//     }
//     pub fn try_union(&mut self, other: Self) -> Res<()> {
//         for (k, v) in other.lat_deps {
//             if let Some(v2) = self.lat_deps.get(&k) {
//                 if v != *v2 {
//                     bail!("lat_deps conflict")
//                 }
//             } else {
//                 self.lat_deps.insert(k, v);
//             }
//         }
//         for (k, v) in other.lat_comp_deps {
//             if let Some(v2) = self.lat_comp_deps.get(&k) {
//                 if v != *v2 {
//                     bail!("lat_comp_deps conflict")
//                 }
//             } else {
//                 self.lat_comp_deps.insert(k, v);
//             }
//         }
//         Ok(())
//     }
// 
// }
// 
// 
// #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
// pub struct LatMerkleNode<LK: Ord, LV, LPK: Ord, LPV, V> {
//     pub value: V,
//     pub deps: LatMerkleDeps<LK, LV, LPK, LPV>,
// }
// 
// type LatMerkleNodeM<L: TaggedMapping, LP: TaggedMapping, V> = LatMerkleNode<L::Key, L::Value, LP::Key, LP::Value, V>;


#[async_trait]
pub trait LatticeLibrary<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LP: TaggedMapping + 'static> : Send + Sync {

    // it's a valid element if check_elem returns a set and each the predicates pass
    async fn check_elem(self: Arc<Self>, _key: &L::Key, _value: &L::Value, _ctx: Arc<dyn PredicateImmutContext<C, L, LP>>) -> Res<()> {
        bail!("check_elem not implemented")
    }

    // precondition: check_requirements(check_elem(key, deps, a, ctx)) && check_requirements(check_elem(key, deps, b, ctx))
    // postcondition: check_requirements(check_elem(key, deps, self.join(a, b, ctx), ctx))
    // postcondition is satisfied if either a or b is returned (total order)
    // must be commutative, associative, idempotent
    async fn join(self: Arc<Self>, _key: &L::Key, _a: &L::Value, _b: &L::Value, _ctx: Arc<dyn ComputationMutContext<C>>) -> Res<L::Value> {
        bail!("join not implemented")
    }

    // computes a lower bound on the lattice given the context
    // should be monotonic in ctx
    // async fn bound(self: Arc<Self>, _key: &L::Key, _value: &L::Value, _ctx: Arc<dyn LatticeMutContext<C, L, LP>>) -> Res<Option<L::Value>> {
    //     Ok(None)
    // }

    // predicates are like the {0, 1} lattice
    // should be monotonic in ctx
    async fn check_predicate(self: Arc<Self>, _key: &LP::Key, _ctx: Arc<dyn PredicateImmutContext<C, L, LP>>) -> Res<()> {
        bail!("check_predicate not implemented")
    }

    // async fn eval_lat_computation(self: Arc<Self>, _key: &LP::Key, _ctx: Arc<dyn LatticeMutContext<C, L, LP>>) -> Res<LP::Value> {
    //     bail!("eval_lat_computation not implemented")
    // }
}

pub enum LowerBound<V> {
    Geq(Option<V>),
    Gt(Option<V>),
}

#[async_trait]
pub trait PredicateImmutContext<C: TaggedMapping, L: TaggedMapping, LP: TaggedMapping> : ComputationImmutContext<C> {
    async fn check_predicate(self: Arc<Self>, key: &LP::Key) -> Res<()>;

    async fn check_lower_bound(self: Arc<Self>, key: &L::Key, lb: LowerBound<L::Value>) -> Res<()>;
}

// #[async_trait]
// pub trait LatticeImmutContext<C: TaggedMapping, L: TaggedMapping, LP: TaggedMapping> : ComputationImmutContext<C> {
// 
//     async fn lattice_lookup(self: Arc<Self>, key: &L::Key) -> Res<Option<L::Value>>;
// 
//     async fn check_predicate(self: Arc<Self>, key: &LP::Key) -> Res<()>;
// 
// }

// pub trait AsLatticeImmutContext<C: TaggedMapping, L: TaggedMapping, LP: TaggedMapping> : LatticeImmutContext<C, L, LP> {
//     fn as_lattice_immut_ctx(self: Arc<Self>) -> Arc<dyn LatticeImmutContext<C, L, LP>>;
// }
// 
// impl<C: TaggedMapping, L: TaggedMapping, LP: TaggedMapping, T: 'static + LatticeImmutContext<C, L, LP>> AsLatticeImmutContext<C, L, LP> for T {
//     fn as_lattice_immut_ctx(self: Arc<Self>) -> Arc<dyn LatticeImmutContext<C, L, LP>> {
//         self
//     }
// }

#[async_trait]
pub trait ComputationMutContext<C: TaggedMapping>: HashPut + ComputationImmutContext<C> {

}

// #[async_trait]
// pub trait LatticeMutContext<C: TaggedMapping, L: TaggedMapping, LP: TaggedMapping>: ComputationMutContext<C> + LatticeImmutContext<C, L, LP> {
// 
// }


// #[derive(Clone)]
// pub struct EmptyComputationLibrary;
// 
// impl<C: TaggedMapping + 'static> ComputationLibrary<C> for EmptyComputationLibrary {}
// 
// #[derive(Clone)]
// pub struct EmptyLatticeLibrary;
// 
// impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LP: TaggedMapping + 'static> LatticeLibrary<C, L, LP> for EmptyLatticeLibrary {}
// 
// #[derive(Clone)]
// pub struct EmptyContext;
// 
// #[async_trait]
// impl HashLookup for EmptyContext {
//     async fn hash_lookup(self: Arc<Self>, hash: HashCode) -> Res<Vec<u8>> {
//         bail!("EmptyHashLookup: no hash lookup for {:?}", hash)
//     }
// }
// 
// #[async_trait]
// impl HashPut for EmptyContext {
//     async fn hash_put(self: Arc<Self>, value: Vec<u8>) -> Res<HashCode> {
//         bail!("EmptyComputationMutContext: no hash put for {:?}", value)
//     }
// }
// 
// #[async_trait]
// impl<C: TaggedMapping + 'static> ComputationImmutContext<C> for EmptyContext {
//     async fn eval_computation(self: Arc<Self>, key: &C::Key) -> Res<C::Value> {
//         bail!("EmptyComputationImmutContext: no computation for {:?}", key)
//     }
// }
// 
// #[async_trait]
// impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LP: TaggedMapping + 'static> LatticeImmutContext<C, L, LP> for EmptyContext {
// 
//     async fn lattice_lookup(self: Arc<Self>, key: &L::Key) -> Res<Option<Hash<LatMerkleNode<L::Key, L::Value, LP::Key, LP::Value, L::Value>>>> {
//         bail!("EmptyLatticeImmutContext: no lattice lookup for {:?}", key)
//     }
// 
//     async fn eval_lat_computation(self: Arc<Self>, key: &LP::Key) -> Res<Hash<LatMerkleNode<L::Key, L::Value, LP::Key, LP::Value, LP::Value>>> {
//         bail!("EmptyLatticeImmutContext: no lattice computation for {:?}", key)
//     }
// 
// }
// 
// #[async_trait]
// impl<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LP: TaggedMapping + 'static> LatticeMutContext<C, L, LP> for EmptyContext {
// }

struct BytesMapping;

impl TaggedMapping for BytesMapping {
    type Key = Vec<u8>;
    type Value = Vec<u8>;
}

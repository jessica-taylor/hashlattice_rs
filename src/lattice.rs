use std::collections::{BTreeSet, BTreeMap};
use std::cmp::Ordering;
use std::sync::Arc;

use serde::{Serialize, Deserialize, de::DeserializeOwned};

pub enum LatResult<G: LatGraph, D, T> {
    Done(Result<T, String>),
    Lookup(D, G::Key, Box<dyn Send + Sync + FnOnce(&G, G::Value) -> LatResult<G, D, T>>)
}

impl<G: LatGraph + 'static, D: 'static, T: 'static> LatResult<G, D, T> {
    pub fn and_then<U>(self, f: impl 'static + Send + Sync + FnOnce(T) -> LatResult<G, D, U>) -> LatResult<G, D, U> {
        match self {
            LatResult::Done(Ok(t)) => f(t),
            LatResult::Done(Err(e)) => LatResult::Done(Err(e)),
            LatResult::Lookup(key, dep, g) => LatResult::Lookup(key, dep, Box::new(move |lat, value| g(lat, value).and_then(f)))
        }
    }
    pub fn map<U>(self, f: impl 'static + Send + Sync + FnOnce(T) -> U) -> LatResult<G, D, U> {
        self.and_then(move |t| LatResult::Done(Ok(f(t))))
    }
}

pub trait LatGraph : Send + Sync + Sized {

    type Key : Eq + Ord + Clone + Send + Sync + Serialize + DeserializeOwned;

    type Value : Eq + Clone + Send + Sync + Serialize + DeserializeOwned;

    fn cmp_keys(&self, key1: &Self::Key, key2: &Self::Key) -> Result<Ordering, String> {
        key1.partial_cmp(key2).ok_or("Keys are not comparable".to_string())
    }

    fn check_elem(&self, key: &Self::Key, value: &Self::Value) -> LatResult<Self, (), ()>;

    fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value) -> LatResult<Self, (), Self::Value>;

    fn bottom(&self, key: &Self::Key) -> LatResult<Self, (), Self::Value>;

    fn transport(&self, key: &Self::Key, value: &Self::Value) -> LatResult<Self, bool, Self::Value>;

}

// pub struct SerializeLatGraph<'a, L: LatGraph>(&'a L);
// 
// impl<'a, L: LatGraph> SerializeLatGraph<'a, L> {
//     pub fn new(l: &'a L) -> Self {
//         SerializeLatGraph(l)
//     }
// }
// 
// impl<'a, L: LatGraph + 'static> SerializeLatGraph<'a, L> {
//     fn unser_key(key: &[u8]) -> Result<L::Key, String> {
//         rmp_serde::from_slice(key).map_err(|e| format!("failed to deserialize key: {}", e))
//     }
//     fn unser_value(value: &[u8]) -> Result<L::Value, String> {
//         rmp_serde::from_slice(value).map_err(|e| format!("failed to deserialize value: {}", e))
//     }
//     fn ser_key(key: &L::Key) -> Result<Vec<u8>, String> {
//         rmp_serde::to_vec(key).map_err(|e| format!("failed to serialize key: {}", e))
//     }
//     fn ser_value(value: &L::Value) -> Result<Vec<u8>, String> {
//         rmp_serde::to_vec(value).map_err(|e| format!("failed to serialize value: {}", e))
//     }
//     fn ser_keys(deps: &BTreeSet<L::Key>) -> Result<BTreeSet<Vec<u8>>, String> {
//         let mut ser_deps = BTreeSet::new();
//         for dep in deps {
//             ser_deps.insert(Self::ser_key(dep)?);
//         }
//         Ok(ser_deps)
//     }
//     fn unser_values(deps: &BTreeMap<Vec<u8>, Vec<u8>>) -> Result<BTreeMap<L::Key, L::Value>, String> {
//         let mut unser_deps = BTreeMap::new();
//         for (k, v) in deps {
//             unser_deps.insert(Self::unser_key(k)?, Self::unser_value(v)?);
//         }
//         Ok(unser_deps)
//     }
// }
// 
// impl<'a, L: LatGraph + 'static> LatGraph for SerializeLatGraph<'a, L> {
// 
//     type Key = Vec<u8>;
// 
//     type Value = Vec<u8>;
// 
//     fn cmp_keys(&self, key1: &Vec<u8>, key2: &Vec<u8>) -> Result<Ordering, String> {
//         self.0.cmp_keys(&Self::unser_key(key1)?, &Self::unser_key(key2)?)
//     }
// 
//     fn lat_deps(&self, key: &Vec<u8>) -> Result<BTreeSet<Vec<u8>>, String> {
//         Self::ser_keys(&self.0.lat_deps(&Self::unser_key(key)?)?)
//     }
// 
//     fn value_deps(&self, key: &Vec<u8>, value: &Vec<u8>) -> Result<BTreeSet<Vec<u8>>, String> {
//         Self::ser_keys(&self.0.value_deps(&Self::unser_key(key)?, &Self::unser_value(value)?)?)
//     }
// 
//     fn check_elem(&self, key: &Vec<u8>, value: &Vec<u8>, deps: &BTreeMap<Vec<u8>, Vec<u8>>) -> Result<(), String> {
//         self.0.check_elem(&Self::unser_key(key)?, &Self::unser_value(value)?, &Self::unser_values(deps)?)
//     }
// 
//     fn join(&self, key: &Vec<u8>, v1: &Vec<u8>, v2: &Vec<u8>, deps: &BTreeMap<Vec<u8>, Vec<u8>>) -> Result<Vec<u8>, String> {
//         Self::ser_value(&self.0.join(&Self::unser_key(key)?, &Self::unser_value(v1)?, &Self::unser_value(v2)?, &Self::unser_values(deps)?)?)
//     }
// 
//     fn bottom(&self, key: &Vec<u8>, deps: &BTreeMap<Vec<u8>, Vec<u8>>) -> Result<Self::Value, String> {
//         Self::ser_value(&self.0.bottom(&Self::unser_key(key)?, &Self::unser_values(deps)?)?)
//     }
// 
//     fn transport(&self, key: &Vec<u8>, value: &Vec<u8>, old_deps: &BTreeMap<Vec<u8>, Vec<u8>>, new_deps: &BTreeMap<Vec<u8>, Vec<u8>>) -> Result<Vec<u8>, String> {
//         Self::ser_value(&self.0.transport(&Self::unser_key(key)?, &Self::unser_value(value)?, &Self::unser_values(old_deps)?, &Self::unser_values(new_deps)?)?)
//     }
// }
// 
// pub trait IsEnum {
//     fn get_branch(&self) -> usize;
// }
// 
// pub struct EnumLatGraph<'a, L: LatGraph>(Vec<&'a L>);
// 
// impl<'a, L: LatGraph> EnumLatGraph<'a, L> {
//     pub fn new(l: Vec<&'a L>) -> Self {
//         EnumLatGraph(l)
//     }
// 
//     fn check_branch_eq(branch1: usize, branch2: usize) -> Result<(), String> {
//         if branch1 != branch2 {
//             return Err(format!("branches do not match: {} != {}", branch1, branch2))
//         }
//         Ok(())
//     }
// 
//     fn lat_by_branch(&self, branch: usize) -> Result<&'a L, String> {
//         if branch >= self.0.len() {
//             return Err(format!("branch {} out of bounds", branch))
//         }
//         Ok(self.0[branch])
//     }
// }
// 
// impl<'a, L: LatGraph + 'static> LatGraph for EnumLatGraph<'a, L>
// where L::Key: IsEnum, L::Value: IsEnum {
//     
//     type Key = L::Key;
// 
//     type Value = L::Value;
// 
//     fn cmp_keys(&self, key1: &L::Key, key2: &L::Key) -> Result<Ordering, String> {
//         Self::check_branch_eq(key1.get_branch(), key2.get_branch())?;
//         self.lat_by_branch(key1.get_branch())?.cmp_keys(key1, key2)
//     }
// 
//     fn lat_deps(&self, key: &L::Key) -> Result<BTreeSet<L::Key>, String> {
//         self.lat_by_branch(key.get_branch())?.lat_deps(key)
//     }
// 
//     fn value_deps(&self, key: &L::Key, value: &L::Value) -> Result<BTreeSet<L::Key>, String> {
//         Self::check_branch_eq(key.get_branch(), value.get_branch())?;
//         self.lat_by_branch(key.get_branch())?.value_deps(key, value)
//     }
// 
//     fn check_elem(&self, key: &L::Key, v: &L::Value, deps: &BTreeMap<L::Key, L::Value>) -> Result<(), String> {
//         Self::check_branch_eq(key.get_branch(), v.get_branch())?;
//         self.lat_by_branch(key.get_branch())?.check_elem(key, v, deps)
//     }
// 
//     fn join(&self, key: &L::Key, v1: &L::Value, v2: &L::Value, deps: &BTreeMap<L::Key, L::Value>) -> Result<L::Value, String> {
//         Self::check_branch_eq(key.get_branch(), v1.get_branch())?;
//         Self::check_branch_eq(key.get_branch(), v2.get_branch())?;
//         self.lat_by_branch(key.get_branch())?.join(key, v1, v2, deps)
//     }
// 
//     fn bottom(&self, key: &L::Key, deps: &BTreeMap<L::Key, L::Value>) -> Result<L::Value, String> {
//         self.lat_by_branch(key.get_branch())?.bottom(key, deps)
//     }
// 
//     fn transport(&self, key: &L::Key, value: &L::Value, old_deps: &BTreeMap<L::Key, L::Value>, new_deps: &BTreeMap<L::Key, L::Value>) -> Result<L::Value, String> {
//         Self::check_branch_eq(key.get_branch(), value.get_branch())?;
//         self.lat_by_branch(key.get_branch())?.transport(key, value, old_deps, new_deps)
//     }
// }
// 
// #[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug, Serialize, Deserialize)]
// pub enum Either<A, B> {
//     Left(A),
//     Right(B),
// }
// 
// pub trait DepLatGraph<L: LatGraph> : Send + Sync {
// 
//     type Key : Eq + Ord + Clone + Send + Sync + Serialize + DeserializeOwned;
// 
//     type Value : Eq + Clone + Send + Sync + Serialize + DeserializeOwned;
// 
//     fn lat_deps(&self, key: &Self::Key) -> Result<BTreeSet<Either<L::Key, Self::Key>>, String>;
// 
//     fn value_deps(&self, key: &Self::Key, value: &Self::Value) -> Result<BTreeSet<Either<L::Key, Self::Key>>, String>;
// 
//     fn check_elem(&self, key: &Self::Key, value: &Self::Value, ldeps: &BTreeMap<L::Key, L::Value>, rdeps: &BTreeMap<Self::Key, Self::Value>) -> Result<(), String>;
// 
//     fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value, ldeps: &BTreeMap<L::Key, L::Value>, rdeps: &BTreeMap<Self::Key, Self::Value>) -> Result<Self::Value, String>;
// 
//     fn bottom(&self, key: &Self::Key, ldeps: &BTreeMap<L::Key, L::Value>, rdeps: &BTreeMap<Self::Key, Self::Value>) -> Result<Self::Value, String>;
// 
//     fn transport(&self, key: &Self::Key, value: &Self::Value, old_ldeps: &BTreeMap<L::Key, L::Value>, old_rdeps: &BTreeMap<Self::Key, Self::Value>, new_ldeps: &BTreeMap<L::Key, L::Value>, new_rdeps: &BTreeMap<Self::Key, Self::Value>) -> Result<Self::Value, String>;
// }
// 
// struct TotalLatGraph<L: LatGraph, D: DepLatGraph<L>> {
//     lat: L,
//     dep: D,
// }
// 
// impl<L: LatGraph, D: DepLatGraph<L>> TotalLatGraph<L, D> {
//     fn new(lat: L, dep: D) -> Self {
//         TotalLatGraph { lat, dep }
//     }
//     fn deps_to_left(deps: &BTreeSet<L::Key>) -> BTreeSet<Either<L::Key, D::Key>> {
//         deps.iter().map(|k| Either::Left(k.clone())).collect()
//     }
// 
//     fn separate_deps(deps: &BTreeMap<Either<L::Key, D::Key>, Either<L::Value, D::Value>>) -> Result<(BTreeMap<L::Key, L::Value>, BTreeMap<D::Key, D::Value>), String> {
//         let mut ldeps = BTreeMap::new();
//         let mut rdeps = BTreeMap::new();
//         for (k, v) in deps {
//             match (k, v) {
//                 (Either::Left(k), Either::Left(v)) => { ldeps.insert(k.clone(), v.clone()); },
//                 (Either::Right(k), Either::Right(v)) => { rdeps.insert(k.clone(), v.clone()); },
//                 _ => { return Err(format!("mismatched key and value")); },
//             }
//         }
//         Ok((ldeps, rdeps))
//     }
// }
// 
// impl<L: LatGraph, D: DepLatGraph<L>> LatGraph for TotalLatGraph<L, D> {
//     type Key = Either<L::Key, D::Key>;
// 
//     type Value = Either<L::Value, D::Value>;
// 
//     fn cmp_keys(&self, k1: &Self::Key, k2: &Self::Key) -> Ordering {
//         match (k1, k2) {
//             (Either::Left(k1), Either::Left(k2)) => self.lat.cmp_keys(k1, k2),
//             (Either::Right(k1), Either::Right(k2)) => self.dep.cmp_keys(k1, k2),
//             (Either::Left(_), Either::Right(_)) => Ordering::Less,
//             (Either::Right(_), Either::Left(_)) => Ordering::Greater,
//         }
//     }
// 
//     fn lat_deps(&self, key: &Self::Key) -> Result<BTreeSet<Self::Key>, String> {
//         match key {
//             Either::Left(k) => Ok(Self::deps_to_left(&self.lat.lat_deps(k)?)),
//             Either::Right(k) => self.dep.lat_deps(k)
//         }
//     }
// 
//     fn value_deps(&self, key: &Self::Key, value: &Self::Value) -> Result<BTreeSet<Self::Key>, String> {
//         match (key, value) {
//             (Either::Left(k), Either::Left(v)) => Ok(Self::deps_to_left(&self.lat.value_deps(k, v)?)),
//             (Either::Right(k), Either::Right(v)) => self.dep.value_deps(k, v),
//             _ => Err("key/value mismatch".to_string()),
//         }
//     }
// 
//     fn check_elem(&self, key: &Self::Key, value: &Self::Value, deps: &BTreeMap<Self::Key, Self::Value>) -> Result<(), String> {
//         let (ldeps, rdeps) = Self::separate_deps(deps)?;
//         match (key, value) {
//             (Either::Left(k), Either::Left(v)) => self.lat.check_elem(k, v, &ldeps),
//             (Either::Right(k), Either::Right(v)) => self.dep.check_elem(k, v, &ldeps, &rdeps),
//             _ => Err("key/value mismatch".to_string()),
//         }
//     }
// 
//     fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value, deps: &BTreeMap<Self::Key, Self::Value>) -> Result<Self::Value, String> {
//         let (ldeps, rdeps) = Self::separate_deps(deps)?;
//         match (key, value1, value2) {
//             (Either::Left(k), Either::Left(v1), Either::Left(v2)) => Ok(Either::Left(self.lat.join(k, v1, v2, &ldeps)?)),
//             (Either::Right(k), Either::Right(v1), Either::Right(v2)) => Ok(Either::Right(self.dep.join(k, v1, v2, &ldeps, &rdeps)?)),
//             _ => Err("key/value mismatch".to_string()),
//         }
//     }
//     fn bottom(&self, key: &Self::Key, deps: &BTreeMap<Self::Key, Self::Value>) -> Result<Self::Value, String> {
//         let (ldeps, rdeps) = Self::separate_deps(deps)?;
//         match key {
//             Either::Left(k) => Ok(Either::Left(self.lat.bottom(k, &ldeps)?)),
//             Either::Right(k) => Ok(Either::Right(self.dep.bottom(k, &ldeps, &rdeps)?)),
//         }
//     }
//     fn transport(&self, key: &Self::Key, value: &Self::Value, old_deps: &BTreeMap<Self::Key, Self::Value>, new_deps: &BTreeMap<Self::Key, Self::Value>) -> Result<Self::Value, String> {
//         let (old_ldeps, old_rdeps) = Self::separate_deps(old_deps)?;
//         let (new_ldeps, new_rdeps) = Self::separate_deps(new_deps)?;
//         match (key, value) {
//             (Either::Left(k), Either::Left(v)) => Ok(Either::Left(self.lat.transport(k, v, &old_ldeps, &new_ldeps)?)),
//             (Either::Right(k), Either::Right(v)) => Ok(Either::Right(self.dep.transport(k, v, &old_ldeps, &old_rdeps, &new_ldeps, &new_rdeps)?)),
//             _ => Err("key/value mismatch".to_string()),
//         }
//     }
// }
// 
// trait LatSubgraph<Tag> : MappingType<Tag> {
//     fn lat_deps(&self, key: &Self::Key) -> Result<TagSet<Tag>, String>;
// 
//     fn value_deps(&self, key: &Self::Key, value: &Self::Value) -> Result<TagSet<Tag>, String>;
// 
//     fn check_elem(&self, key: &Self::Key, value: &Self::Value, deps: &TagMap<Tag>) -> Result<(), String>;
// 
//     fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value, deps: &TagMap<Tag>) -> Result<Self::Value, String>;
// 
//     fn bottom(&self, key: &Self::Key, deps: &TagMap<Tag>) -> Result<Self::Value, String>;
// 
//     fn transport(&self, key: &Self::Key, value: &Self::Value, old_deps: &TagMap<Tag>, new_deps: &TagMap<Tag>) -> Result<Self::Value, String>;
// }

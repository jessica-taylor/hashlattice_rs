use std::collections::{BTreeSet, BTreeMap};

use serde::{Serialize, de::DeserializeOwned};

/// A graph where each item is a semilattice, which may depend on other lattice max values.
pub trait LatGraph : Send + Sync {

    /// Keys identifying lattice value keys.
    type K : Eq + Ord + Clone + Serialize + DeserializeOwned + Send + Sync;

    /// The values themselves.
    type V : Eq + Clone + Serialize + DeserializeOwned + Send + Sync;

    /// Dependencies of a given key.
    fn dependencies(&self, key: &Self::K, value: Option<&Self::V>) -> Result<BTreeSet<Self::K>, String>;

    /// Joins two values given dependencies.
    fn join(&self, key: &Self::K, v1: &Self::V, v2: &Self::V, deps: &BTreeMap<Self::K, Self::V>) -> Result<Self::V, String>;

    /// The default element of the lattice.
    fn autofill(&self, key: &Self::K, deps: &BTreeMap<Self::K, Self::V>) -> Result<Self::V, String>;
}

pub struct SerializeLatGraph<'a, L: LatGraph>(&'a L);

impl<'a, L: LatGraph> SerializeLatGraph<'a, L> {
    pub fn new(l: &'a L) -> Self {
        SerializeLatGraph(l)
    }
}

impl<'a, L: LatGraph + 'static> LatGraph for SerializeLatGraph<'a, L> {

    type K = Vec<u8>;

    type V = Vec<u8>;

    fn dependencies(&self, key: &Vec<u8>, value: Option<&Vec<u8>>) -> Result<BTreeSet<Vec<u8>>, String> {
        let key = rmp_serde::from_slice(key).map_err(|e| format!("failed to deserialize key: {}", e))?;
        let unser_deps = match value {
            None => self.0.dependencies(&key, None)?,
            Some(v) => {
                let value = rmp_serde::from_slice(v).map_err(|e| format!("failed to deserialize value: {}", e))?;
                self.0.dependencies(&key, Some(&value))?
            }
        };
        let mut deps = BTreeSet::new();
        for dep in unser_deps {
            deps.insert(rmp_serde::to_vec(&dep).map_err(|e| format!("failed to serialize key: {}", e))?);
        }
        Ok(deps)
    }

    fn join(&self, key: &Self::K, v1: &Self::V, v2: &Self::V, deps: &BTreeMap<Self::K, Self::V>) -> Result<Self::V, String> {
        let mut deps2 = BTreeMap::new();
        for (k, v) in deps.into_iter() {
            let k = rmp_serde::from_slice(&k).map_err(|e| format!("failed to deserialize key: {}", e))?;
            let v = rmp_serde::from_slice(&v).map_err(|e| format!("failed to deserialize value: {}", e))?;
            deps2.insert(k, v);
        }
        let key = rmp_serde::from_slice(key).map_err(|e| format!("failed to deserialize key: {}", e))?;
        let v1 = rmp_serde::from_slice(v1).map_err(|e| format!("failed to deserialize value: {}", e))?;
        let v2 = rmp_serde::from_slice(v2).map_err(|e| format!("failed to deserialize value: {}", e))?;
        let v = self.0.join(&key, &v1, &v2, &deps2)?;
        rmp_serde::to_vec_named(&v).map_err(|e| format!("failed to serialize value: {}", e))
    }

    fn autofill(&self, key: &Self::K, deps: &BTreeMap<Self::K, Self::V>) -> Result<Self::V, String> {
        let key = rmp_serde::from_slice(key).map_err(|e| format!("failed to deserialize key: {}", e))?;
        let mut deps2 = BTreeMap::new();
        for (k, v) in deps.into_iter() {
            let k = rmp_serde::from_slice(&k).map_err(|e| format!("failed to deserialize key: {}", e))?;
            let v = rmp_serde::from_slice(&v).map_err(|e| format!("failed to deserialize value: {}", e))?;
            deps2.insert(k, v);
        }
        let res = self.0.autofill(&key, &deps2)?;
        rmp_serde::to_vec_named(&res).map_err(|e| format!("failed to serialize value: {}", e))
    }
}

pub trait IsEnum {
    fn get_branch(&self) -> usize;
}

pub struct EnumLatGraph<'a, L: LatGraph>(Vec<&'a L>);

impl<'a, L: LatGraph> EnumLatGraph<'a, L> {
    pub fn new(l: Vec<&'a L>) -> Self {
        EnumLatGraph(l)
    }
}

impl<'a, L: LatGraph + 'static> LatGraph for EnumLatGraph<'a, L>
where L::K: IsEnum, L::V: IsEnum {
    
    type K = L::K;

    type V = L::V;

    fn dependencies(&self, key: &Self::K, value: Option<&Self::V>) -> Result<BTreeSet<Self::K>, String> {
        let branch = key.get_branch();
        match value {
            None => {},
            Some(v) => if v.get_branch() != branch {
                return Err(format!("branch mismatch: {} != {}", branch, v.get_branch()));
            }
        }
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        self.0[branch].dependencies(key, value)
    }

    fn join(&self, key: &Self::K, v1: &Self::V, v2: &Self::V, deps: &BTreeMap<Self::K, Self::V>) -> Result<Self::V, String> {
        let branch = key.get_branch();
        let branch2 = v1.get_branch();
        let branch3 = v2.get_branch();
        if branch != branch2 || branch != branch3 {
            return Err(format!("key and value have different branches: {} vs {} vs {}", branch, branch2, branch3));
        }
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        self.0[branch].join(key, v1, v2, deps)
    }

    fn autofill(&self, key: &Self::K, deps: &BTreeMap<Self::K, Self::V>) -> Result<Self::V, String> {
        let branch = key.get_branch();
        if branch >= self.0.len() {
            return Err(format!("branch {} out of range", branch));
        }
        self.0[branch].autofill(key, deps)
    }
}

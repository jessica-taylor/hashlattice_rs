use std::collections::{BTreeSet, BTreeMap};

use serde::{Serialize, de::DeserializeOwned};

pub trait LatGraph : Send + Sync {

    type Key : Eq + Ord + Clone + Send + Sync + Serialize + DeserializeOwned;

    type Value : Eq + Clone + Send + Sync + Serialize + DeserializeOwned;

    fn lat_deps(&self, key: &Self::Key) -> Result<BTreeSet<Self::Key>, String>;

    fn value_deps(&self, key: &Self::Key, value: &Self::Value) -> Result<BTreeSet<Self::Key>, String>;

    fn check_elem(&self, key: &Self::Key, value: &Self::Value, deps: &BTreeMap<Self::Key, Self::Value>) -> Result<(), String>;

    fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value, deps: &BTreeMap<Self::Key, Self::Value>) -> Result<Self::Value, String>;

    fn bottom(&self, key: &Self::Key, deps: &BTreeMap<Self::Key, Self::Value>) -> Result<Self::Value, String>;

    fn transport(&self, key: &Self::Key, value: &Self::Value, old_deps: &BTreeMap<Self::Key, Self::Value>, new_deps: &BTreeMap<Self::Key, Self::Value>) -> Result<Self::Value, String>;

}

pub struct SerializeLatGraph<'a, L: LatGraph>(&'a L);

impl<'a, L: LatGraph> SerializeLatGraph<'a, L> {
    pub fn new(l: &'a L) -> Self {
        SerializeLatGraph(l)
    }
}

impl<'a, L: LatGraph + 'static> SerializeLatGraph<'a, L> {
    fn unser_key(key: &[u8]) -> Result<L::Key, String> {
        rmp_serde::from_slice(key).map_err(|e| format!("failed to deserialize key: {}", e))
    }
    fn unser_value(value: &[u8]) -> Result<L::Value, String> {
        rmp_serde::from_slice(value).map_err(|e| format!("failed to deserialize value: {}", e))
    }
    fn ser_key(key: &L::Key) -> Result<Vec<u8>, String> {
        rmp_serde::to_vec(key).map_err(|e| format!("failed to serialize key: {}", e))
    }
    fn ser_value(value: &L::Value) -> Result<Vec<u8>, String> {
        rmp_serde::to_vec(value).map_err(|e| format!("failed to serialize value: {}", e))
    }
    fn ser_keys(deps: &BTreeSet<L::Key>) -> Result<BTreeSet<Vec<u8>>, String> {
        let mut ser_deps = BTreeSet::new();
        for dep in deps {
            ser_deps.insert(Self::ser_key(dep)?);
        }
        Ok(ser_deps)
    }
    fn unser_values(deps: &BTreeMap<Vec<u8>, Vec<u8>>) -> Result<BTreeMap<L::Key, L::Value>, String> {
        let mut unser_deps = BTreeMap::new();
        for (k, v) in deps {
            unser_deps.insert(Self::unser_key(k)?, Self::unser_value(v)?);
        }
        Ok(unser_deps)
    }
}

impl<'a, L: LatGraph + 'static> LatGraph for SerializeLatGraph<'a, L> {

    type Key = Vec<u8>;

    type Value = Vec<u8>;

    fn lat_deps(&self, key: &Vec<u8>) -> Result<BTreeSet<Vec<u8>>, String> {
        Self::ser_keys(&self.0.lat_deps(&Self::unser_key(key)?)?)
    }

    fn value_deps(&self, key: &Vec<u8>, value: &Vec<u8>) -> Result<BTreeSet<Vec<u8>>, String> {
        Self::ser_keys(&self.0.value_deps(&Self::unser_key(key)?, &Self::unser_value(value)?)?)
    }

    fn check_elem(&self, key: &Vec<u8>, value: &Vec<u8>, deps: &BTreeMap<Vec<u8>, Vec<u8>>) -> Result<(), String> {
        self.0.check_elem(&Self::unser_key(key)?, &Self::unser_value(value)?, &Self::unser_values(deps)?)
    }

    fn join(&self, key: &Vec<u8>, v1: &Vec<u8>, v2: &Vec<u8>, deps: &BTreeMap<Vec<u8>, Vec<u8>>) -> Result<Vec<u8>, String> {
        Self::ser_value(&self.0.join(&Self::unser_key(key)?, &Self::unser_value(v1)?, &Self::unser_value(v2)?, &Self::unser_values(deps)?)?)
    }

    fn bottom(&self, key: &Vec<u8>, deps: &BTreeMap<Vec<u8>, Vec<u8>>) -> Result<Self::Value, String> {
        Self::ser_value(&self.0.bottom(&Self::unser_key(key)?, &Self::unser_values(deps)?)?)
    }

    fn transport(&self, key: &Vec<u8>, value: &Vec<u8>, old_deps: &BTreeMap<Vec<u8>, Vec<u8>>, new_deps: &BTreeMap<Vec<u8>, Vec<u8>>) -> Result<Vec<u8>, String> {
        Self::ser_value(&self.0.transport(&Self::unser_key(key)?, &Self::unser_value(value)?, &Self::unser_values(old_deps)?, &Self::unser_values(new_deps)?)?)
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

    fn check_branch_eq(branch1: usize, branch2: usize) -> Result<(), String> {
        if branch1 != branch2 {
            return Err(format!("branches do not match: {} != {}", branch1, branch2))
        }
        Ok(())
    }

    fn lat_by_branch(&self, branch: usize) -> Result<&'a L, String> {
        if branch >= self.0.len() {
            return Err(format!("branch {} out of bounds", branch))
        }
        Ok(self.0[branch])
    }
}

impl<'a, L: LatGraph + 'static> LatGraph for EnumLatGraph<'a, L>
where L::Key: IsEnum, L::Value: IsEnum {
    
    type Key = L::Key;

    type Value = L::Value;

    fn lat_deps(&self, key: &L::Key) -> Result<BTreeSet<L::Key>, String> {
        self.lat_by_branch(key.get_branch())?.lat_deps(key)
    }

    fn value_deps(&self, key: &L::Key, value: &L::Value) -> Result<BTreeSet<L::Key>, String> {
        Self::check_branch_eq(key.get_branch(), value.get_branch())?;
        self.lat_by_branch(key.get_branch())?.value_deps(key, value)
    }

    fn check_elem(&self, key: &L::Key, v: &L::Value, deps: &BTreeMap<L::Key, L::Value>) -> Result<(), String> {
        Self::check_branch_eq(key.get_branch(), v.get_branch())?;
        self.lat_by_branch(key.get_branch())?.check_elem(key, v, deps)
    }

    fn join(&self, key: &L::Key, v1: &L::Value, v2: &L::Value, deps: &BTreeMap<L::Key, L::Value>) -> Result<L::Value, String> {
        Self::check_branch_eq(key.get_branch(), v1.get_branch())?;
        Self::check_branch_eq(key.get_branch(), v2.get_branch())?;
        self.lat_by_branch(key.get_branch())?.join(key, v1, v2, deps)
    }

    fn bottom(&self, key: &L::Key, deps: &BTreeMap<L::Key, L::Value>) -> Result<L::Value, String> {
        self.lat_by_branch(key.get_branch())?.bottom(key, deps)
    }

    fn transport(&self, key: &L::Key, value: &L::Value, old_deps: &BTreeMap<L::Key, L::Value>, new_deps: &BTreeMap<L::Key, L::Value>) -> Result<L::Value, String> {
        Self::check_branch_eq(key.get_branch(), value.get_branch())?;
        self.lat_by_branch(key.get_branch())?.transport(key, value, old_deps, new_deps)
    }
}

use std::collections::{BTreeSet, BTreeMap};

use serde::{Serialize, de::DeserializeOwned};

pub trait LatGraph : Send + Sync {

    type Key : Eq + Ord + Clone + Send + Sync + Serialize + DeserializeOwned;

    type Value : Eq + Clone + Send + Sync + Serialize + DeserializeOwned;

    fn lat_deps(&self, key: &Self::Key) -> BTreeSet<Self::Key>;

    fn value_deps(&self, key: &Self::Key, value: &Self::Value) -> BTreeSet<Self::Key>;

    fn is_elem(&self, key: &Self::Key, value: &Self::Value, deps: BTreeMap<Self::Key, Self::Value>) -> bool;

    fn join(&self, key: &Self::Key, value1: &Self::Value, value2: &Self::Value, deps: BTreeMap<Self::Key, Self::Value>) -> Self::Value;

    fn bottom(&self, key: &Self::Key, deps: BTreeMap<Self::Key, Self::Value>) -> Self::Value;

    fn transport(&self, key: &Self::Key, value: &Self::Value, old_deps: BTreeMap<Self::Key, Self::Value>, new_deps: BTreeMap<Self::Key, Self::Value>) -> Self::Value;

}


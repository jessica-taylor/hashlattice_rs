use std::sync::Arc;

use anyhow::{bail};
use async_trait::async_trait;

use hashlattice::error::Res;
use hashlattice::tagged_mapping::TaggedMapping;
use hashlattice::lattice::{EmptyComputationLibrary, LatticeLibrary, LatticeImmutContext, LatticeMutContext, EmptyContext, hash_lookup_generic};
use hashlattice::db::{LatStore, LatDBMapping};
use hashlattice::sql_db::SqlDepDB;

struct EmptyMapping;
impl TaggedMapping for EmptyMapping {
    type Key = ();
    type Value = ();
}

struct MaxTupleMapping;
impl TaggedMapping for MaxTupleMapping {
    type Key = String;
    type Value = Vec<usize>;
}

struct MaxTupleLatLibrary(usize);

#[async_trait]
impl LatticeLibrary<EmptyMapping, MaxTupleMapping, EmptyMapping> for MaxTupleLatLibrary {
    async fn check_elem(self: Arc<Self>, _key: &String, value: &Vec<usize>, _ctx: Arc<dyn LatticeImmutContext<EmptyMapping, MaxTupleMapping, EmptyMapping>>) -> Res<()> {
        if value.len() != self.0 {
            bail!("wrong length");
        }
        Ok(())
    }
    async fn join(self: Arc<Self>, _key: &String, value1: &Vec<usize>, value2: &Vec<usize>, _ctx: Arc<dyn LatticeMutContext<EmptyMapping, MaxTupleMapping, EmptyMapping>>) -> Res<Option<Vec<usize>>> {
        let mut result = value1.clone();
        for (i, v) in value2.iter().enumerate() {
            result[i] = std::cmp::max(result[i], *v);
        }
        Ok(Some(result))
    }
}

async fn test_lookup<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static>(store: &Arc<LatStore<C, L, LC>>, key: &L::Key, expected: L::Value) {
    assert_eq!(expected, hash_lookup_generic(&store, store.clone().lattice_lookup(key).await.unwrap().unwrap()).await.unwrap().value);
}

async fn test_join<C: TaggedMapping + 'static, L: TaggedMapping + 'static, LC: TaggedMapping + 'static>(store: &Arc<LatStore<C, L, LC>>, key: &L::Key, value: L::Value, expected: L::Value) {
    assert_eq!(expected.clone(), hash_lookup_generic(&store, store.lattice_join_elem(key, value).await.unwrap().unwrap()).await.unwrap().value);
    test_lookup(store, key, expected).await;
}


#[tokio::test]
async fn test_db() {
    let mut db = SqlDepDB::<LatDBMapping<EmptyMapping, MaxTupleMapping, EmptyMapping>>::new(":memory:").unwrap();
    db.initialize().unwrap();
    let store = Arc::new(LatStore::new(db, Arc::new(EmptyComputationLibrary), Arc::new(MaxTupleLatLibrary(3)), Arc::new(EmptyContext)));

    let mut key = "first".to_string();
    assert!(store.clone().lattice_lookup(&key).await.unwrap().is_none());

    test_join(&store, &key, vec![1, 2, 3], vec![1, 2, 3]).await;
    test_join(&store, &key, vec![2, 1, 3], vec![2, 2, 3]).await;
    test_join(&store, &key, vec![1, 1, 1], vec![2, 2, 3]).await;
    test_join(&store, &key, vec![2, 2, 3], vec![2, 2, 3]).await;

    key = "second".to_string();
    assert!(store.clone().lattice_lookup(&key).await.unwrap().is_none());

    test_join(&store, &key, vec![1, 0, 1], vec![1, 0, 1]).await;
    test_join(&store, &key, vec![0, 1, 1], vec![1, 1, 1]).await;

    test_lookup(&store, &"first".to_string(), vec![2, 2, 3]).await;
}

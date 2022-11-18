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


#[tokio::test]
async fn test_db() {
    let mut db = SqlDepDB::<LatDBMapping<EmptyMapping, MaxTupleMapping, EmptyMapping>>::new(":memory:").unwrap();
    db.initialize().unwrap();
    let store = Arc::new(LatStore::new(db, EmptyComputationLibrary, MaxTupleLatLibrary(3), EmptyContext));
    let key = "first".to_string();
    assert!(store.clone().lattice_lookup(&key).await.unwrap().is_none());
    assert_eq!(vec![1, 2, 0], hash_lookup_generic(&store, store.lattice_join_elem(&key, vec![1, 2, 0]).await.unwrap().unwrap()).await.unwrap().value);
    // assert_eq!(vec![1, 2, 0], store.lattice_lookup(&key).unwrap().unwrap().0);
    // assert_eq!(vec![4, 2, 1], store.lattice_join(&key, &vec![4, 0, 1], &EmptyContext).unwrap());
    // assert_eq!(vec![4, 2, 1], store.lattice_lookup(&key).unwrap().unwrap().0);
    // 
    // key = "second".to_string();
    // assert!(store.lattice_lookup(&key).await.unwrap().is_none());
    // assert_eq!(vec![1, 0, 1], store.lattice_join(&key, &vec![1, 0, 1], &EmptyContext).unwrap());
    // assert_eq!(vec![1, 0, 1], store.lattice_lookup(&key).unwrap().unwrap().0);
    // assert_eq!(vec![1, 2, 3], store.lattice_join(&key, &vec![0, 2, 3], &EmptyContext).unwrap());
    // assert_eq!(vec![1, 2, 3], store.lattice_lookup(&key).unwrap().unwrap().0);

    // assert_eq!(vec![4, 2, 1], store.lattice_lookup(&"first".to_string()).unwrap().unwrap().0);
}

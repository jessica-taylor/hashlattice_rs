use hashlattice::error::{Res, str_error};
use hashlattice::tagged_mapping::TaggedMapping;
use hashlattice::lattice::{EmptyComputationLibrary, LatticeLibrary, LatticeImmutContext, LatticeMutContext, EmptyContext};
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

impl LatticeLibrary<EmptyMapping, MaxTupleMapping, EmptyMapping> for MaxTupleLatLibrary {
    fn check_elem(&self, _key: &String, value: &Vec<usize>, _ctx: &dyn LatticeImmutContext<EmptyMapping, MaxTupleMapping, EmptyMapping>) -> Res<()> {
        if value.len() != self.0 {
            return str_error("wrong length");
        }
        Ok(())
    }
    fn join(&self, _key: &String, value1: &Vec<usize>, value2: &Vec<usize>, _ctx: &dyn LatticeMutContext<EmptyMapping, MaxTupleMapping, EmptyMapping>) -> Res<Vec<usize>> {
        let mut result = value1.clone();
        for (i, v) in value2.iter().enumerate() {
            result[i] = std::cmp::max(result[i], *v);
        }
        Ok(result)
    }
    fn eval_lat_computation(&self, _comp: &(), _ctx: &dyn LatticeImmutContext<EmptyMapping, MaxTupleMapping, EmptyMapping>) -> Res<()> {
        str_error("no computations")
    }

}


#[tokio::test]
async fn test_db() {
    let mut db = SqlDepDB::<LatDBMapping<EmptyMapping, MaxTupleMapping, EmptyMapping>>::new(":memory:").unwrap();
    db.initialize().unwrap();
    let store = LatStore::new(db, EmptyComputationLibrary, MaxTupleLatLibrary(3));
    let mut key = "first".to_string();
    assert!(store.lattice_lookup(&key).unwrap().is_none());
    assert_eq!(vec![1, 2, 0], store.lattice_join(&key, &vec![1, 2, 0], &EmptyContext).unwrap());
    assert_eq!(vec![1, 2, 0], store.lattice_lookup(&key).unwrap().unwrap().0);
    assert_eq!(vec![4, 2, 1], store.lattice_join(&key, &vec![4, 0, 1], &EmptyContext).unwrap());
    assert_eq!(vec![4, 2, 1], store.lattice_lookup(&key).unwrap().unwrap().0);
    
    key = "second".to_string();
    assert!(store.lattice_lookup(&key).unwrap().is_none());
    assert_eq!(vec![1, 0, 1], store.lattice_join(&key, &vec![1, 0, 1], &EmptyContext).unwrap());
    assert_eq!(vec![1, 0, 1], store.lattice_lookup(&key).unwrap().unwrap().0);
    assert_eq!(vec![1, 2, 3], store.lattice_join(&key, &vec![0, 2, 3], &EmptyContext).unwrap());
    assert_eq!(vec![1, 2, 3], store.lattice_lookup(&key).unwrap().unwrap().0);

    assert_eq!(vec![4, 2, 1], store.lattice_lookup(&"first".to_string()).unwrap().unwrap().0);
}

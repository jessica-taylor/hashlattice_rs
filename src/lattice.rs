use std::collections::{BTreeSet, BTreeMap};

use serde::{Serialize, Deserialize, de::DeserializeOwned};

// function from D to semilattice
pub trait SemiL : Send + Sync {

    type Elem : Eq + Ord + Clone + Send + Sync + Serialize + DeserializeOwned;

    fn is_elem(&self, e: &Self::Elem) -> bool;

    fn join(&self, a: &Self::Elem, b: &Self::Elem) -> Self::Elem;

    // laws:
    //   assume self.is_elem(a), self.is_elem(b), self.is_elem(c)
    //   self.join(a, a) = a
    //   self.join(a, b) = self.join(b, a)
    //   self.join(a, self.join(b, c)) = self.join(self.join(a, b), c)

    fn bottom(&self) -> Self::Elem;

    // laws:
    //   self.is_elem(self.bottom(d))
    //   self.join(a, self.bottom(d)) = a
    
    fn leq(&self, a: &Self::Elem, b: &Self::Elem) -> bool {
        self.join(a, b) == *b
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Serialize, Deserialize)]
enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<L1 : SemiL, L2: SemiL> SemiL for Either<L1, L2> {
    type Elem = Either<L1::Elem, L2::Elem>;

    fn is_elem(&self, e: &Self::Elem) -> bool {
        match (self, e) {
            (Either::Left(l1), Either::Left(e)) => l1.is_elem(e),
            (Either::Right(l2), Either::Right(e)) => l2.is_elem(e),
            _ => false,
        }
    }

    fn join(&self, a: &Self::Elem, b: &Self::Elem) -> Self::Elem {
        match (self, a, b) {
            (Either::Left(l1), Either::Left(a), Either::Left(b)) => Either::Left(l1.join(a, b)),
            (Either::Right(l2), Either::Right(a), Either::Right(b)) => Either::Right(l2.join(a, b)),
            _ => panic!("join: not an element"),
        }
    }

    fn bottom(&self) -> Self::Elem {
        match self {
            Either::Left(l1) => Either::Left(l1.bottom()),
            Either::Right(l2) => Either::Right(l2.bottom()),
        }
    }
}

// function from D to semilattice fibration
pub trait SemiLFibration<L : SemiL> : Send + Sync {
    type Lat : SemiL;

    fn lattice(&self, lat: &L, x: &L::Elem) -> Self::Lat;

    fn transport(&self, lat: &L, x: &L::Elem, y: &L::Elem, a: <Self::Lat as SemiL>::Elem) -> <Self::Lat as SemiL>::Elem;

    // laws:
    //   assume lat.is_elem(x), lat.is_elem(y), lat.is_elem(z)
    //   assume lat.leq(x, y), lat.leq(y, z)
    //   assume self.lattice(lat, x).is_elem(a),
    //          self.lattice(lat, x).is_elem(b)
    //
    //   self.transport(lat, x, x, a) = a
    //   self.transport(lat, x, y, self.transport(lat, x, z, a)) = self.transport(lat, x, z, self.transport(lat, y, z, a))
    //   self.transport(x, y, self.lattice(lat, x).bottom()) = self.lattice(lat, y).bottom()
    //   self.transport(lat, x, y, self.lattice(lat, x).join(a, b))
    //     = self.lattice(lat, y).join(
    //         self.transport(lat, x, y, a), self.transport(lat, x, y, b))
}

pub trait SemiLUniverse<L: SemiL> : Send + Sync + Sized {
    type Key : Eq + Ord + Clone + Send + Sync + Serialize + DeserializeOwned;

    type Spec : SemiLUniverseSpec<L, Self>;

    type Fib : SemiLFibration<Self::Spec>;

    fn fibration(&self, lat: &L, key: &Self::Key, spec: &Self::Spec) -> Self::Fib;
}

pub trait SemiLUniverseSpec<L: SemiL, U: SemiLUniverse<L, Spec = Self>> : SemiL + Sized {

    fn base_elem(&self, lat: &L) -> L::Elem;

    fn elem_at(&self, lat: &L, key: &U::Key) -> <<U::Fib as SemiLFibration<Self>>::Lat as SemiL>::Elem;
}


pub trait SemiLMultiverse<L: SemiL, U: SemiLUniverse<Self::MultiSpec>> : Send + Sync + Sized {
    type MultiKey : Eq + Ord + Clone + Send + Sync + Serialize + DeserializeOwned;

    type MultiSpec : SemiLMultiverseSpec<L, U, Self>;

    fn universe(&self, lat: &L, key: &Self::MultiKey, spec: &Self::MultiSpec) -> U;
}

pub trait SemiLMultiverseSpec<L: SemiL, U: SemiLUniverse<Self>, M: SemiLMultiverse<L, U, MultiSpec = Self>> : SemiL + Sized {

    fn base_elem(&self, lat: &L) -> L::Elem;

    fn universe_at(&self, lat: &L, mkey: &M::MultiKey) -> U;
}


{-# OPTIONS --cubical --guardedness #-}

module deps where

open import Agda.Builtin.Unit
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Data.Empty
open import Data.Vec using (Vec)
open import Data.List using (List; []; _∷_; length)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false; not; if_then_else_) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything public
open import Relation.Nullary using (¬_)

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Base using (_×_) public

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspec : ∀ {a} {A : Set a} (x : A) → Singleton x
inspec x = x with≡ refl

iff : Type → Type → Type
iff P Q = (P → Q) × (Q → P)

-- record PartialOrder ℓ : Type (lsuc ℓ) where
--   field
--     elᵖ : Type ℓ
--     leqᵖ : elᵖ → elᵖ → Type
-- 
--   _≤ᵖ_ : elᵖ → elᵖ → Type
--   _≤ᵖ_ = leqᵖ
-- 
--   field
--     leq-propᵖ : {x y : elᵖ} → isProp (x ≤ᵖ y)
--     reflᵖ : {x : elᵖ} → x ≤ᵖ x
--     transᵖ : {x y z : elᵖ} → x ≤ᵖ y → y ≤ᵖ z → x ≤ᵖ z
--     antisymmᵖ : {x y : elᵖ} → x ≤ᵖ y → y ≤ᵖ x → x ≡ y

-- open PartialOrder

data Comparison : Type where
  LT : Comparison
  EQ : Comparison
  GT : Comparison

negate-cmp : Comparison → Comparison
negate-cmp LT = GT
negate-cmp EQ = EQ
negate-cmp GT = LT

record TotalOrder ℓ : Type (lsuc ℓ) where
  field
    elᵗ : Type ℓ
    compareᵗ : elᵗ → elᵗ → Comparison
    reflᵗ : {x : elᵗ} → compareᵗ x x ≡ EQ
    anticommᵗ : {x y : elᵗ} → compareᵗ x y ≡ negate-cmp (compareᵗ y x)
    is-eqᵗ : {x y : elᵗ} → compareᵗ x y ≡ EQ → x ≡ y
    transᵗ : {x y z : elᵗ} → compareᵗ x y ≡ LT → compareᵗ y z ≡ LT → compareᵗ x z ≡ LT


open TotalOrder

inspec-compareᵗ : (K : TotalOrder lzero) → (x : elᵗ K) → (y : elᵗ K) → Σ Comparison (λ c → compareᵗ K x y ≡ c)
inspec-compareᵗ K x y with inspec (compareᵗ K x y)
... | c with≡ eq = (c , eq)

list-member : {K : Type} → K → List K → Type
list-member _ [] = ⊥
list-member x (k ∷ ks) = x ≡ k ⊎ list-member x ks

is-fin-pfun : {K V : Type} → (K → Maybe V) → Type
is-fin-pfun {K = K} f = Σ (List K) (λ elems → (k : K) → iff (¬ (f k ≡ nothing)) (list-member k elems))

map-pfun : {K V1 V2 : Type} → (V1 → V2) → (K → Maybe V1) → (K → Maybe V2)
map-pfun f pf k with pf k
... | nothing = nothing
... | just v = just (f v)

pfun-subset-domain : {K V1 V2 : Type} → (K → Maybe V1) → (K → Maybe V2) → Type
pfun-subset-domain {K = K} f g = (k : K) → g k ≡ nothing → f k ≡ nothing

pfun-eq-domain : {K V1 V2 : Type} → (K → Maybe V1) → (K → Maybe V2) → Type
pfun-eq-domain {K = K} f g = (k : K) → iff (f k ≡ nothing) (g k ≡ nothing)

pfun-domain : {K V : Type} → (K → Maybe V) → (K → Maybe Unit)
pfun-domain = map-pfun (λ _ → tt)

pset-union : {K : Type} → (K → Maybe Unit) → (K → Maybe Unit) → (K → Maybe Unit)
pset-union f g k with f k | g k
... | nothing | nothing = nothing
... | _ | _ = just tt

pfun-union : {K V : Type} → (V → V → V) → (K → Maybe V) → (K → Maybe V) → (K → Maybe V)
pfun-union inner f g k with f k | g k
... | nothing | nothing = nothing
... | just x | nothing = just x
... | nothing | just y = just y
... | just x | just y = just (inner x y)

pfun-intersection : {K V1 V2 V3 : Type} → (V1 → V2 → V3) → (K → Maybe V1) → (K → Maybe V2) → (K → Maybe V3)
pfun-intersection inner f g k with f k | g k
... | just x | just y = just (inner x y)
... | _ | _ = nothing

pfun-intersection-right : {K V1 V2 : Type} → (K → Maybe V1) → (K → Maybe V2) → (K → Maybe V2)
pfun-intersection-right = pfun-intersection (λ x y → y)


-- pfun-union-right : {K V : Type} → (K → Maybe V) → (K → Maybe V) → (


  
-- lt-first : (K : TotalOrder lzero) → elᵗ K → List (elᵗ K) → Type
-- lt-first K k [] = Unit
-- lt-first K k (k' ∷ _) = compareᵗ K k k' ≡ LT
-- 
-- is-strictly-sorted : (K : TotalOrder lzero) → List (elᵗ K) → Type
-- is-strictly-sorted _ [] = Unit
-- is-strictly-sorted K (k ∷ ks) = lt-first K k ks × is-strictly-sorted K ks
-- 
-- 
-- SortList : TotalOrder lzero → Type
-- SortList K = Σ (List (elᵗ K)) (is-strictly-sorted K)
-- 
-- merge-lists : (K : TotalOrder lzero) → List (elᵗ K) → List (elᵗ K) → List (elᵗ K)
-- merge-lists _ [] ks = ks
-- merge-lists _ ks [] = ks
-- merge-lists K all1@(k1 ∷ ks1) all2@(k2 ∷ ks2) with compareᵗ K k1 k2 | merge-lists K all1 ks2
-- ... | EQ | _ = k1 ∷ merge-lists K ks1 ks2
-- ... | LT | _ = k1 ∷ merge-lists K ks1 all2
-- ... | GT | rest = k2 ∷ rest
-- 
-- lt-both-lt-merge : {K : TotalOrder lzero} → (k : elᵗ K) → (ks1 ks2 : List (elᵗ K)) → lt-first K k ks1 → lt-first K k ks2 → lt-first K k (merge-lists K ks1 ks2)
-- lt-both-lt-merge k [] _ _ k<ks2 = k<ks2
-- lt-both-lt-merge k (_ ∷ _) [] k<ks1 _ = k<ks1
-- lt-both-lt-merge {K = K} k (k1 ∷ ks1) (k2 ∷ ks2) k<k1 k<k2 with compareᵗ K k1 k2
-- ... | EQ = k<k1
-- ... | LT = k<k1
-- ... | GT = k<k2
-- 
-- 
-- merge-lists-sorted : {K : TotalOrder lzero} → (ks1 : List (elᵗ K)) → (ks2 : List (elᵗ K)) → is-strictly-sorted K ks1 → is-strictly-sorted K ks2 → is-strictly-sorted K (merge-lists K ks1 ks2)
-- merge-lists-sorted [] _ _ ks2-sorted = ks2-sorted
-- merge-lists-sorted (_ ∷ _) [] ks1-sorted _ = ks1-sorted
-- merge-lists-sorted {K = K} (k1 ∷ ks1) (k2 ∷ ks2) (k1<ks1 , ks1-sorted) (k2<ks2 , ks2-sorted) with compareᵗ K k1 k2 | inspect (compareᵗ K k1) k2 | merge-lists-sorted (k1 ∷ ks1) ks2 (k1<ks1 , ks1-sorted) ks2-sorted
-- ... | EQ | [ k1=k2 ]ᵢ | _ = lt-both-lt-merge k1 ks1 ks2 k1<ks1 (transport (cong (λ x → lt-first K x ks2) (sym (is-eqᵗ K k1=k2))) k2<ks2) , merge-lists-sorted ks1 ks2 ks1-sorted ks2-sorted
-- ... | LT | [ k1<k2 ]ᵢ | _ = lt-both-lt-merge k1 ks1 (k2 ∷ ks2) k1<ks1 k1<k2 , merge-lists-sorted ks1 (k2 ∷ ks2) ks1-sorted (k2<ks2 , ks2-sorted)
-- ... | GT | [ k1>k2 ]ᵢ | rest = lt-both-lt-merge k2 (k1 ∷ ks1) ks2 (anticommᵗ K ∙ cong negate-cmp k1>k2) k2<ks2 , rest
-- 
-- merge-comm : {K : TotalOrder lzero} → (ks1 ks2 : List (elᵗ K)) → merge-lists K ks1 ks2 ≡ merge-lists K ks2 ks1
-- merge-comm [] (_ ∷ _) = refl
-- merge-comm (_ ∷ _) [] = refl
-- merge-comm {K = K} (k1 ∷ ks1) (k2 ∷ ks2) with compareᵗ K k1 k2 | inspect (compareᵗ K k1) k2 | compareᵗ K k2 k1 | inspect (compareᵗ K k2) k1 | merge-comm (k1 ∷ ks1) ks2
-- ... | EQ | [ k1=k2 ]ᵢ | EQ | _ | _ = cong₂ (_∷_) (is-eqᵗ K k1=k2) (merge-comm ks1 ks2)
-- ... | LT | [ k1<k2 ]ᵢ | GT | _ | _ = cong (_∷_ k1) (merge-comm ks1 (k2 ∷ ks2))
-- ... | GT | [ k1>k2 ]ᵢ | LT | _ | rest = cong (_∷_ k2) rest
-- 
-- union-sort-lists : {K : TotalOrder lzero} → SortList K → SortList K → SortList K
-- union-sort-lists {K = K} (ks1 , ks1-sorted) (ks2 , ks2-sorted) =
--   (merge-lists K ks1 ks2 , merge-lists-sorted ks1 ks2 ks1-sorted ks2-sorted)
-- 
-- 
-- merge-includes-left : (K : TotalOrder lzero) → (ks1 ks2 : List (elᵗ K)) → (k : elᵗ K) → list-member k ks1 → list-member k (merge-lists K ks1 ks2)
-- merge-includes-left _ [] _ _ bot = ⊥-elim bot
-- merge-includes-left _ (_ ∷ _) [] _ in1 = in1
-- merge-includes-left K (k1 ∷ ks1) (k2 ∷ ks2) k in1 with compareᵗ K k1 k2 | in1 | merge-includes-left K (k1 ∷ ks1) ks2 k in1
-- ... | EQ | inj₁ k=k1 | _ = inj₁ k=k1
-- ... | EQ | inj₂ k∈ | _ = inj₂ (merge-includes-left K ks1 ks2 k k∈)
-- ... | LT | inj₁ k=k1 | _ = inj₁ k=k1
-- ... | LT | inj₂ k∈ | _ = inj₂ (merge-includes-left K ks1 (k2 ∷ ks2) k k∈)
-- ... | GT | _ | rest = inj₂ rest (k1<ks1 , ks1-sorted) (k2<ks2 , ks2-sorted) 
-- 
-- merge-includes-right : (K : TotalOrder lzero) → (ks1 ks2 : List (elᵗ K)) → (k : elᵗ K) → list-member k ks2 → list-member k (merge-lists K ks1 ks2)
-- merge-includes-right K ks1 ks2 k in1 =
--   transport (cong (list-member k) (merge-comm ks2 ks1)) (merge-includes-left K ks2 ks1 k in1)
-- 
-- SortMap : {K : TotalOrder lzero} → SortList K → Type → Type
-- SortMap {K = K} ks V = (k : elᵗ K) → list-member k (fst ks) → V

-- value-subvec : {K : TotalOrder lzero} {V : Type} → (ks1 : SortList K) → (ks2 : SortList K) → Vec V (length (fst (union-sort-lists ks1 ks2))) → Vec V (length (fst ks1))
-- value-subvec ks1 ks2 = 

-- record SortMap (K : TotalOrder lzero) (V : Type) : Type where
--   field
--     listᵐ : SortList K
--     valuesᵐ : Vector V (length listᵐ)

-- data SortMap (K : TotalOrder lzero) (V : Type) : Type
-- is-next-key : {K : TotalOrder lzero} {V : Type} → SortMap K V → elᵗ K → Type
-- 
-- data SortMap K V where
--   sm-empty : SortMap K V
--   sm-rcons : (butlast : SortMap K V) → (k : elᵗ K) → is-next-key butlast k → V → SortMap K V
-- 
-- is-next-key sm-empty _ = Unit
-- is-next-key {K = K} (sm-rcons _ k _ _) k' = leqᵗ K k k' → ⊥
-- 
-- SortList : TotalOrder lzero → Type
-- SortList K = SortMap K Unit
-- 
-- map-sm : {K : TotalOrder lzero} {V1 V2 : Type} → (V1 → V2) → SortMap K V1 → SortMap K V2
-- map-sm _ sm-empty = sm-empty
-- map-sm f (sm-rcons sm-empty k k-next v) = sm-rcons sm-empty k k-next (f v)
-- map-sm f (sm-rcons butlast@(sm-rcons _ _ _ _) k k-next v) = sm-rcons (map-sm f butlast) k k-next (f v)
-- 
-- sm-same-keys : {K : TotalOrder lzero} {V1 V2 : Type} → SortMap K V1 → SortMap K V2 → Type
-- sm-same-keys sm-empty sm-empty = Unit
-- sm-same-keys (sm-rcons _ _ _ _) sm-empty = ⊥
-- sm-same-keys sm-empty (sm-rcons _ _ _ _) = ⊥
-- sm-same-keys (sm-rcons butlast1 k1 _ _) (sm-rcons butlast2 k2 _ _) =
--   (k1 ≡ k2) × sm-same-keys butlast1 butlast2


-- SortMapOfList : {K : TotalOrder lzero} → SortList K → Type → Type
-- SortMapOfList ks V = Σ (SortMap K V)


record DepGraph : Type₁ where
  field
    keyᵍ : TotalOrder lzero
    valueᵍ : Type
    bottomᵍ : elᵗ keyᵍ → valueᵍ
    depsᵍ : elᵗ keyᵍ → valueᵍ → elᵗ keyᵍ → Maybe Unit
    deps-finᵍ : (k : elᵗ keyᵍ) → (v : valueᵍ) → is-fin-pfun (depsᵍ k v)
    is-elemᵍ : (k : elᵗ keyᵍ) → (v : valueᵍ) → (d : elᵗ keyᵍ → Maybe valueᵍ) → pfun-subset-domain (depsᵍ k v) d → Type
    compareᵍ : (k : elᵗ keyᵍ) → (v1 v2 : valueᵍ) → (d : elᵗ keyᵍ → Maybe valueᵍ) →
      (v1-deps : pfun-subset-domain (depsᵍ k v1) d) → (v2-deps : pfun-subset-domain (depsᵍ k v2) d) →
      is-elemᵍ k v1 d v1-deps → is-elemᵍ k v2 d v2-deps → Comparison
    transportᵍ : (k : elᵗ keyᵍ) → (v : valueᵍ) → (d1 d2 : elᵗ keyᵍ → Maybe valueᵍ) → (d1-deps : pfun-subset-domain (depsᵍ k v) d1) → pfun-subset-domain (depsᵍ k v) d2 →
      is-elemᵍ k v d1 d1-deps → valueᵍ
    -- let A, B(a : A) be total orders
    -- transport takes a₁ ≤ a₂, b : B(a₁), produces B(a₂)
    -- we consider transport2 to take (a₁, b), a₂ and produce (a₂, transport(a₁, a₂, b))
    -- the condition is that transport2 must be monotonic on its first argument
    -- where the ordering on pairs is lexicographic
    -- this condition states:
    -- if we have a₁ < a₁' < a₂, then transport(a₁, a₂, b) ≤ transport(a₁', a₂, b)
    -- if we have a₁ < a₂, b ≤ b' : B(a₁), then transport(a₁, a₂, b) ≤ transport(a₁, a₂, b')
    -- problem: it makes tr kinda redundant? handles bottom wrong?
    -- we could make an arbitrary function into a monotonic version of itself by:
    -- g(x) = max(x' ≤ x) f(x)
    -- however, computing the max may be difficult
    -- an insight! a monotonic function can be represented as a map from the original set to an equivalence class!
    -- suppose A, B are total orders
    -- if f : A -> B is monotonic, then we can construct a function g : B → Set(A) splitting B into equivalence classes
    -- then, consider f' : A → Codomain(g) which maps an A to the set containing its B
    -- then, f is monotonic, with Codomain(g) ordered by the corresponding b values
    -- issue: not all B values are in cod(f)
    -- ok, idea: a value in a₂ is a pair (a₁ ≤ a₂: A, b : B(a))
    -- basically representing transporting tr(a₁, a₂, b)
    -- to compare two values (a₁, b₁), (a₁', b₁'), we compare them using the ordering of max(a₁, a₁')
    -- this is so transport preserves orderings.
    -- so, for each a₂, we need to compare it to values (a₁ ≤ a₂, B(a₁))
    -- in a way that preserves the orderings on the (a₁ ≤ a₂, B(a₁)) values implied by lower a₂
    -- also...we can collapse some of the orderings on those values with equivalence classes!
    -- basically, we're promoting an order by collapsing adjacent elements and inserting new ones in some places.
    -- main condition we need is transitivity
    -- if we have b₁ at level a₁, b₂ at level a₂, b₃ at level a₃,
    -- and b₁ < b₂ at a₂,
    -- then we can't have b₁ < b₃ < b₁ at level a₃.
    -- hmm... what if we map each b₃ value to 2 value at level a₂ that are ``adjacent''?
    -- and also give a set of a₂ ranges that are collapsed?
    -- equivalently: we give a set of equivalence classes over a₂ as ranges.
    -- then, we assign to each b₃ value, either an equivalence class, or a pair of adjacent ones, or an endpoint.
    -- we could also provide an equivalence class (disjoint with the other ones and each b₃) that is mapped to ⊥.

    bottom-no-deps : (k d : elᵗ keyᵍ) → depsᵍ k (bottomᵍ k) d ≡ nothing
    bottom-is-elem : (k : elᵗ keyᵍ) → is-elemᵍ k (bottomᵍ k) (λ _ → nothing) (λ d _ → bottom-no-deps k d)

data BoundaryElem {ℓ : Level} (O : TotalOrder ℓ) : Type ℓ where
  before : elᵗ O → BoundaryElem O
  after : elᵗ O → BoundaryElem O

record DepTotalOrder {ℓ : Level} (O : TotalOrder ℓ) : Type (lsuc ℓ) where
  field
    new-ordᵈ : elᵗ O → TotalOrder ℓ
    boundaries : {o₁ o₂ : elᵗ O} → compareᵗ O o₁ o₂ ≡ LT → elᵗ (new-ordᵈ o₂) × List (BoundaryElem (new-ordᵈ o₁) × elᵗ (new-ordᵈ o₂)) -- ascending
    -- hmm.. it's hard with 2d boundaries. we basically need Pareto frontiers.
    -- consider the semilattice homomorphisms from a semilattice S to {0, 1}.
    -- we decide on a set of values to map to 0 and a set to map to 1
    -- such that, if a ≤ b, then we can't have f(a) = 1, f(b) = 0
    -- this can be the condition for being > or ≥ some b₃ value.
    -- hmm... suppose S is A × B where A and B are total orders.
    -- then, given a : A, we can find the min b value for which f(a, b) = 1
    -- this minimum must be anti-monotonic in a. but we already have the theory for that!
    -- if we have a monotonic function from A to B, we can represent that by its graph
    -- and, can query the graph
    -- basically, suppose we have A₁..Aₙ, B
    -- let f be a monotonic function from A₁...Aₙ → B
    -- we can say this is a monotonic function from A₁..Aₙ, -B → {0, 1}
    -- which says whether f(a₁...aₙ) ≥ b
    -- so, wlog, assume B = {0, 1}
    -- now: the monotonic functions from unit to B are either 0 or 1
    -- the monotonic functions from A₁ to B are represented by a minimum A₁
    -- the monotonic functions from A₁, A₂ to B are represented by an anti-monotonic function from A₁ to the minimum A₂
    --   we can represent this as a function from a threshold A₂ value to the minimum A₁ exceeding that threshold
    -- the monotonic functions from A₁, A₂, A₃ to B are represented by an anti-monotonic function from A₁, A₂ to the minimum A₃
    --   we can represent this as a function from a threshold A₃ value to an anti-monotonic function from A₁ to A₂
    --     we can represent this as a (monotonic? antimonotonic?) function from a threshold A₂ value to the minimum A₁
    --       we can represent this as a order preserving mapping from A₂ onto A₁
    -- hmm, let's try again
    -- let's *not* assume B is {0, 1}
    -- now, functions from unit to B are just a B value
    -- monotonic functions from A₁ to B are segmentations of A₁ into intervals and placements of B with respect to those intervals
    -- monotonic functions from A₁, A₂ to B
    --   we could segment (A₁, A₂) into Pareto frontiers?
    --     a specific Pareto frontier is an anti-monotonic function from A₁ to A₂
    --     but, we need to assign these Pareto frontiers anti-monotonically in B
    --  here's an approach: we could map each B value to a set of rectangles (⊥, ⊥), (a₁, a₂)
    --   such that, for f(a₁', a₂') ≥ b, it is sufficient for a₁' < a₁, a₂' < b₂
    --   basically, union the rectangles
    --   and, we also union with rectangles of lower b
    --   showing f(a₁, a₂) ≥ b is now a search problem for a rectangle...
    --  umm, let's just 80/20 it. tr is id, except it does an is_elem check, and maps to bottom if it's not an elem.
    --  if we want collapsing, we factor the semilattice, and some semilattices in the factorization get collapsed!
    --  wait...now do we need is_elem to be monotonic or smth???
    --  the only effect of tr is to map some elems to bottom...
    --  we want to avoid a₁ < a₂ < a₃ : A, b₁ : B, tr(a₁, a₂, b₁) = ⊥, tr(a₁, a₃, b₁) ≠ bot
    -- hmm... what if we first construct the product A × B, then filter on a joint is_elem check???
    -- problem: our is_elem check has to be monotonic...
    -- our is_elem checks a B given an A. since we check the A using is_elem for A.
    -- so we get the same issue as before... dang
    -- basically: to ensure is_elem is monotonic, we set a maximum A × B value
    -- assume for now that is_elem is always true of A
    -- then, for a given A value, we get the minimum B value that passes is_elem. the minimum must be anti-monotonic in A.
    -- as an alternative to a dependent semilattice of B(a) on A:
    -- we construct a family of semilattices B(a) for each A
    -- then, we do a semilattice computation where we first find the best a : A and then find the best b : B(a)
    -- problem: this doesn't have transports...
    -- but, maybe we can special case this???
    -- semilattices are equipped with a computation that finds the lower bound value???
    -- this gives us auto updates!!
    -- hmm...pretty nice...




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

record SemiLat {ℓ} (S : Type ℓ) : Type ℓ where
  field
    joinˢ : S → S → S
    bottomˢ : S → S → S

  leqˢ : S → S → Type ℓ
  leqˢ x y = joinˢ x y ≡ y

open SemiLat

record DepSemiLat {ℓ₁ ℓ₂} {S : Type ℓ₁} (L : SemiLat S) (D : S → Type ℓ₂) : Type (ℓ₁ ⊔ ℓ₂) where
  field
    semiᵈ : (x : S) → SemiLat (D x)
    trᵈ : {x y : S} → leqˢ L x y → D x → D y

open DepSemiLat

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


  


record DepGraph : Type₁ where
  field
    keyᵍ : TotalOrder lzero
    valueᵍ : Type
    is-elemᵍ : (k : elᵗ keyᵍ) → (elᵗ keyᵍ → Maybe valueᵍ) → (v : valueᵍ) → Type

  elemᵍ : elᵗ keyᵍ → (elᵗ keyᵍ → Maybe valueᵍ) → Type
  elemᵍ k ctx = Σ valueᵍ (is-elemᵍ k ctx)

  field
    semilᵍ : (k : elᵗ keyᵍ) → (ctx : elᵗ keyᵍ → Maybe valueᵍ) → SemiLat (elemᵍ k ctx)
    transportᵍ : (k : elᵗ keyᵍ) → (elᵗ keyᵍ → Maybe valueᵍ) → (elᵗ keyᵍ → Maybe valueᵍ) → valueᵍ → Maybe valueᵍ

  Key<ᵍ : elᵗ keyᵍ → Type
  Key<ᵍ k = Σ (elᵗ keyᵍ) (λ k' → compareᵗ keyᵍ k' k ≡ LT)

  Key≤ᵍ : elᵗ keyᵍ → Type
  Key≤ᵍ k = Σ (elᵗ keyᵍ) (λ k' → ¬ (compareᵗ keyᵍ k' k ≡ GT))

  Ctx<ᵍ : elᵗ keyᵍ → Type
  Ctx<ᵍ k = Key<ᵍ k → Maybe valueᵍ

  Ctx≤ᵍ : elᵗ keyᵍ → Type
  Ctx≤ᵍ k = Key≤ᵍ k → Maybe valueᵍ


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

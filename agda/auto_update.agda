
{-# OPTIONS --cubical --guardedness #-}
module auto_update where



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

data Comparison : Type where
  LT : Comparison
  EQ : Comparison
  GT : Comparison

negate-cmp : Comparison → Comparison
negate-cmp LT = GT
negate-cmp EQ = EQ
negate-cmp GT = LT


record Ordinal ℓ : Type (lsuc ℓ) where
  field
    elᵗ : Type ℓ
    compareᵗ : elᵗ → elᵗ → Comparison
    reflᵗ : {x : elᵗ} → compareᵗ x x ≡ EQ
    anticommᵗ : {x y : elᵗ} → compareᵗ x y ≡ negate-cmp (compareᵗ y x)
    is-eqᵗ : {x y : elᵗ} → compareᵗ x y ≡ EQ → x ≡ y
    transᵗ : {x y z : elᵗ} → compareᵗ x y ≡ LT → compareᵗ y z ≡ LT → compareᵗ x z ≡ LT

  type<ᵗ : elᵗ → Type ℓ
  type<ᵗ k = Σ elᵗ (λ k' → compareᵗ k' k ≡ LT)

  field
    inductionᵗ : (P : elᵗ → Type) → ((k : elᵗ) → ((k' : type<ᵗ k) → P (fst k')) → P k) → (k : elᵗ) → P k



open Ordinal

record SemiLat : Type₁ where
  field
    elˢ : Type
    joinˢ : elˢ → elˢ → elˢ 
    bottomˢ : elˢ

open SemiLat
  

record SemiLatGraph (K : Ordinal lzero) : Type₁ where
  field
    semilᵍ : (k : elᵗ K) → SemiLat
    boundᵍ : (k : elᵗ K) → ((k' : type<ᵗ K k) → elˢ (semilᵍ (fst k'))) → elˢ (semilᵍ k)
    -- bound is monotonic??

  Mappingᵍ : Type
  Mappingᵍ = (k : elᵗ K) → elˢ (semilᵍ k)

  Mapping<ᵍ : elᵗ K → Type
  Mapping<ᵍ k = (k' : type<ᵗ K k) → elˢ (semilᵍ (fst k'))

  weaken-mappingᵍ : (k1 k2 : elᵗ K) → compareᵗ K k1 k2 ≡ LT → Mapping<ᵍ k2 → Mapping<ᵍ k1
  weaken-mappingᵍ k1 k2 k1<k2 map2 (k' , k'<k1) = map2 (k' , transᵗ K k'<k1 k1<k2)

  update<ᵍ : (k : elᵗ K) → Mapping<ᵍ k → Mapping<ᵍ k
  update<ᵍ k map k' = joinˢ (semilᵍ (fst k')) (map k') (boundᵍ (fst k') (weaken-mappingᵍ (fst k') k (snd k') map))

  join-boundᵍ : Mappingᵍ → (k : elᵗ K) → Mapping<ᵍ k → elˢ (semilᵍ k)
  join-boundᵍ map k map< = joinˢ (semilᵍ k) (map k) (boundᵍ k map<)

  updateᵍ : Mappingᵍ → Mappingᵍ
  updateᵍ map =
    let inner = inductionᵗ K Mapping<ᵍ (λ k ind-assm k' → join-boundᵍ map (fst k') (ind-assm k'))
    in λ k → join-boundᵍ map k (inner k) 

  
    

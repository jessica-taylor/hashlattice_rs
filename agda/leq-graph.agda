
{-# OPTIONS --cubical --guardedness #-}

module leq-graph where

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


record PartialOrder {ℓ} (S : Type ℓ) : Type (ℓ ⊔ (lsuc lzero)) where
  field
    leqᵖ : S → S → Type
    leq-propᵖ : (x y : S) → isProp (leqᵖ x y)
    reflᵖ : (x : S) → leqᵖ x x
    transᵖ : (x y z : S) → leqᵖ x y → leqᵖ y z → leqᵖ x z
    antisymmᵖ : (x y : S) → leqᵖ x y → leqᵖ y x → x ≡ y

open PartialOrder

record TotalOrder {ℓ} (S : Type ℓ) : Type (ℓ ⊔ (lsuc lzero)) where
  field
    partialᵗ : PartialOrder S

  leqᵗ = leqᵖ partialᵗ

  field
    completeᵗ : (x y : S) → leqᵗ x y ⊎ leqᵗ y x

open TotalOrder

record SemiLat {ℓ} (S : Type ℓ) : Type (ℓ ⊔ (lsuc lzero)) where
  field
    partialˢ : PartialOrder S
    joinˢ : S → S → S

  leqˢ = leqᵖ partialˢ

  field
    left≤joinˢ : (x y : S) → leqˢ x (joinˢ x y)
    right≤joinˢ : (x y : S) → leqˢ y (joinˢ x y)
    join-lubˢ : (x y z : S) → leqˢ x z → leqˢ y z → leqˢ (joinˢ x y) z

open SemiLat

is-or-nothing : {ℓ : Level} {S : Type ℓ} → (S → Type) → Maybe S → Type
is-or-nothing _ nothing = Unit
is-or-nothing pred (just x) = pred x

record SemiGraph {ℓ} {K : Type ℓ} (KT : TotalOrder K) (V : Type ℓ) : Type (ℓ ⊔ (lsuc lzero)) where
  field
    is-elemᵍ : K → (K → Maybe V) → V → Type

  maybe-is-elemᵍ : K → (K → Maybe V) → Maybe V → Type
  maybe-is-elemᵍ k ctx = is-or-nothing (is-elemᵍ k ctx)

  elemᵍ : K → (K → Maybe V) → Type ℓ
  elemᵍ k ctx = Σ V (is-elemᵍ k ctx)

  field
    semilᵍ : (k : K) → (ctx : K → Maybe V) → SemiLat (elemᵍ k ctx)
    trᵍ : (k : K) → (ctx1 ctx2 : K → Maybe V) → V → V

  is-ctxᵍ : (K → Maybe V) → Type ℓ
  is-ctxᵍ ctx = (k : K) → maybe-is-elemᵍ k ctx (ctx k)

  -- ctx-leqᵍ : (K → Maybe V) → (K → Maybe V) → Type ℓ
  -- ctx-leqᵍ ctx1 ctx2 = (k : K) → {!leqˢ (semilᵍ k ctx2) ? (!}


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

data UnitL ℓ : Set ℓ where
  <> : UnitL ℓ

data BotL ℓ : Set ℓ where

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspec : ∀ {a} {A : Set a} (x : A) → Singleton x
inspec x = x with≡ refl

record PartialOrder {ℓ₁} ℓ₂ (S : Type ℓ₁) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
  field
    leqᵖ : S → S → Type ℓ₂
    leq-propᵖ : (x y : S) → isProp (leqᵖ x y)
    reflᵖ : (x : S) → leqᵖ x x
    transᵖ : (x y z : S) → leqᵖ x y → leqᵖ y z → leqᵖ x z
    antisymmᵖ : (x y : S) → leqᵖ x y → leqᵖ y x → x ≡ y

open PartialOrder

record TotalOrder {ℓ₁} ℓ₂ (S : Type ℓ₁) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
  field
    partialᵗ : PartialOrder ℓ₂ S

  leqᵗ = leqᵖ partialᵗ

  field
    completeᵗ : (x y : S) → leqᵗ x y ⊎ leqᵗ y x

open TotalOrder

record SemiLat {ℓ₁} ℓ₂ (S : Type ℓ₁) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
  field
    partialˢ : PartialOrder ℓ₂ S
    joinˢ : S → S → S

  leqˢ = leqᵖ partialˢ

  field
    left≤joinˢ : (x y : S) → leqˢ x (joinˢ x y)
    right≤joinˢ : (x y : S) → leqˢ y (joinˢ x y)
    join-lubˢ : (x y z : S) → leqˢ x z → leqˢ y z → leqˢ (joinˢ x y) z

open SemiLat

is-or-nothing : {ℓ₁ ℓ₂ : Level} {S : Type ℓ₁} → (S → Type ℓ₂) → Maybe S → Type ℓ₂
is-or-nothing {ℓ₂ = ℓ₂} _ nothing = UnitL ℓ₂
is-or-nothing pred (just x) = pred x

record SemiGraph {ℓ₁ ℓ₂} {K : Type ℓ₁} (KT : TotalOrder ℓ₂ K) (V : Type ℓ₁) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where
  field
    is-elemᵍ : K → (K → Maybe V) → V → Type ℓ₂
    leqᵍ : K → (K → Maybe V) → V → V → Type ℓ₂
    joinᵍ : K → (K → Maybe V) → V → V → V
    bottomᵍ : K → (K → Maybe V) → V
    trᵍ : (k : K) → (K → Maybe V) → (K → Maybe V) → V → V

  maybe-is-elemᵍ : K → (K → Maybe V) → Maybe V → Type ℓ₂
  maybe-is-elemᵍ k ctx = is-or-nothing (is-elemᵍ k ctx)

  elemᵍ : K → (K → Maybe V) → Type (ℓ₁ ⊔ ℓ₂)
  elemᵍ k ctx = Σ V (is-elemᵍ k ctx)

  maybe-leqᵍ : (k : K) → (ctx : K → Maybe V) → Maybe V → Maybe V → Type ℓ₂
  maybe-leqᵍ _ _ nothing nothing = UnitL ℓ₂
  maybe-leqᵍ _ _ nothing (just _) = UnitL ℓ₂
  maybe-leqᵍ _ _ (just _) nothing = BotL ℓ₂
  maybe-leqᵍ k ctx (just x) (just y) = leqᵍ k ctx x y

  maybe-trᵍ : K → (K → Maybe V) → (K → Maybe V) → Maybe V → Maybe V
  maybe-trᵍ _ _ _ nothing = nothing
  maybe-trᵍ k ctx1 ctx2 (just v) = just (trᵍ k ctx1 ctx2 v)

  is-ctxᵍ : (K → Maybe V) → Type (ℓ₁ ⊔ ℓ₂)
  is-ctxᵍ ctx = (k : K) → maybe-is-elemᵍ k ctx (ctx k)

  Ctxᵍ : Type (ℓ₁ ⊔ ℓ₂)
  Ctxᵍ = Σ (K → Maybe V) is-ctxᵍ

  ctx-lookupᵍ : (k : K) → (ctx : Ctxᵍ) → Maybe (elemᵍ k (fst ctx))
  ctx-lookupᵍ k (ctx , is-ctx) with ctx k | is-ctx k
  ... | nothing | _ = nothing
  ... | just v | v-is = just (v , v-is)

  ctx≤ᵍ : (K → Maybe V) → (K → Maybe V) → Type (ℓ₁ ⊔ ℓ₂)
  ctx≤ᵍ ctx1 ctx2 = (k : K) → maybe-leqᵍ k ctx2 (maybe-trᵍ k ctx1 ctx2 (ctx1 k)) (ctx2 k)


open SemiGraph

record IsSemiGraph {ℓ₁ ℓ₂} {K : Type ℓ₁} {KT : TotalOrder ℓ₂ K} {V : Type ℓ₁} (G : SemiGraph KT V) : Type (ℓ₁ ⊔ (lsuc ℓ₂)) where

  field
    leq-propⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y : elemᵍ G k (fst ctx)) → isProp (leqᵍ G k (fst ctx) (fst x) (fst y))
    leq-reflⁱ : (k : K) → (ctx : Ctxᵍ G) → (x : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (fst x) (fst x)
    leq-transⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y z : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (fst x) (fst y) → leqᵍ G k (fst ctx) (fst y) (fst z) → leqᵍ G k (fst ctx) (fst x) (fst z)
    leq-antisymmⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (fst x) (fst y) → leqᵍ G k (fst ctx) (fst y) (fst x) → x ≡ y
    join-is-elemⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y : elemᵍ G k (fst ctx)) → is-elemᵍ G k (fst ctx) (joinᵍ G k (fst ctx) (fst x) (fst y))
    bot-is-elemⁱ : (k : K) → (ctx : Ctxᵍ G) → is-elemᵍ G k (fst ctx) (bottomᵍ G k (fst ctx))
    left≤joinⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (fst x) (joinᵍ G k (fst ctx) (fst x) (fst y))
    right≤joinⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (fst y) (joinᵍ G k (fst ctx) (fst x) (fst y))
    join-lubⁱ : (k : K) → (ctx : Ctxᵍ G) → (x y z : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (fst x) (fst z) → leqᵍ G k (fst ctx) (fst y) (fst z) → leqᵍ G k (fst ctx) (joinᵍ G k (fst ctx) (fst x) (fst y)) (fst z)
    bot≤ⁱ : (k : K) → (ctx : Ctxᵍ G) → (x : elemᵍ G k (fst ctx)) → leqᵍ G k (fst ctx) (bottomᵍ G k (fst ctx)) (fst x)
    tr-is-elemⁱ : (k : K) → (ctx1 ctx2 : Ctxᵍ G) → ctx≤ᵍ G (fst ctx1) (fst ctx2) → (x : elemᵍ G k (fst ctx1)) → is-elemᵍ G k (fst ctx2) (trᵍ G k (fst ctx1) (fst ctx2) (fst x))
    tr-reflⁱ : (k : K) → (ctx : Ctxᵍ G) → (x : elemᵍ G k (fst ctx)) → trᵍ G k (fst ctx) (fst ctx) (fst x) ≡ fst x
    tr-transⁱ : (k : K) → (ctx1 ctx2 ctx3 : Ctxᵍ G) → ctx≤ᵍ G (fst ctx1) (fst ctx2) → ctx≤ᵍ G (fst ctx2) (fst ctx3) → (x : elemᵍ G k (fst ctx1)) → trᵍ G k (fst ctx2) (fst ctx3) (trᵍ G k (fst ctx1) (fst ctx2) (fst x)) ≡ trᵍ G k (fst ctx1) (fst ctx3) (fst x)

  joinⁱ : (k : K) → (ctx : Ctxᵍ G) → elemᵍ G k (fst ctx) → elemᵍ G k (fst ctx) → elemᵍ G k (fst ctx)
  joinⁱ k ctx x y = (joinᵍ G k (fst ctx) (fst x) (fst y) , join-is-elemⁱ k ctx x y)

  bottomⁱ : (k : K) → (ctx : Ctxᵍ G) → elemᵍ G k (fst ctx)
  bottomⁱ k ctx = (bottomᵍ G k (fst ctx) , bot-is-elemⁱ k ctx)

  ctx≤-reflⁱ : (ctx : Ctxᵍ G) → ctx≤ᵍ G (fst ctx) (fst ctx)
  ctx≤-reflⁱ ctx k with fst ctx k | inspect (fst ctx) k | snd ctx k
  ... | nothing | [ _ ]ᵢ | _ = <>
  ... | just v | [ _ ]ᵢ | v-elem = transport (cong (λ v' → leqᵍ G k (fst ctx) v' v) (sym (tr-reflⁱ k ctx (v , v-elem)))) (leq-reflⁱ k ctx (v , v-elem))
  


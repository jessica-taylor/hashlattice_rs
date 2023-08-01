{-# OPTIONS --cubical --guardedness #-}

module fromtot where

open import Agda.Builtin.Unit
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Data.Empty
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false; not; if_then_else_) public
open import Data.Maybe using (Maybe; just; nothing) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything public
open import Relation.Nullary using (¬_)

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Base using (_×_) public


record SemiLat (S : Type) : Type where
  field
    joinˢ : S → S → S
    botˢ : S
    idemˢ : (x : S) → joinˢ x x ≡ x
    commˢ : (x y : S) → joinˢ x y ≡ joinˢ y x
    assocˢ : (x y z : S) → joinˢ (joinˢ x y) z ≡ joinˢ x (joinˢ y z)
    bot-idˢ : (x : S) → joinˢ botˢ x ≡ x

  leq-transˢ : (x y z : S) → joinˢ x y ≡ y → joinˢ y z ≡ z → joinˢ x z ≡ z
  leq-transˢ x y z x≤y y≤z =
    joinˢ x z
    ≡⟨ cong (joinˢ x) (sym y≤z) ⟩
    joinˢ x (joinˢ y z)
    ≡⟨ sym (assocˢ x y z) ⟩
    joinˢ (joinˢ x y) z
    ≡⟨ cong (λ a → joinˢ a z) x≤y ⟩
    joinˢ y z
    ≡⟨ y≤z ⟩
    z
    ∎

open SemiLat

record IsSemiMor {S1 S2 : Type} (L1 : SemiLat S1) (L2 : SemiLat S2) (f : S1 → S2) : Type where
  field
    joinᵐ : (x y : S1) → f (joinˢ L1 x y) ≡ joinˢ L2 (f x) (f y)
    botᵐ : f (botˢ L1) ≡ botˢ L2

open IsSemiMor

record SemiTot {S : Type} (L : SemiLat S) (D : S → Type) : Type where
  field
    botᵗ : (x : S) → D x
    semi-totᵗ : SemiLat (Σ S D)
    proj1ᵗ : IsSemiMor semi-totᵗ L fst
    bot-idᵗ : (x : S) → (x' : D x) → joinˢ semi-totᵗ (x , botᵗ x) (x , x') ≡ (x , x')

  dep-semilatᵗ : (x : S) → SemiLat (D x)
  joinˢ (dep-semilatᵗ x) a b = transport (cong D (joinᵐ proj1ᵗ (x , a) (x , b) ∙ idemˢ L x)) (snd (joinˢ semi-totᵗ (x , a) (x , b)))
  botˢ (dep-semilatᵗ x) = botᵗ x
  idemˢ (dep-semilatᵗ x) a =
    transport
      (λ i → D ((joinᵐ proj1ᵗ (x , a) (x , a) ∙ idemˢ L x) i))
      (snd (joinˢ semi-totᵗ (x , a) (x , a)))
      ≡⟨ {!!} ⟩
    transport
      (λ i → D ((joinᵐ proj1ᵗ (x , a) (x , a) ∙ idemˢ L x) i))
      (snd (joinˢ semi-totᵗ (x , a) (x , a)))
     ≡⟨ {!!} ⟩ a ∎
    -- transport (cong D (joinᵐ proj1ᵗ (x , a) (x , a) ∙ idemˢ L x)) (snd (joinˢ semi-totᵗ (x , a) (x , a)))
    -- ≡⟨ ? ⟩
    -- snd (joinˢ semi-totᵗ (x , a) (x , a))
    -- ∎
  -- idemˢ (dep-semilatᵗ x) a i = transp (λ j → {!!}) i {!!}

  trᵗ : (x y : S) → joinˢ L x y ≡ y → D x → D y
  trᵗ x y x≤y x' = transport (cong D (joinᵐ proj1ᵗ (x , x') (y , botᵗ y) ∙ x≤y)) (snd (joinˢ semi-totᵗ (x , x') (y , botᵗ y)))

  tr-compᵗ : (x y z : S) → (x≤y : joinˢ L x y ≡ y) → (y≤z : joinˢ L y z ≡ z) → (x' : D x) → trᵗ y z y≤z (trᵗ x y x≤y x') ≡ trᵗ x z (leq-transˢ L x y z x≤y y≤z) x'
  tr-compᵗ x y z x≤y y≤z x' = {!!}


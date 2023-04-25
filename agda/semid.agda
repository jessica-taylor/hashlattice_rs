{-# OPTIONS --cubical --guardedness #-}

open import Agda.Builtin.Unit
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything public

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

Σ-≡-intro :
  ∀ {α}{A : Set α}{B : A → Set α} {a a' : A} {b : B a} {b' : B a'}
  → (Σ (a ≡ a') λ p → PathP (λ i → B (p i)) b b') → (a , b) ≡ (a' , b')

Σ-≡-intro eqs =
  cong₂ (λ c c' → (c , c'))
    (fst eqs)
    (snd eqs)

record SemiL (elˢ : Set) : Set where
  field
    joinˢ : elˢ → elˢ → elˢ
    botˢ : elˢ
    idemˢ : (x : elˢ) → joinˢ x x ≡ x
    commˢ : (x y : elˢ) → joinˢ x y ≡ joinˢ y x
    assocˢ : (x y z : elˢ) → joinˢ (joinˢ x y) z ≡ joinˢ x (joinˢ y z)
    bot-idˢ : (x : elˢ) → joinˢ x botˢ ≡ x

open SemiL

record IsSemiMor {S1 : Set} (L1 : SemiL S1) {S2 : Set} (L2 : SemiL S2) (apᵐ : S1 → S2) : Set where
  field
    pres-botᵐ : apᵐ (botˢ L1) ≡ botˢ L2
    pres-joinᵐ : (x y : S1) → apᵐ (joinˢ L1 x y) ≡ joinˢ L2 (apᵐ x) (apᵐ y)

open IsSemiMor

record SemiLᵈ {S : Set} (L : SemiL S) (D : S → Set) : Set where
  field
    tot-semiᵈ : SemiL (Σ S D)
    morᵈ : IsSemiMor tot-semiᵈ L fst
    botᵈ : (x : S) → D x
    bot-idᵈ : (x : S) (y : D x) → joinˢ tot-semiᵈ (x , y) (x , botᵈ x) ≡ (x , y)

  joinᵈ : (x : S) → (x' : D x) → (y : S) → (y' : D y) → D (joinˢ L x y)
  joinᵈ x x' y y' = transport (cong D (pres-joinᵐ morᵈ (x , x') (y , y'))) (snd (joinˢ tot-semiᵈ (x , x') (y , y')))

-- record SemiL2ᵈ {S : Set} (L : SemiL S) (D : S → Set) : Set where
--   field
--     join2ᵈ : (x : S) → (x' : D x) → (y : S) → (y' : D y) → D (joinˢ L x y)
--     bot2ᵈ : (x : S) → D x
--     bot-id2ᵈ : (x : S) → (x' : D x) → join2ᵈ x x' x (bot2ᵈ x) ≡ x'
    

-- quotient : {S : Set} {L : SemiL S} {DS : S → Set} → (DL : SemiL (Σ S DS)) → IsSemiMor DL L (λ (x : (Σ S DS)) → fst x) → S → Set


-- record SemiLᵈ : Set₁ where
--   field
--     semilᵈ : SemiL
--     elᵈ : elˢ semilᵈ → Set
--     joinᵈ : (a : elˢ semilᵈ) → elᵈ a → (b : elˢ semilᵈ) → elᵈ b → elᵈ (joinˢ semilᵈ a b)
--     botᵈ : (a : elˢ semilᵈ) → elᵈ a
--     idemᵈ : (a : elˢ semilᵈ) → (a' : elᵈ a) → transport (cong elᵈ (idemˢ semilᵈ a)) (joinᵈ a a' a a') ≡ a'
--     commᵈ : (a : elˢ semilᵈ) → (a' : elᵈ a) → (b : elˢ semilᵈ) → (b' : elᵈ b) → transport (cong elᵈ (commˢ semilᵈ a b)) (joinᵈ a a' b b') ≡ joinᵈ b b' a a'
--     assocᵈ : (a : elˢ semilᵈ) → (a' : elᵈ a) → (b : elˢ semilᵈ) → (b' : elᵈ b) → (c : elˢ semilᵈ) → (c' : elᵈ c) →
--       transport (cong elᵈ (assocˢ semilᵈ a b c)) (joinᵈ (joinˢ semilᵈ a b) (joinᵈ a a' b b') c c') ≡ joinᵈ a a' (joinˢ semilᵈ b c) (joinᵈ b b' c c')
--     bot-idᵈ : (a : elˢ semilᵈ) → (a' : elᵈ a) → transport (cong elᵈ (idemˢ semilᵈ a)) (joinᵈ a a' a (botᵈ a)) ≡ a'
-- 
-- open SemiLᵈ
-- 
-- semil-tot : SemiLᵈ → SemiL
-- elˢ (semil-tot sd) = Σ (elˢ (semilᵈ sd)) (elᵈ sd)
-- joinˢ (semil-tot sd) (a , a') (b , b') = (joinˢ (semilᵈ sd) a b , joinᵈ sd a a' b b')
-- idemˢ (semil-tot sd) (a , a') = Σ-≡-intro (idemˢ (semilᵈ sd) a , (λ i → transport {!!} a'))


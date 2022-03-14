{-# OPTIONS --cubical --guardedness #-}

module semilattice where

open import Agda.Builtin.Unit
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything renaming (cong to ap) public

open import Cubical.Data.Nat
open import Cubical.Data.Sigma


private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

f : {A : Set ℓ} → A → A
f x = x

Σ-≡-intro :
  ∀ {α}{A : Set α}{B : A → Set α} {a a' : A} {b : B a} {b' : B a'}
  → (Σ (a ≡ a') λ p → PathP (λ i → B (p i)) b b') → (a , b) ≡ (a' , b')

Σ-≡-intro eqs =
  cong₂ (λ c c' → (c , c'))
    (fst eqs)
    (snd eqs)


record SemiL ℓ : Type (lsuc ℓ) where
  field
    elˢ : Type ℓ
    _∨ˢ_ : elˢ → elˢ → elˢ
    commˢ : (x y : elˢ) → x ∨ˢ y ≡ y ∨ˢ x
    assocˢ : (x y z : elˢ) → (x ∨ˢ y) ∨ˢ z ≡ x ∨ˢ (y ∨ˢ z)
    idemˢ : (x : elˢ) → x ∨ˢ x ≡ x

  joinˢ : elˢ → elˢ → elˢ
  joinˢ = _∨ˢ_

  compeqˢ : (x y z : elˢ) → (x ∨ˢ y) ∨ˢ (x ∨ˢ (y ∨ˢ z)) ≡ x ∨ˢ (y ∨ˢ z)
  compeqˢ x y z =
    (x ∨ˢ y) ∨ˢ (x ∨ˢ (y ∨ˢ z))
    ≡⟨ ap (joinˢ (x ∨ˢ y)) (assocˢ x y z ⁻¹) ⟩
    (x ∨ˢ y) ∨ˢ ((x ∨ˢ y) ∨ˢ z)
    ≡⟨ assocˢ (x ∨ˢ y) (x ∨ˢ y) z ⁻¹ ⟩
    ((x ∨ˢ y) ∨ˢ (x ∨ˢ y)) ∨ˢ z
    ≡⟨ ap (λ a → a ∨ˢ z) (idemˢ (x ∨ˢ y)) ⟩
    (x ∨ˢ y) ∨ˢ z
    ≡⟨ assocˢ x y z ⟩
    x ∨ˢ (y ∨ˢ z)
    ∎

open SemiL

onepointˢ : SemiL lzero
elˢ onepointˢ = ⊤
_∨ˢ_ onepointˢ tt tt = tt
commˢ onepointˢ x y = λ i → tt
assocˢ onepointˢ x y z = λ i → tt
idemˢ onepointˢ x = refl

record SemiLᵈ (L : SemiL ℓ₁) ℓ₂ : Type (ℓ₁ ⊔ lsuc ℓ₂) where
  field
    semilᵈ : elˢ L → SemiL ℓ₂

    trᵈ : {x y : elˢ L} (x' : elˢ (semilᵈ x)) → elˢ (semilᵈ (joinˢ L x y))

    idᵈ : {x : elˢ L} (x' : elˢ (semilᵈ x)) → PathP (λ i → elˢ (semilᵈ (idemˢ L x i))) (trᵈ x') (x')

    compᵈ : {x y z : elˢ L} (x' : elˢ (semilᵈ x)) →
      PathP (λ i → elˢ (semilᵈ (compeqˢ L x y z i))) (trᵈ (trᵈ x')) (trᵈ x')

    distrᵈ : {x y : elˢ L} (x' x'' : elˢ (semilᵈ x)) →
      trᵈ (joinˢ (semilᵈ x) x' x'') ≡ joinˢ (semilᵈ (joinˢ L x y)) (trᵈ x') (trᵈ x'')

  trcommᵈ : {x y : elˢ L} → elˢ (semilᵈ (joinˢ L x y)) → elˢ (semilᵈ (joinˢ L y x))
  trcommᵈ {x} {y} = transport (ap (λ e → elˢ (semilᵈ e)) (commˢ L x y))

  trrᵈ : {x y : elˢ L} (y' : elˢ (semilᵈ y)) → elˢ (semilᵈ (joinˢ L x y))
  trrᵈ = trcommᵈ ∘ trᵈ

open SemiLᵈ

Σ-SemiL : (ℒ : SemiL ℓ₁) (ℳ : SemiLᵈ ℒ ℓ₂) → SemiL (ℓ₁ ⊔ ℓ₂)
elˢ (Σ-SemiL ℒ ℳ) = Σ (elˢ ℒ) (elˢ ∘ semilᵈ ℳ)
_∨ˢ_ (Σ-SemiL ℒ ℳ) (x , α) (y , β) = joinˢ ℒ x y , joinˢ (semilᵈ ℳ (joinˢ ℒ x y)) (trᵈ ℳ α) (trcommᵈ ℳ (trᵈ ℳ β)) 
commˢ (Σ-SemiL ℒ ℳ) = {!!}
assocˢ (Σ-SemiL ℒ ℳ) = {!!}
idemˢ (Σ-SemiL ℒ ℳ) = {!!}

record TyStr ℓ : Type (lsuc ℓ) where
  coinductive
  field
    ty : Type ℓ
    ex : ty → TyStr ℓ

open TyStr

semil-u' : (ℒ : SemiL ℓ) → TyStr (lsuc ℓ)
ty (semil-u' {ℓ} ℒ) = SemiLᵈ ℒ ℓ
ex (semil-u' ℒ) ℳ = semil-u' (Σ-SemiL ℒ ℳ)

semil-u : TyStr (lsuc lzero)
semil-u = semil-u' onepointˢ

record sec (𝒯 : TyStr ℓ) : Type ℓ where
  coinductive
  field
    headˢ : ty 𝒯
    tailˢ : sec (ex 𝒯 headˢ)

open sec

record ∞-el' {ℒ : SemiL ℓ} (σ : sec (semil-u' ℒ)) (x : elˢ ℒ) : Type ℓ where
  coinductive
  field
    headᵉ : elˢ (semilᵈ (headˢ σ) x)
    tailᵉ : ∞-el' (tailˢ σ) (x , headᵉ)

open ∞-el'

∞-el : sec semil-u → Type lzero
∞-el σ = ∞-el' σ tt

join-∞ : {ℒ : SemiL ℓ} (σ : sec (semil-u' ℒ)) (x y : elˢ ℒ) → ∞-el' σ x → ∞-el' σ y → ∞-el' σ (joinˢ ℒ x y)
headᵉ (join-∞ {ℒ = ℒ} σ x y a b) = joinˢ (semilᵈ (headˢ σ) (joinˢ ℒ x y)) (trᵈ (headˢ σ) (headᵉ a)) (trrᵈ (headˢ σ) (headᵉ b))
tailᵉ (join-∞ σ x y a b) = join-∞ (tailˢ σ) (x , headᵉ a) (y , headᵉ b) (tailᵉ a) (tailᵉ b)

Σ-SemiL-∞ : sec semil-u → SemiL lzero
elˢ (Σ-SemiL-∞ σ) = ∞-el σ
_∨ˢ_ (Σ-SemiL-∞ σ) x y = join-∞ σ tt tt x y  
assocˢ (Σ-SemiL-∞ σ) = {!!}
commˢ (Σ-SemiL-∞ σ) = {!!}
idemˢ (Σ-SemiL-∞ σ) = {!!}

{-
  trcomm-twiceᵈ : {x y : elˢ L} (x' : elˢ (semilᵈ (joinˢ L x y))) → trcommᵈ (trcommᵈ x') ≡ x'
  trcomm-twiceᵈ = refl

  fullᵈ : SemiL (ℓ₁ ⊔ ℓ₂){!!} 
  fullᵈ =
    let el : Type (ℓ₁ ⊔ ℓ₂)
        el = Σ (elˢ L) (λ x → elˢ (semilᵈ x))

        join : el → el → el
        join x y = (joinˢ L (fst x) (fst y), joinˢ (semilᵈ (joinˢ L (fst x) (fst y))) (trᵈ (snd x)) (trcommᵈ (trᵈ (snd y))))

        -- comm : (x y : el) → join x y ‌‌≡ join y x
        -- comm x y = Σ-≡-intro (
        --   commˢ L x y ,  
        --   joinˢ (semilᵈ (joinˢ L (fst x) (fst y))) (trᵈ (snd x)) (tr2ᵈ (snd y))
        --   ≡⟨ commˢ (semilᵈ (joinˢ (fst x) (fst y))) (trᵈ (snd x)) (tr2ᵈ (snd y)) ⟩
        --   joinˢ (semilᵈ (joinˢ L (fst x) (fst y))) (tr2ᵈ (snd y)) (trᵈ (snd x))
        --   ≡⟨   ⟩
        --   ∎
          
          
    in record {
        elˢ = el;
        _∨ˢ_ = join
    }
-}


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

data Ord : Set where
  zeroOrd : Ord
  sucOrd  : Ord → Ord
  limOrd  : (ℕ → Ord) → Ord

data predᵒ : Ord → Ord → Type where
  pred-suc : (x : Ord) → predᵒ x (sucOrd x)
  pred-lim : (f : ℕ → Ord) → (n : ℕ) → predᵒ (f n) (limOrd f)

data _≤ᵒ_ : Ord → Ord → Type
data _<ᵒ_ : Ord → Ord → Type

data _≤ᵒ_ where
  self-≤ : (x : Ord) → x ≤ᵒ x
  pred-≤ : {x y : Ord} → x <ᵒ y → x ≤ᵒ y

data _<ᵒ_ where
  pred-< : {x y z : Ord} → x ≤ᵒ y → predᵒ y z → x <ᵒ z

Ord≤ : Ord → Type
Ord≤ ub = Σ Ord (λ o → o ≤ᵒ ub)

Ord< : Ord → Type
Ord< ub = Σ Ord (λ o → o <ᵒ ub)

ord-is-<maybe : Maybe Ord → Ord → Type
ord-is-<maybe nothing _ = Unit
ord-is-<maybe (just ub) o = o <ᵒ ub

Ord<Maybe : Maybe Ord → Type
Ord<Maybe m = Σ Ord (ord-is-<maybe m)

Ord<-to-≤ : {k : Ord} → Ord< k → Ord≤ k
Ord<-to-≤ (k' , k'<k) = (k' , pred-≤ k'<k)

≤-transᵒ : {x y z : Ord} → x ≤ᵒ y → y ≤ᵒ z → x ≤ᵒ z
<-trans-rᵒ : {x y z : Ord} → x ≤ᵒ y → y <ᵒ z → x <ᵒ z

≤-transᵒ x≤y (self-≤ _) = x≤y
≤-transᵒ x≤y (pred-≤ y<z) = pred-≤ (<-trans-rᵒ x≤y y<z)

<-trans-rᵒ x≤y (pred-< y≤z' zpred) = pred-< (≤-transᵒ x≤y y≤z') zpred

<-trans-lᵒ : {x y z : Ord} → x <ᵒ y → y ≤ᵒ z → x <ᵒ z
<-trans-lᵒ x<y (self-≤ _) = x<y
<-trans-lᵒ x<y (pred-≤ y<z) = <-trans-rᵒ (pred-≤ x<y) y<z

<-suc-to-≤ᵒ : {x y : Ord} → x <ᵒ sucOrd y → x ≤ᵒ y
<-suc-to-≤ᵒ (pred-< x≤sy' predy) with predy
... | (pred-suc _) = x≤sy'

not-<0ᵒ : {x : Ord} → x <ᵒ zeroOrd → ⊥
not-<0ᵒ (pred-< _ pred) with pred
... | ()

induction1ᵒ : (P : Ord → Type) → P zeroOrd →
                                 ((k : Ord) → P k → P (sucOrd k)) →
                                 ((f : ℕ → Ord) → ((n : ℕ) → P (f n)) → P (limOrd f)) →
                                 (k : Ord) → P k
induction1ᵒ _ pz _ _ zeroOrd = pz
induction1ᵒ P pz ps pl (sucOrd k) = ps k (induction1ᵒ P pz ps pl k)
induction1ᵒ P pz ps pl (limOrd f) = pl f (λ n → induction1ᵒ P pz ps pl (f n))

induction2ᵒ : (P : Ord → Type) → ((k : Ord) → ((k' : Ord< k) → P (fst k')) → P k) → (k : Ord) → P k
induction2ᵒ P ind k = induction1ᵒ (λ k → (k' : Ord) → k' ≤ᵒ k → P k')
  (λ k' k'≤0 → ind k' (λ (k'' , k''<k') → ⊥-elim (not-<0ᵒ (<-trans-lᵒ k''<k' k'≤0))))
  (λ k ind-assm k' k'≤sk → ind k' (λ (k'' , k''<k') → ind-assm k'' (<-suc-to-≤ᵒ (<-trans-lᵒ k''<k' k'≤sk)))  )
  (λ f ind-assm k' k'≤lf → ind k' (λ (k'' , k''<k') → case <-trans-lᵒ k''<k' k'≤lf of
    λ {(pred-< k''≤fn (pred-lim _ n)) → ind-assm n k'' k''≤fn}))
  k k (self-≤ k)

record SemiLat : Type₁ where
  field
    elˢ : Type
    joinˢ : elˢ → elˢ → elˢ 
    bottomˢ : elˢ

open SemiLat

maybe-≤ : {S : Type} → (S → S → Type) → Maybe S → Maybe S → Type
maybe-≤ _ nothing _ = Unit
maybe-≤ _ (just _) nothing = ⊥
maybe-≤ ≤ (just x) (just y) = ≤ x y

maybe-join : {S : Type} → (S → S → S) → Maybe S → Maybe S → Maybe S
maybe-join _ nothing y = y
maybe-join _ x nothing = x
maybe-join join (just x) (just y) = just (join x y)

maybe->>= : {A B : Type} → Maybe A → (A → Maybe B) → Maybe B
maybe->>= nothing _ = nothing
maybe->>= (just x) f = f x
  

record SemiLatGraph : Type₁ where
  field
    valueᵍ : Type
    max-ordᵍ : Ord


  Ctx<ᵍ : Ord → Type
  Ctx<ᵍ k = Ord< k → Maybe valueᵍ

  Ctxᵍ : Type
  Ctxᵍ = Ctx<ᵍ max-ordᵍ


  Ctx≤ᵍ : Ord → Type
  Ctx≤ᵍ k = Ord≤ k → Maybe valueᵍ

  field
    is-elemᵍ : (k : Ord) → Ctx<ᵍ k → valueᵍ → Type
    joinᵍ : (k : Ord) → Ctx<ᵍ k → valueᵍ → valueᵍ → valueᵍ
    transportᵍ : (k : Ord) → Ctx<ᵍ k → Ctx<ᵍ k → valueᵍ → Maybe valueᵍ

  ctx-filter-<ᵍ : {k : Ord} → (k' : Ord< k) → Ctx<ᵍ k → Ctx<ᵍ (fst k')
  ctx-filter-<ᵍ k' ctx k'' = ctx ((fst k'' , <-trans-lᵒ (snd k'') (pred-≤ (snd k'))))

  maybe-is-elemᵍ : (k : Ord) → Ctx<ᵍ k → Maybe valueᵍ → Type
  maybe-is-elemᵍ k ctx v = case v of
    λ {nothing → Unit;
       (just v) → is-elemᵍ k ctx v}
  

  ctx-are-elemsᵍ : {ub : Ord} → Ctx<ᵍ ub → Type
  ctx-are-elemsᵍ {ub} ctx = (k : Ord< ub) → maybe-is-elemᵍ (fst k) (ctx-filter-<ᵍ k ctx) (ctx k)

  ctx-≤ᵍ : {ub : Ord} → Ctx<ᵍ ub → Ctx<ᵍ ub → Type
  ctx-≤ᵍ {ub} ctx1 ctx2 = (k : Ord< ub) →
    let v1' = maybe->>= (ctx1 k) (transportᵍ (fst k) (ctx-filter-<ᵍ k ctx1) (ctx-filter-<ᵍ k ctx2))
    in maybe-≤ (λ v1 v2 → joinᵍ (fst k) (ctx-filter-<ᵍ k ctx2) v1 v2 ≡ v2) v1' (ctx2 k)

  field
    join-is-elemᵍ : (k : Ord) → (ctx : Ctx<ᵍ k) → ctx-are-elemsᵍ ctx →
      (v1 v2 : valueᵍ) → is-elemᵍ k ctx v1 → is-elemᵍ k ctx v2 →
      is-elemᵍ k ctx (joinᵍ k ctx v1 v2)

    join-commutᵍ : (k : Ord) → (ctx : Ctx<ᵍ k) → ctx-are-elemsᵍ ctx →
      (v1 v2 : valueᵍ) → is-elemᵍ k ctx v1 → is-elemᵍ k ctx v2 →
      joinᵍ k ctx v1 v2 ≡ joinᵍ k ctx v2 v1

    join-assocᵍ : (k : Ord) → (ctx : Ctx<ᵍ k) → ctx-are-elemsᵍ ctx →
      (v1 v2 v3 : valueᵍ) → is-elemᵍ k ctx v1 → is-elemᵍ k ctx v2 → is-elemᵍ k ctx v3 →
      joinᵍ k ctx (joinᵍ k ctx v1 v2) v3 ≡ joinᵍ k ctx v1 (joinᵍ k ctx v2 v3)

    join-idemᵍ : (k : Ord) → (ctx : Ctx<ᵍ k) → ctx-are-elemsᵍ ctx →
      (v : valueᵍ) → is-elemᵍ k ctx v →
      joinᵍ k ctx v v ≡ v

    tr-is-elemᵍ : (k : Ord) → (ctx1 ctx2 : Ctx<ᵍ k) →
      ctx-are-elemsᵍ ctx1 → ctx-are-elemsᵍ ctx2 → ctx-≤ᵍ ctx1 ctx2 →
      (v : valueᵍ) → is-elemᵍ k ctx1 v →
      case transportᵍ k ctx1 ctx2 v of
        λ { nothing → Unit;
            (just v') → is-elemᵍ k ctx2 v' }

    tr-idᵍ : (k : Ord) → (ctx : Ctx<ᵍ k) →
      ctx-are-elemsᵍ ctx →
      (v : valueᵍ) → is-elemᵍ k ctx v →
      transportᵍ k ctx ctx v ≡ just v

    tr-transᵍ : (k : Ord) → (ctx1 ctx2 ctx3 : Ctx<ᵍ k) →
      ctx-are-elemsᵍ ctx1 → ctx-are-elemsᵍ ctx2 → ctx-are-elemsᵍ ctx3 →
      ctx-≤ᵍ ctx1 ctx2 → ctx-≤ᵍ ctx2 ctx3 →
      (v : valueᵍ) → is-elemᵍ k ctx1 v →
      case transportᵍ k ctx1 ctx2 v of
        λ { nothing → nothing ≡ transportᵍ k ctx1 ctx3 v;
            (just v') → transportᵍ k ctx2 ctx3 v' ≡ transportᵍ k ctx1 ctx3 v }

  ctx-join-indstepᵍ : {ub : Ord} → (k : Ord< ub) → Ctx<ᵍ ub → Ctx<ᵍ ub → (Ctx<ᵍ (fst k) → Ctx<ᵍ (fst k) → Ctx<ᵍ (fst k)) → Maybe valueᵍ
  ctx-join-indstepᵍ k ctx1 ctx2 join-ind =
    let ctx1' = ctx-filter-<ᵍ k ctx1
        ctx2' = ctx-filter-<ᵍ k ctx2
        ctx-j = join-ind ctx1' ctx2'
    in maybe-join (joinᵍ (fst k) ctx-j)
         (maybe->>= (ctx1 k) (transportᵍ (fst k) ctx1' ctx-j))
         (maybe->>= (ctx2 k) (transportᵍ (fst k) ctx2' ctx-j))
    

  ctx-joinᵍ : (k : Ord) → Ctx<ᵍ k → Ctx<ᵍ k → Ctx<ᵍ k
  ctx-joinᵍ = induction2ᵒ (λ k → Ctx<ᵍ k → Ctx<ᵍ k → Ctx<ᵍ k)
    (λ k ind ctx1 ctx2 k' → ctx-join-indstepᵍ k' ctx1 ctx2 (ind k'))

  ctx-join-are-elemsᵍ : (k : Ord) → (ctx1 ctx2 : Ctx<ᵍ k) →
    ctx-are-elemsᵍ ctx1 → ctx-are-elemsᵍ ctx2 → ctx-are-elemsᵍ (ctx-joinᵍ k ctx1 ctx2)
  ctx-join-are-elemsᵍ = induction2ᵒ (λ k → (ctx1 ctx2 : Ctx<ᵍ k) → ctx-are-elemsᵍ ctx1 → ctx-are-elemsᵍ ctx2 → ctx-are-elemsᵍ (ctx-joinᵍ k ctx1 ctx2))
    (λ k ind ctx1 ctx2 ctx1-elems ctx2-elems k' →
      let ctx1' = ctx-filter-<ᵍ k' ctx1
          ctx2' = ctx-filter-<ᵍ k' ctx2
          ctx-j = ctx-joinᵍ (fst k') ctx1' ctx2'
      in {!!})

  -- ctx-join-are-elems : (k : Ord) → (ctx1 ctx2 : Ctx<ᵍ k) → ctx<-are-elemsᵍ (ctx<-joinᵍ k ctx1 ctx2)
  -- ctx-join-are-elems =
  --   let P : Ord → Type
  --       P = (λ k → (ctx1 ctx2 : Ctx<ᵍ k) → ctx<-are-elemsᵍ (ctx<-joinᵍ k ctx1 ctx2))
  --       P' : Ord → Type
  --       P' k = Ctx<ᵍ k → Ctx<ᵍ k → Ctx<ᵍ k
  --       step : (k : Ord) → ((k' : type<ᵒ keyᵍ k) → P' (fst k')) → P' k
  --       step = (λ k ind ctx1 ctx2 k' → ctx-join-indstepᵍ (fst k') (ctx<-to-ctxᵍ ctx1) (ctx<-to-ctxᵍ ctx2) (ind k'))
  --   in inductionᵒ keyᵍ (λ k → (ctx1 ctx2 : Ctx<ᵍ k) → ctx<-are-elemsᵍ (ctx<-joinᵍ k ctx1 ctx2))
  --     (λ k ind ctx1 ctx2 k' →
  --       case ctx<-to-ctxᵍ (ctx<-joinᵍ k ctx1 ctx2) k' return maybe-is-elemᵍ k' {!!} of
  --       λ { nothing → tt;
  --           (just v) → {!!} })
  --       -- let foofoo = induction-eqᵒ keyᵍ P' step k in

  -- ctx-join-are-elems : (ctx1 ctx2 : Ctxᵍ) → ctx-are-elemsᵍ (ctx-joinᵍ ctx1 ctx2)
  -- ctx-join-are-elems ctx1 ctx2 k = {!!}
  
      

  -- elemᵍ : elᵒ keyᵍ → (elᵒ keyᵍ → Maybe valueᵍ) → Type
  -- elemᵍ k ctx = Σ valueᵍ (is-elemᵍ k ctx)

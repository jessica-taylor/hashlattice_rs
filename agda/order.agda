{-# OPTIONS --cubical --guardedness --rewriting #-}

module order where

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


data PrefixFree : Type where
  atomic : PrefixFree
  split : PrefixFree -> PrefixFree -> PrefixFree

data PFString : PrefixFree -> Type where
  pf-empty : PFString atomic
  pf-0 : {pf0 pf1 : PrefixFree} -> PFString pf0 -> PFString (split pf0 pf1)
  pf-1 : {pf0 pf1 : PrefixFree} -> PFString pf1 -> PFString (split pf0 pf1)

data PFPreString : PrefixFree -> Type where
  pfp-empty : {pf : PrefixFree} -> PFPreString pf
  pfp-0 : {pf0 pf1 : PrefixFree} -> PFPreString pf0 -> PFPreString (split pf0 pf1)
  pfp-1 : {pf0 pf1 : PrefixFree} -> PFPreString pf1 -> PFPreString (split pf0 pf1)

pf-negate : PrefixFree -> PrefixFree
pf-negate atomic = atomic
pf-negate (split x y) = split (pf-negate y) (pf-negate x)

pf-str-negate : {pf : PrefixFree} -> PFString pf -> PFString (pf-negate pf)
pf-str-negate pf-empty = pf-empty
pf-str-negate (pf-0 rest) = pf-1 (pf-str-negate rest)
pf-str-negate (pf-1 rest) = pf-0 (pf-str-negate rest)

data Comparison : Type where
  LT : Comparison
  EQ : Comparison
  GT : Comparison

pf-compare : {pf : PrefixFree} -> PFString pf -> PFString pf -> Comparison
pf-compare pf-empty pf-empty = EQ
pf-compare (pf-0 _) (pf-1 _) = LT
pf-compare (pf-1 _) (pf-0 _) = GT
pf-compare (pf-0 x) (pf-0 y) = pf-compare x y
pf-compare (pf-1 x) (pf-1 y) = pf-compare x y

data PFThreshold : PrefixFree -> Type where
  thresh-begin : {pf : PrefixFree} -> PFThreshold pf
  thresh-end : {pf : PrefixFree} -> PFThreshold pf
  thresh-left : {pf0 pf1 : PrefixFree} -> PFThreshold pf0 -> PFThreshold (split pf0 pf1)
  thresh-right : {pf0 pf1 : PrefixFree} -> PFThreshold pf1 -> PFThreshold (split pf0 pf1)

data PFMon : PrefixFree -> PrefixFree -> Type where
  mon-atomic : {pf : PrefixFree} -> PFMon pf atomic
  mon-split : {pf pf0 pf1 : PrefixFree} -> PFThreshold pf -> PFMon pf pf0 -> PFMon pf pf1 -> PFMon pf (split pf0 pf1)

PFThreshold2 : PrefixFree -> PrefixFree -> Type
PFThreshold2 pfx pfy = PFMon (pf-negate pfx) pfy -- todo

-- data PFMon2 : PrefixFree -> PrefixFree -> PrefixFree -> Type where
--   mon2-atomic : {pfx pfy : PrefixFree} -> PFMon pfx pfy atomic


PFTrans : Type
PFTrans = (pf : PrefixFree) -> PFPreString pf -> PFPreString (pf ++ [0]) -> PFPreString (pf ++ [1])

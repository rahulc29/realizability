{-# OPTIONS --cubical #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Relation.Binary.Poset
open import Cubical.Foundations.Powerset

module Realizability.DirectedCompletePartialOrder where

module _ {ℓ ℓ'} (P' : Poset ℓ ℓ') where
  P = P' .fst
  open PosetStr (P' .snd)

  isUpperbound : P → Type _
  isUpperbound p = ∀ x → x ≤ p

  record isSupremum (p : P) : Type (ℓ-max ℓ ℓ') where
    field
      ub : isUpperbound p
      lub : ∀ x → isUpperbound x → p ≤ x

  

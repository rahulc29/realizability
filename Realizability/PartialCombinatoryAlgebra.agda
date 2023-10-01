{-# OPTIONS --cubical #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Realizability.Partiality
open import Realizability.BinaryApplicativeStructure

module Realizability.PartialCombinatoryAlgebra where

record PartialCombinatoryAlgebra {ℓ} (A : Type ℓ) (pas : PartialApplicativeStructure A) : Type ℓ where
  open PartialApplicativeStructure pas
  field
    s : A
    k : A
    kab≡a : ∀ (a b : ♯ A) → (η k) ̇ a ̇ b ≡ a
    sabc≡ac_bc : ∀ a b c → (η s) ̇ a ̇ b ̇ c ≡ (a ̇ c) ̇ (b ̇ c)

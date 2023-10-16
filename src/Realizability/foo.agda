{-# OPTIONS --guarded --cubical #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

record ℙfinal {ℓ} (A : Type ℓ) : Type _ where
  coinductive
  field
    force : ▹ ℙ (ℙfinal A)

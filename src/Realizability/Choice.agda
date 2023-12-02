{-# OPTIONS --cubical #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Functions.Surjection
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

module Realizability.Choice where

Choice : ∀ ℓ ℓ' → Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ'))
Choice ℓ ℓ' = (A : Type ℓ) (B : Type ℓ') (f : A → B) → isSurjection f → ∃[ f' ∈ (B → A) ] section f f'

{-# OPTIONS --cubical #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Realizability.Partiality

module Realizability.BinaryApplicativeStructure where

record PartialApplicativeStructure {ℓ} (A : Type ℓ) : Type ℓ where
  infixl 25 _̇_
  field
    _̇_ : ♯ A → ♯ A → ♯ A


module _ {ℓ} {A : Type ℓ} (pas : PartialApplicativeStructure A) where
  foo : A → ♯ A
  foo a = do
          return a

  bar : ∀ {B : Type ℓ} → A → (A → ♯ B) → ♯ B
  bar a f = do
            answer ← f a
            return answer

  
  

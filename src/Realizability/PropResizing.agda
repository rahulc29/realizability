open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

module Realizability.PropResizing where

-- Formulation of propositional resizing inspired by the corresponding formulation
-- in TypeTopology
-- https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Size.html

copyOf : ∀ {ℓ} → Type ℓ → (ℓ' : Level) → Type _
copyOf {ℓ} X ℓ' = Σ[ copy ∈ Type ℓ' ] X ≃ copy

copy = fst
copyEquiv = snd

propResizing : ∀ ℓ ℓ' → Type _
propResizing ℓ ℓ' = ∀ (X : Type ℓ) → isProp X → copyOf X ℓ'

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

module Realizability.PropResizing where

-- Formulation of propositional resizing inspired by the corresponding formulation
-- in TypeTopology
-- https://www.cs.bham.ac.uk/~mhe/TypeTopology/UF.Size.html

copyOf : ∀ {ℓ} → Type ℓ → (ℓ' : Level) → Type _
copyOf {ℓ} X ℓ' = Σ[ copy ∈ Type ℓ' ] X ≃ copy

copy = fst
copyEquiv = snd

-- We need the principle that TypeTopology calls Ω resizing
-- that the universe of props in a universe 𝓤 has a copy in 𝓤
-- This we call hPropResizing
hPropResizing : ∀ ℓ → Type _
hPropResizing ℓ = copyOf (hProp ℓ) ℓ

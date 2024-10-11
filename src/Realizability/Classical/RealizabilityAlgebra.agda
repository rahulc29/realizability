-- Realizability algebras of Krivine
-- I do not aim to give a complete account of
-- classical realizability but I wanted to experiment
-- with the notion of the realizability algebra.
-- This Agda module is based on Krivine's paper
-- "Realizability algebras : a program to well order ℝ"
-- https://www.irif.fr/~krivine/articles/Well_order.pdf

open import Cubical.Foundations.Prelude

module Realizability.Classical.RealizabilityAlgebra {ℓ ℓ' ℓ''} where

-- Just the definition of a realizability algebra is much more complicated than a combinatory algebra.
-- Thankfully I do not have to delay any notion of partiality since Krivine defines realizability algebras
-- without any notion of partiality.
-- This might not be the best definition in a HoTT setting - but we will probably have to find that out
-- the hard way. 
record RealizabilityAlgebra (Λ : Type ℓ) (Π : Type ℓ') (_⋆_ : Λ → Π → Type ℓ'') : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ''))) where
  infixl 26 _·_
  infixr 25 _↑_
  infix 24 _★_
  field
    isSetΛ : isSet Λ
    isSetΠ : isSet Π
    isSetΛ⋆Π : ∀ l p → isSet (l ⋆ p)
    B C E id K W cc : Λ
    _·_ : Λ → Λ → Λ
    _↑_ : Λ → Π → Π
    _★_ : (l : Λ) → (p : Π) → l ⋆ p
    cont : Π → Λ

module Execution (Λ : Type ℓ) (Π : Type ℓ') (_⋆_ : Λ → Π → Type ℓ'') (ra : RealizabilityAlgebra Λ Π _⋆_) where
  open RealizabilityAlgebra ra
  infix 20 _≺_

  -- An abstract state machine that allows us to execute the programs of a realizability algebra
  -- The reflexive transitive closure of this relation *is* evaluation
  data _≺'_ : {l₁ l₂ : Λ} {p₁ p₂ : Π} → l₁ ⋆ p₁ → l₂ ⋆ p₂ → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'') where
    push : ∀ (ξ η : Λ) (π : Π) → ξ · η ★ π ≺  ξ ★ η ↑ π
    noop : ∀ ξ π → id ★ ξ ↑ π ≺ ξ ★ π
    -- TODO : Complete

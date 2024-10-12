open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude

module Realizability.Tripos.Prealgebra.Predicate {ℓ ℓ' ℓ''} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Tripos.Prealgebra.Predicate.Base {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} ca public
open import Realizability.Tripos.Prealgebra.Predicate.Properties {ℓ' = ℓ'} {ℓ'' = ℓ''} ca public

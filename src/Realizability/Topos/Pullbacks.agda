open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm; λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Fin
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinProduct

module Realizability.Topos.Pullbacks
  {ℓ ℓ' ℓ''} {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥) where

open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Topos.Object {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial 
open import Realizability.Topos.FunctionalRelation {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate renaming (isSetX to isSetPredicateBase)
open PredicateProperties
open Morphism

private
  λ*ComputationRule = `λ*ComputationRule as fefermanStructure
  λ* = `λ* as fefermanStructure

open FunctionalRelation
open PartialEquivalenceRelation


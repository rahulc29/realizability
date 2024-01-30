open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm)
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.FinData renaming (zero to fzero)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

module Realizability.Topos.FunctionalRelation
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  where

open import Realizability.Tripos.Logic.Syntax {ℓ = ℓ'}
open import Realizability.Tripos.Logic.Semantics {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Tripos.Prealgebra.Predicate.Base ca renaming (Predicate to Predicate'; _⊩_ to _pre⊩_)
open import Realizability.Tripos.Prealgebra.Predicate.Properties ca
open import Realizability.Topos.Object {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial 

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate' renaming (isSetX to isSetPredicateBase)
open PredicateProperties
open Morphism

private
  _⊩_ : ∀ a (P : Predicate' {ℓ' = ℓ'} {ℓ'' = ℓ''} Unit*) → Type _
  a ⊩ P = a pre⊩ ∣ P ∣ tt*

record FunctionalRelation (X Y : Type ℓ') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  open PartialEquivalenceRelation
  field
    perX : PartialEquivalenceRelation X
    perY : PartialEquivalenceRelation Y
  _~X_ = perX ._~_
  _~Y_ = perY ._~_

  field
    relation : Predicate (X × Y)

  private
    `X : Sort
    `X = ↑ (X , perX .isSetX)

    `Y : Sort
    `Y = ↑ (Y , perY .isSetX)

    relationSymbol : Vec Sort 3
    relationSymbol = (`X `× `Y) ∷ `X `× `X ∷ `Y `× `Y ∷ []

    relationSymbolInterpretation : RelationInterpretation relationSymbol
    relationSymbolInterpretation fzero = relation
    relationSymbolInterpretation one = _~X_
    relationSymbolInterpretation two = _~Y_

    `relation : Fin 3
    `relation = fzero
    `~X : Fin 3
    `~X = one
    `~Y : Fin 3
    `~Y = two

  module RelationInterpretation = Interpretation relationSymbol relationSymbolInterpretation isNonTrivial
  open RelationInterpretation

  module RelationSoundness = Soundness isNonTrivial relationSymbolInterpretation
  open RelationSoundness

  -- Strictness
  -- If the functional relation holds for x and y then x and y "exist"
  private
    strictnessContext : Context
    strictnessContext = ([] ′ `X) ′ `Y

    x∈strictnessContext : `X ∈ strictnessContext
    x∈strictnessContext = there here

    y∈strictnessContext : `Y ∈ strictnessContext
    y∈strictnessContext = here

    xˢᵗ : Term strictnessContext `X
    xˢᵗ = var x∈strictnessContext

    yˢᵗ : Term strictnessContext `Y
    yˢᵗ = var y∈strictnessContext
  

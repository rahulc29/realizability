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

open PartialEquivalenceRelation

record FunctionalRelation (X Y : Type ℓ') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  field
    perX : PartialEquivalenceRelation X
    perY : PartialEquivalenceRelation Y
  _~X_ = perX ._~_
  _~Y_ = perY ._~_

  field
    relation : Predicate (X × Y)

  `X : Sort
  `X = ↑ (X , perX .isSetX)

  `Y : Sort
  `Y = ↑ (Y , perY .isSetX)

  private
    relationSymbol : Vec Sort 3
    relationSymbol = (`X `× `Y) ∷ `X `× `X ∷ `Y `× `Y ∷ []

    `F : Fin 3
    `F = fzero
    `~X : Fin 3
    `~X = one
    `~Y : Fin 3
    `~Y = two

  open Relational relationSymbol

  module RelationInterpretation' = Interpretation relationSymbol (λ { fzero → relation ; one → _~X_ ; two → _~Y_ }) isNonTrivial
  open RelationInterpretation'

  module RelationSoundness = Soundness {relSym = relationSymbol} isNonTrivial (λ { fzero → relation ; one → _~X_ ; two → _~Y_ })
  open RelationSoundness

  -- # Strictness
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

    -- F : Rel X Y, _~X_ : Rel X X, _~Y_ : Rel Y Y ⊢ F(x ,y) → (x ~X x) ∧ (y ~Y y)
    strictnessPrequantFormula : Formula strictnessContext
    strictnessPrequantFormula = rel `F (xˢᵗ `, yˢᵗ) `→ (rel `~X (xˢᵗ `, xˢᵗ) `∧ rel `~Y (yˢᵗ `, yˢᵗ))

  strictnessFormula : Formula []
  strictnessFormula = `∀ (`∀ strictnessPrequantFormula)

  field
    strictnessWitness : A
    isStrict : strictnessWitness ⊩ ⟦ strictnessFormula ⟧ᶠ

  -- # Relational
  -- The functional relation preserves equality
  -- "Substitutive" might be a better term for this property
  private
    relationalContext : Context
    relationalContext =
      [] ′ `Y ′ `Y ′ `X ′ `X

    x₁∈relationalContext : `X ∈ relationalContext
    x₁∈relationalContext = there here

    x₂∈relationalContext : `X ∈ relationalContext
    x₂∈relationalContext = here

    y₁∈relationalContext : `Y ∈ relationalContext
    y₁∈relationalContext = there (there here)

    y₂∈relationalContext : `Y ∈ relationalContext
    y₂∈relationalContext = there (there (there here))

    x₁ = var x₁∈relationalContext
    x₂ = var x₂∈relationalContext
    y₁ = var y₁∈relationalContext
    y₂ = var y₂∈relationalContext

    relationalPrequantFormula : Formula relationalContext
    relationalPrequantFormula = (rel `F (x₁ `, y₁) `∧ (rel `~X (x₁ `, x₂) `∧ rel `~Y (y₁ `, y₂))) `→ rel `F (x₂ `, y₂)

  relationalFormula : Formula []
  relationalFormula = `∀ (`∀ (`∀ (`∀ relationalPrequantFormula)))

  field
    relationalWitness : A
    isRelational : relationalWitness ⊩ ⟦ relationalFormula ⟧ᶠ

  -- # Single-valued
  -- Self explanatory
  private
    singleValuedContext : Context
    singleValuedContext =
      [] ′ `Y ′ `Y ′ `X

    x∈singleValuedContext : `X ∈ singleValuedContext
    x∈singleValuedContext = here

    y₁∈singleValuedContext : `Y ∈ singleValuedContext
    y₁∈singleValuedContext = there here

    y₂∈singleValuedContext : `Y ∈ singleValuedContext
    y₂∈singleValuedContext = there (there here)

    xˢᵛ = var x∈singleValuedContext
    y₁ˢᵛ = var y₁∈singleValuedContext
    y₂ˢᵛ = var y₂∈singleValuedContext

    singleValuedPrequantFormula : Formula singleValuedContext
    singleValuedPrequantFormula =
      (rel `F (xˢᵛ `, y₁ˢᵛ) `∧ rel `F (xˢᵛ `, y₂ˢᵛ)) `→ rel `~Y (y₁ˢᵛ `, y₂ˢᵛ)

  singleValuedFormula : Formula []
  singleValuedFormula = `∀ (`∀ (`∀ singleValuedPrequantFormula))

  field
    singleValuedWitness : A
    isSingleValued : singleValuedWitness ⊩ ⟦ singleValuedFormula ⟧ᶠ

  -- # Total
  -- For all existent elements in the domain x there is an element in the codomain y
  -- such that F(x, y)
  private
    totalContext : Context
    totalContext =
      [] ′ `X

    x∈totalContext : `X ∈ totalContext
    x∈totalContext = here

    xᵗˡ = var x∈totalContext

    totalPrequantFormula : Formula totalContext
    totalPrequantFormula = rel `~X (xᵗˡ `, xᵗˡ)  `→ `∃ (rel `F (renamingTerm (drop id) xᵗˡ `, var here))

  totalFormula : Formula []
  totalFormula = `∀ totalPrequantFormula

  field
    totalWitness : A
    isTotal : totalWitness ⊩ ⟦ totalFormula ⟧ᶠ  

open FunctionalRelation hiding (`X; `Y)

pointwiseEntailment : ∀ {X Y : Type ℓ'} → FunctionalRelation X Y → FunctionalRelation X Y → Type _
pointwiseEntailment {X} {Y} F G = Σ[ a ∈ A ] (a ⊩ ⟦ entailmentFormula ⟧ᶠ) where
  
  `X : Sort
  `Y : Sort

  `X = ↑ (X , F .perX .isSetX)
  `Y = ↑ (Y , F .perY .isSetX)

  relationSymbols : Vec Sort 2
  relationSymbols = (`X `× `Y) ∷ (`X `× `Y) ∷ []

  `F : Fin 2
  `F = fzero

  `G : Fin 2
  `G = one

  open Relational relationSymbols

  module RelationalInterpretation = Interpretation relationSymbols (λ { fzero → F .relation ; one → G .relation }) isNonTrivial
  open RelationalInterpretation

  entailmentContext : Context
  entailmentContext = [] ′ `X ′ `Y

  x∈entailmentContext : `X ∈ entailmentContext
  x∈entailmentContext = there here

  y∈entailmentContext : `Y ∈ entailmentContext
  y∈entailmentContext = here

  x = var x∈entailmentContext
  y = var y∈entailmentContext

  entailmentPrequantFormula : Formula entailmentContext
  entailmentPrequantFormula = rel `F (x `, y) `→ rel `G (x `, y)

  entailmentFormula : Formula []
  entailmentFormula = `∀ (`∀ entailmentPrequantFormula)


functionalRelationIsomorphism : ∀ {X Y : Type ℓ'} → FunctionalRelation X Y → FunctionalRelation X Y → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
functionalRelationIsomorphism {X} {Y} F G =
  pointwiseEntailment F G × pointwiseEntailment G F

pointwiseEntailment→functionalRelationIsomorphism : ∀ {X Y : Type ℓ'} → (F G : FunctionalRelation X Y) → pointwiseEntailment F G → functionalRelationIsomorphism F G
pointwiseEntailment→functionalRelationIsomorphism {X} {Y} F G (a , a⊩peFG) = {!!} where
    
  `X : Sort
  `Y : Sort

  `X = ↑ (X , F .perX .isSetX)
  `Y = ↑ (Y , F .perY .isSetX)

  relationSymbols : Vec Sort 4
  relationSymbols = (`X `× `Y) ∷ (`X `× `Y) ∷ (`X `× `X) ∷ (`Y `× `Y) ∷ []

  `F : Fin 4
  `F = fzero

  `G : Fin 4
  `G = one

  `~X : Fin 4
  `~X = two

  `~Y : Fin 4
  `~Y = three

  

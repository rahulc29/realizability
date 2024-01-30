open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm)
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.FinData renaming (zero to fzero)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty

module Realizability.Topos.Object
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  where

open import Realizability.Tripos.Logic.Syntax {ℓ = ℓ'}
open import Realizability.Tripos.Logic.Semantics {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Tripos.Prealgebra.Predicate.Base ca renaming (Predicate to Predicate'; _⊩_ to _pre⊩_)
open import Realizability.Tripos.Prealgebra.Predicate.Properties ca
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate' renaming (isSetX to isSetPredicateBase)
open PredicateProperties
open Morphism

private
  _⊩_ : ∀ a (P : Predicate' {ℓ' = ℓ'} {ℓ'' = ℓ''} Unit*) → Type _
  a ⊩ P = a pre⊩ ∣ P ∣ tt*

record PartialEquivalenceRelation (X : Type ℓ') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  field
    isSetX : isSet X
  private
    `X : Sort
    `X = ↑ (X , isSetX)

    `X×X : Sort
    `X×X = `X `× `X

    ~relSym : Vec Sort 1
    ~relSym = `X×X ∷ []

  module X×XRelational = Relational ~relSym
  open X×XRelational

  field
    _~_ : Predicate ⟨ ⟦ lookup fzero ~relSym ⟧ˢ ⟩

  private
    ~relSymInterpretation : RelationInterpretation ~relSym
    ~relSymInterpretation = λ { fzero → _~_ }
  
  module ~Interpretation = Interpretation ~relSym ~relSymInterpretation isNonTrivial
  open ~Interpretation

  module ~Soundness = Soundness isNonTrivial ~relSymInterpretation
  open ~Soundness

  -- Partial equivalence relations

  private
    symContext : Context
    symContext = ([] ′ `X) ′ `X

    x∈symContext : `X ∈ symContext
    x∈symContext = there here

    y∈symContext : `X ∈ symContext
    y∈symContext = here

    xˢ : Term symContext `X
    xˢ = var x∈symContext

    yˢ : Term symContext `X
    yˢ = var y∈symContext

    symPrequantFormula : Formula symContext
    symPrequantFormula = rel fzero (xˢ `, yˢ) `→ rel fzero (yˢ `, xˢ)

  -- ~ ⊢ ∀ x. ∀ y. x ~ y → y ~ x
  symFormula : Formula []
  symFormula = `∀ (`∀ symPrequantFormula)

  field
    symWitness : A
    symIsWitnessed : symWitness ⊩ ⟦ symFormula ⟧ᶠ

  private
    transContext : Context
    transContext = (([] ′ `X) ′ `X) ′ `X

    z∈transContext : `X ∈ transContext
    z∈transContext = here

    y∈transContext : `X ∈ transContext
    y∈transContext = there here

    x∈transContext : `X ∈ transContext
    x∈transContext = there (there here)

    zᵗ : Term transContext `X
    zᵗ = var z∈transContext

    yᵗ : Term transContext `X
    yᵗ = var y∈transContext

    xᵗ : Term transContext `X
    xᵗ = var x∈transContext

    -- ~ : Rel X X, x : X, y : X, z : X ⊢ x ~ y ∧ y ~ z → x ~ z
    transPrequantFormula : Formula transContext
    transPrequantFormula = (rel fzero (xᵗ `, yᵗ) `∧ rel fzero (yᵗ `, zᵗ)) `→ rel fzero (xᵗ `, zᵗ)

  transFormula : Formula []
  transFormula = `∀ (`∀ (`∀ transPrequantFormula))

  field
    transWitness : A
    transIsWitnessed : transWitness ⊩ ⟦ transFormula ⟧ᶠ
   

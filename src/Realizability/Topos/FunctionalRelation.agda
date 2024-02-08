open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm; λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)

open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Fin hiding (Fin; _/_)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients
open import Cubical.Categories.Category

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
open import Realizability.Tripos.Prealgebra.Meets.Identity ca
open import Realizability.Topos.Object {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial 

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate' renaming (isSetX to isSetPredicateBase)
open PredicateProperties
open Morphism

private
  _⊩_ : ∀ a (P : Predicate' {ℓ' = ℓ'} {ℓ'' = ℓ''} Unit*) → Type _
  a ⊩ P = a pre⊩ ∣ P ∣ tt*

  
private λ*ComputationRule = `λ*ComputationRule as fefermanStructure
private λ* = `λ* as fefermanStructure


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
    `F = zero
    `~X : Fin 3
    `~X = one
    `~Y : Fin 3
    `~Y = two

  open Relational relationSymbol

  module RelationInterpretation' = Interpretation relationSymbol (λ { zero → relation ; one → _~X_ ; two → _~Y_ }) isNonTrivial
  open RelationInterpretation'

  module RelationSoundness = Soundness {relSym = relationSymbol} isNonTrivial (λ { zero → relation ; one → _~X_ ; two → _~Y_ })
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
  strictnessFormula : Formula strictnessContext
  strictnessFormula = rel `F (xˢᵗ `, yˢᵗ) `→ (rel `~X (xˢᵗ `, xˢᵗ) `∧ rel `~Y (yˢᵗ `, yˢᵗ))

  field
    isStrict : holdsInTripos strictnessFormula

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

  relationalFormula : Formula relationalContext
  relationalFormula = (rel `F (x₁ `, y₁) `∧ (rel `~X (x₁ `, x₂) `∧ rel `~Y (y₁ `, y₂))) `→ rel `F (x₂ `, y₂)

  field
    isRelational : holdsInTripos relationalFormula

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

  singleValuedFormula : Formula singleValuedContext
  singleValuedFormula =
    (rel `F (xˢᵛ `, y₁ˢᵛ) `∧ rel `F (xˢᵛ `, y₂ˢᵛ)) `→ rel `~Y (y₁ˢᵛ `, y₂ˢᵛ)

  field
    isSingleValued : holdsInTripos singleValuedFormula

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

  totalFormula : Formula totalContext
  totalFormula = rel `~X (xᵗˡ `, xᵗˡ)  `→ `∃ (rel `F (renamingTerm (drop id) xᵗˡ `, var here))

  field
    isTotal : holdsInTripos totalFormula

open FunctionalRelation hiding (`X; `Y)

pointwiseEntailment : ∀ {X Y : Type ℓ'} → FunctionalRelation X Y → FunctionalRelation X Y → Type _
pointwiseEntailment {X} {Y} F G = holdsInTripos entailmentFormula where
  
  `X : Sort
  `Y : Sort

  `X = ↑ (X , F .perX .isSetX)
  `Y = ↑ (Y , F .perY .isSetX)

  relationSymbols : Vec Sort 2
  relationSymbols = (`X `× `Y) ∷ (`X `× `Y) ∷ []

  `F : Fin 2
  `F = zero

  `G : Fin 2
  `G = one

  open Relational relationSymbols

  module RelationalInterpretation = Interpretation relationSymbols (λ { zero → F .relation ; one → G .relation }) isNonTrivial
  open RelationalInterpretation

  module RelationalSoundness = Soundness {relSym = relationSymbols} isNonTrivial (λ { zero → F .relation ; one → G .relation })
  open RelationalSoundness

  entailmentContext : Context
  entailmentContext = [] ′ `X ′ `Y

  x∈entailmentContext : `X ∈ entailmentContext
  x∈entailmentContext = there here

  y∈entailmentContext : `Y ∈ entailmentContext
  y∈entailmentContext = here

  x = var x∈entailmentContext
  y = var y∈entailmentContext

  entailmentFormula : Formula entailmentContext
  entailmentFormula = rel `F (x `, y) `→ rel `G (x `, y)

functionalRelationIsomorphism : ∀ {X Y : Type ℓ'} → FunctionalRelation X Y → FunctionalRelation X Y → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
functionalRelationIsomorphism {X} {Y} F G =
  pointwiseEntailment F G × pointwiseEntailment G F


pointwiseEntailment→functionalRelationIsomorphism : ∀ {X Y : Type ℓ'} → (F G : FunctionalRelation X Y) → pointwiseEntailment F G → functionalRelationIsomorphism F G
pointwiseEntailment→functionalRelationIsomorphism {X} {Y} F G F≤G = F≤G , G≤F where
    
  `X : Sort
  `Y : Sort

  `X = ↑ (X , F .perX .isSetX)
  `Y = ↑ (Y , F .perY .isSetX)

  relationSymbols : Vec Sort 4
  relationSymbols = (`X `× `Y) ∷ (`X `× `Y) ∷ (`X `× `X) ∷ (`Y `× `Y) ∷ []

  `F : Fin 4
  `F = zero

  `G : Fin 4
  `G = one

  `~X : Fin 4
  `~X = two

  `~Y : Fin 4
  `~Y = three

  open Interpretation relationSymbols (λ { zero → F .relation ; one → G .relation ; two → F .perX ._~_ ; three → G .perY ._~_}) isNonTrivial
  open Soundness {relSym = relationSymbols} isNonTrivial ((λ { zero → F .relation ; one → G .relation ; two → F .perX ._~_ ; three → G .perY ._~_}))
  open Relational relationSymbols

  -- What we need to prove is that
  -- F ≤ G ⊨ G ≤ F
  -- We will use the semantic combinators we borrowed from the 1lab

  entailmentContext : Context
  entailmentContext = [] ′ `X ′ `Y

  x : Term entailmentContext `X
  x = var (there here)

  y : Term entailmentContext `Y
  y = var here

  G⊨x~x : (⊤ᵗ `∧ rel `G (x `, y)) ⊨ rel `~X (x `, x)
  G⊨x~x =
    `→elim
      {Γ = entailmentContext}
      {ϕ = ⊤ᵗ `∧ (rel `G (x `, y))}
      {ψ = rel `G (x `, y)}
      {θ = rel `~X (x `, x)}
      {!G .isStrict!}
      {!!}

  ⊤∧G⊨F : (⊤ᵗ `∧ rel `G (x `, y)) ⊨ rel `F (x `, y)
  ⊤∧G⊨F = cut {Γ = entailmentContext} {ϕ = ⊤ᵗ `∧ rel `G (x `, y)} {ψ = rel `~X (x `, x)}
           {θ = rel `F (x `, y)}
           G⊨x~x
           {!!}

  G≤F : pointwiseEntailment G F
  G≤F = `→intro {Γ = entailmentContext} {ϕ = ⊤ᵗ} {ψ = rel `G (x `, y)} {θ = rel `F (x `, y)} ⊤∧G⊨F

RTMorphism : (X Y : Type ℓ') →  Type _
RTMorphism X Y = FunctionalRelation X Y / λ F G → functionalRelationIsomorphism F G

RTObject : Type _
RTObject = Σ[ X ∈ Type ℓ' ] PartialEquivalenceRelation X

idMorphism : (ob : RTObject) → RTMorphism (ob .fst) (ob .fst)
idMorphism ob =
  [ record
     { perX = ob .snd
     ; perY = ob .snd
     ; relation = ob .snd ._~_
     ; isStrict = {!!}
     ; isRelational = {!!}
     ; isSingleValued = {!!}
     ; isTotal = {!!}
     } ] where

  `X : Sort
  `X = ↑ (ob .fst , ob .snd .isSetX)

  relationSymbols : Vec Sort 3
  relationSymbols = (`X `× `X) ∷ (`X `× `X) ∷ (`X `× `X) ∷ []

  open Interpretation relationSymbols (λ { zero → ob .snd ._~_ ; one → ob .snd ._~_ ; two → ob .snd ._~_ }) isNonTrivial
  open Soundness {relSym = relationSymbols} isNonTrivial (λ { zero → ob .snd ._~_ ; one → ob .snd ._~_ ; two → ob .snd ._~_ })
  open Relational relationSymbols

  isStrictContext : Context
  isStrictContext = [] ′ `X ′ `X

  x : Term isStrictContext `X
  x = var (there here)

  y : Term isStrictContext `X
  y = var here

  holdsInTriposIsStrict : holdsInTripos (rel zero (x `, y) `→ (rel one (x `, y) `∧ rel two (x `, y)))
  holdsInTriposIsStrict =
    do
    let
      prover : ApplStrTerm as 2
      prover =
        ` pair ̇ # fone ̇ # fone
    return
      (λ* prover ,
      (λ { ((tt* , x') , y') a tt* b b⊩x'~y'
        →
          let
            proofEq : λ* prover ⨾ a ⨾ b ≡ pair ⨾ b ⨾ b
            proofEq =
              λ*ComputationRule prover (a ∷ b ∷ [])

            pr₁proofEq : pr₁ ⨾ (λ* prover ⨾ a ⨾ b) ≡ b
            pr₁proofEq =
              pr₁ ⨾ (λ* prover ⨾ a ⨾ b)
                ≡⟨ cong (λ x → pr₁ ⨾ x) proofEq ⟩
              pr₁ ⨾ (pair ⨾ b ⨾ b)
                ≡⟨ pr₁pxy≡x b b ⟩
              b
                ∎

            pr₂proofEq : pr₂ ⨾ (λ* prover ⨾ a ⨾ b) ≡ b
            pr₂proofEq =
              pr₂ ⨾ (λ* prover ⨾ a ⨾ b)
                ≡⟨ cong (λ x → pr₂ ⨾ x) proofEq ⟩
              pr₂ ⨾ (pair ⨾ b ⨾ b)
                ≡⟨ pr₂pxy≡y b b ⟩
              b
                ∎
          in
          (subst
            (λ r → r pre⊩ ∣ (⋆_ (isSet× (isSet× isSetUnit* (ob .snd .isSetX)) (ob .snd .isSetX)) (isSet× (ob .snd .isSetX) (ob .snd .isSetX)) (λ γ → snd (fst γ) , snd γ) (ob .snd ._~_)) ∣ ((tt* , x') , y'))
          (sym pr₁proofEq) b⊩x'~y') ,
          subst
            (λ r → r pre⊩ ∣ (⋆_ (isSet× (isSet× isSetUnit* (ob .snd .isSetX)) (ob .snd .isSetX)) (isSet× (ob .snd .isSetX) (ob .snd .isSetX)) (λ γ → snd (fst γ) , snd γ) (ob .snd ._~_)) ∣ ((tt* , x') , y')) (sym pr₂proofEq) b⊩x'~y' }))
  

RT : Category (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) ((ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')))
Category.ob RT = Σ[ X ∈ Type ℓ' ] PartialEquivalenceRelation X
Category.Hom[_,_] RT (X , perX) (Y , perY) = RTMorphism X Y
Category.id RT {X , perX} = {!!}
Category._⋆_ RT = {!!}
Category.⋆IdL RT = {!!}
Category.⋆IdR RT = {!!}
Category.⋆Assoc RT = {!!}
Category.isSetHom RT = {!!}

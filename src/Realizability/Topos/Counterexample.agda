open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm)
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
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Relation.Binary

module Realizability.Topos.Counterexample
  {ℓ}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  where

open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ} {ℓ'' = ℓ} ca
open import Realizability.Tripos.Prealgebra.Meets.Identity {ℓ' = ℓ} {ℓ'' = ℓ} ca
open import Realizability.Topos.Object {ℓ = ℓ} {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.FunctionalRelation {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.TerminalObject {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate renaming (isSetX to isSetPredicateBase)
open PredicateProperties
open Morphism

module
  ChoiceCounterexample
  (choice :
    ∀ {X Y : Type ℓ}
      (perX : PartialEquivalenceRelation X)
      (perY : PartialEquivalenceRelation Y)
      (f : RTMorphism perX perY)
    → Σ[ F ∈ FunctionalRelation perX perY ] ([ F ] ≡ f)) where

  module _ (a : A) where
    opaque
      unfolding terminalPer
      singleRealizerIdFuncRel : FunctionalRelation terminalPer terminalPer
      Predicate.isSetX (FunctionalRelation.relation singleRealizerIdFuncRel) = isSet× isSetUnit* isSetUnit*
      Predicate.∣ FunctionalRelation.relation singleRealizerIdFuncRel ∣ (tt* , tt*) r = r ≡ a
      Predicate.isPropValued (FunctionalRelation.relation singleRealizerIdFuncRel) (tt* , tt*) r = isSetA _ _
      isFunctionalRelation.isStrictDomain (FunctionalRelation.isFuncRel singleRealizerIdFuncRel) = return (k , (λ { tt* tt* r r≡a → tt* }))
      isFunctionalRelation.isStrictCodomain (FunctionalRelation.isFuncRel singleRealizerIdFuncRel) = return (k , (λ { tt* tt* r r≡a → tt* }))
      isFunctionalRelation.isRelational (FunctionalRelation.isFuncRel singleRealizerIdFuncRel) =
        let
          realizer : ApplStrTerm as 3
          realizer = # one
        in
        return (λ*3 realizer , (λ { tt* tt* tt* tt* a b c tt* b≡a tt* → λ*3ComputationRule realizer a b c ∙ b≡a}))
      isFunctionalRelation.isSingleValued (FunctionalRelation.isFuncRel singleRealizerIdFuncRel) = return (k , (λ { x y y' r₁ r₂ x₁ x₂ → tt* }))
      isFunctionalRelation.isTotal (FunctionalRelation.isFuncRel singleRealizerIdFuncRel) = return (k ⨾ a , (λ { tt* r tt* → ∣ tt* , (kab≡a a r) ∣₁}))

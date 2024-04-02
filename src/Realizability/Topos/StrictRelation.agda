open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm)
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
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
open import Cubical.Categories.Morphism
open import Cubical.Categories.Constructions.SubObject
open import Cubical.Categories.Constructions.Slice
open import Cubical.Relation.Binary

module Realizability.Topos.StrictRelation
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  where

open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Tripos.Prealgebra.Meets.Identity {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Topos.Object {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial 
open import Realizability.Topos.FunctionalRelation {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial
open import Realizability.Topos.Equalizer {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial
open import Realizability.Topos.BinProducts {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial
open import Realizability.Topos.MonicReprFuncRel {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate renaming (isSetX to isSetPredicateBase)
open Morphism
open PartialEquivalenceRelation
open FunctionalRelation
open Category RT

record isStrictRelation {X : Type ℓ'} (perX : PartialEquivalenceRelation X) (ϕ : Predicate X) : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
  field
    isStrict : ∃[ st ∈ A ] (∀ x r → r ⊩ ∣ ϕ ∣ x → (st ⨾ r) ⊩ ∣ perX .equality ∣ (x , x))
    isRelational : ∃[ rel ∈ A ] (∀ x x' r s → r ⊩ ∣ ϕ ∣ x → s ⊩ ∣ perX .equality ∣ (x , x') → (rel ⨾ r ⨾ s) ⊩ ∣ ϕ ∣ x')

record StrictRelation {X : Type ℓ'} (perX : PartialEquivalenceRelation X) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ''))) where
  field
    predicate : Predicate X
    isStrictRelationPredicate : isStrictRelation perX predicate
  open isStrictRelation isStrictRelationPredicate public

-- Every strict relation induces a subobject
module InducedSubobject {X : Type ℓ'} (perX : PartialEquivalenceRelation X) (ϕ : StrictRelation perX) where
  open StrictRelation
  -- the subobject induced by ϕ
  {-# TERMINATING #-}
  subPer : PartialEquivalenceRelation X
  Predicate.isSetX (equality subPer) = isSet× (perX .isSetX) (perX .isSetX)
  ∣ equality subPer ∣ (x , x') r = (pr₁ ⨾ r) ⊩ ∣ perX .equality ∣ (x , x') × (pr₂ ⨾ r) ⊩ ∣ ϕ .predicate ∣ x
  isPropValued (equality subPer) (x , x') r = isProp× (perX .equality .isPropValued _ _) (ϕ .predicate .isPropValued _ _)
  isPartialEquivalenceRelation.isSetX (isPerEquality subPer) = perX .isSetX
  isPartialEquivalenceRelation.isSymmetric (isPerEquality subPer) =
    do
      -- Trivial : use symmetry of ~X and relationality of ϕ
      (s , s⊩isSymmetricX) ← perX .isSymmetric
      (relϕ , relϕ⊩isRelationalϕ) ← ϕ .isRelational
      let
        realizer : ApplStrTerm as 1
        realizer = ` pair ̇ (` s ̇ (` pr₁ ̇ # zero)) ̇ (` relϕ ̇ (` pr₂ ̇ # zero) ̇ (` pr₁ ̇ # zero))
      return
        (λ* realizer ,
        (λ { x x' r (pr₁r⊩x~x' , pr₂r⊩ϕx) →
          subst
            (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x))
            (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _))
            (s⊩isSymmetricX x x' _ pr₁r⊩x~x') ,
          subst
            (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x')
            (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _))
            (relϕ⊩isRelationalϕ x x' _ _ pr₂r⊩ϕx pr₁r⊩x~x') }))
  isPartialEquivalenceRelation.isTransitive (isPerEquality subPer) =
    do
      (t , t⊩isTransitiveX) ← perX .isTransitive
      (relϕ , relϕ⊩isRelationalϕ) ← ϕ .isRelational
      let
        realizer : ApplStrTerm as 2
        realizer = ` pair ̇ (` t ̇ (` pr₁ ̇ # one) ̇ (` pr₁ ̇ # zero)) ̇ (` pr₂ ̇ # one)
      return
        (λ*2 realizer ,
        (λ { x₁ x₂ x₃ a b (⊩x₁~x₂ , ⊩ϕx₁) (⊩x₂~x₃ , ⊩ϕx₂) →
          subst
            (λ r' → r' ⊩ ∣ perX .equality ∣ (x₁ , x₃))
            (sym (cong (λ x → pr₁ ⨾ x) (λ*2ComputationRule realizer a b) ∙ pr₁pxy≡x _ _))
            (t⊩isTransitiveX x₁ x₂ x₃ _ _ ⊩x₁~x₂ ⊩x₂~x₃) ,
          subst
            (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x₁)
            (sym (cong (λ x → pr₂ ⨾ x) (λ*2ComputationRule realizer a b) ∙ pr₂pxy≡y _ _))
            ⊩ϕx₁ }))

  opaque
    unfolding idFuncRel
    {-# TERMINATING #-}
    incFuncRel : FunctionalRelation subPer perX
    Predicate.isSetX (relation incFuncRel) = isSet× (perX .isSetX) (perX .isSetX)
    Predicate.∣ relation incFuncRel ∣ (x , x') r = (pr₁ ⨾ r) ⊩ ∣ perX .equality ∣ (x , x') × (pr₂ ⨾ r) ⊩ ∣ ϕ .predicate ∣ x
    Predicate.isPropValued (relation incFuncRel) (x , x') r = isProp× (perX .equality .isPropValued _ _) (ϕ .predicate .isPropValued _ _)
    isFunctionalRelation.isStrictDomain (isFuncRel incFuncRel) =
      do
        (stD , stD⊩isStrictDomain) ← idFuncRel perX .isStrictDomain
        let
          realizer : ApplStrTerm as 1
          realizer = ` pair ̇ (` stD ̇ (` pr₁ ̇ # zero)) ̇ (` pr₂ ̇ # zero)
        return
          (λ* realizer ,
          (λ { x x' r (⊩x~x' , ⊩ϕx) →
            (subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _)) (stD⊩isStrictDomain x x' _ ⊩x~x')) ,
            (subst (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x) (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _)) ⊩ϕx) }))
    isFunctionalRelation.isStrictCodomain (isFuncRel incFuncRel) =
      do
        (stC , stC⊩isStrictCodomain) ← idFuncRel perX .isStrictCodomain
        let
          realizer : ApplStrTerm as 1
          realizer = ` stC ̇ (` pr₁ ̇ # zero)
        return
          (λ* realizer ,
          (λ { x x' r (⊩x~x' , ⊩ϕx) → subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x')) (sym (λ*ComputationRule realizer r)) (stC⊩isStrictCodomain x x' _ ⊩x~x')}))
    isFunctionalRelation.isRelational (isFuncRel incFuncRel) =
      do
        (relX , relX⊩isRelationalX) ← idFuncRel perX .isRelational
        (relϕ , relϕ⊩isRelationalϕ) ← ϕ .isRelational
        let
          realizer : ApplStrTerm as 3
          realizer = ` pair ̇ (` relX ̇ (` pr₁ ̇ # two) ̇ (` pr₁ ̇ # one) ̇ # zero) ̇ (` relϕ ̇ (` pr₂ ̇ # two) ̇ (` pr₁ ̇ # two))
        return
          (λ*3 realizer ,
          (λ { x₁ x₂ x₃ x₄ a b c (⊩x₁~x₂ , ⊩ϕx₁) (⊩x₁~x₃ , ⊩ϕx₁') c⊩x₃~x₄ →
            subst
              (λ r' → r' ⊩ ∣ perX .equality ∣ (x₂ , x₄))
              (sym (cong (λ x → pr₁ ⨾ x) (λ*3ComputationRule realizer a b c) ∙ pr₁pxy≡x _ _))
              (relX⊩isRelationalX x₁ x₂ x₃ x₄ _ _ _ ⊩x₁~x₂ ⊩x₁~x₃ c⊩x₃~x₄) ,
            subst
              (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x₂)
              (sym (cong (λ x → pr₂ ⨾ x) (λ*3ComputationRule realizer a b c) ∙ pr₂pxy≡y _ _))
              (relϕ⊩isRelationalϕ x₁ x₂ _ _ ⊩ϕx₁ ⊩x₁~x₂) }))
    isFunctionalRelation.isSingleValued (isFuncRel incFuncRel) =
      do
        (sv , sv⊩isSingleValuedX) ← idFuncRel perX .isSingleValued
        let
          realizer : ApplStrTerm as 2
          realizer = ` sv ̇ (` pr₁ ̇ # one) ̇ (` pr₁ ̇ # zero)
        return
          (λ*2 realizer ,
          (λ { x x' x'' r₁ r₂ (⊩x~x' , ⊩ϕx) (⊩x~x'' , ⊩ϕx') →
            subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x'')) (sym (λ*2ComputationRule realizer r₁ r₂)) (sv⊩isSingleValuedX x x' x'' _ _ ⊩x~x' ⊩x~x'') }))
    isFunctionalRelation.isTotal (isFuncRel incFuncRel) =
      do
        return
          (Id ,
          (λ { x r (pr₁r⊩x~x , pr₂r⊩ϕx) →
            return
              (x ,
              subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (cong (λ x → pr₁ ⨾ x) (sym (Ida≡a _))) pr₁r⊩x~x ,
              subst (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x) (cong (λ x → pr₂ ⨾ x) (sym (Ida≡a _))) pr₂r⊩ϕx) }))

  opaque
    unfolding isInjectiveFuncRel
    unfolding incFuncRel
    isInjectiveIncFuncRel : isInjectiveFuncRel subPer perX incFuncRel
    isInjectiveIncFuncRel =
      do
        (t , t⊩isTransitiveX) ← perX .isTransitive
        (s , s⊩isSymmetricX) ← perX .isSymmetric
        let
          realizer : ApplStrTerm as 2
          realizer = ` pair ̇ (` t ̇ (` pr₁ ̇ # one) ̇ (` s ̇ (` pr₁ ̇ # zero))) ̇ (` pr₂ ̇ # one)
        return
          (λ*2 realizer ,
          (λ x₁ x₂ x₃ r₁ r₂ (⊩x₁~x₃ , ⊩ϕx₁) (⊩x₂~x₃ , ⊩ϕx₂) →
            subst
              (λ r' → r' ⊩ ∣ perX .equality ∣ (x₁ , x₂))
              (sym (cong (λ x → pr₁ ⨾ x) (λ*2ComputationRule realizer r₁ r₂) ∙ pr₁pxy≡x _ _))
              (t⊩isTransitiveX x₁ x₃ x₂ _ _ ⊩x₁~x₃ (s⊩isSymmetricX x₂ x₃ _ ⊩x₂~x₃)) ,
            subst
              (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x₁)
              (sym (cong (λ x → pr₂ ⨾ x) (λ*2ComputationRule realizer r₁  r₂) ∙ pr₂pxy≡y _ _))
              ⊩ϕx₁))

  isMonicInc : isMonic RT [ incFuncRel ]
  isMonicInc = isInjectiveFuncRel→isMonic subPer perX incFuncRel isInjectiveIncFuncRel

-- Every subobject representing functional relation is isomorphic (as a subobject) to a subobject induced by a strict relation
module SubobjectIsoMonicFuncRel
  {X Y : Type ℓ'}
  (perX : PartialEquivalenceRelation X)
  (perY : PartialEquivalenceRelation Y)
  (F : FunctionalRelation perY perX)
  (isMonicF : isMonic RT [ F ]) where

  {-# TERMINATING #-}
  ψ : StrictRelation perX
  Predicate.isSetX (StrictRelation.predicate ψ) = perX .isSetX
  Predicate.∣ StrictRelation.predicate ψ ∣ x r = ∃[ y ∈ Y ] r ⊩ ∣ F .relation ∣ (y , x)
  Predicate.isPropValued (StrictRelation.predicate ψ) x r = isPropPropTrunc
  isStrictRelation.isStrict (StrictRelation.isStrictRelationPredicate ψ) =
    do
      (stCF , stCF⊩isStrictCodomainF) ← F .isStrictCodomain
      return
        (stCF ,
        (λ x r r⊩∃y →
          transport
            (propTruncIdempotent (perX .equality .isPropValued _ _))
            (do
              (y , ⊩Fyx) ← r⊩∃y
              return (stCF⊩isStrictCodomainF y x _ ⊩Fyx))))
  isStrictRelation.isRelational (StrictRelation.isStrictRelationPredicate ψ) =
    do
      (relF , relF⊩isRelationalF) ← F .isRelational
      (stDF , stDF⊩isStrictDomainF) ← F .isStrictDomain
      let
        realizer : ApplStrTerm as 2
        realizer = ` relF ̇ (` stDF ̇ # one) ̇ # one ̇ # zero
      return
        (λ*2 realizer ,
        (λ x x' r s r⊩∃y s⊩x~x' →
          do
            (y , ⊩Fyx) ← r⊩∃y
            return
              (y ,
              subst
                (λ r' → r' ⊩ ∣ F .relation ∣ (y , x'))
                (sym (λ*2ComputationRule realizer r s))
                (relF⊩isRelationalF y y x x' _ _ _ (stDF⊩isStrictDomainF y x _ ⊩Fyx) ⊩Fyx s⊩x~x'))))

  perψ : PartialEquivalenceRelation X
  perψ = InducedSubobject.subPer perX ψ

  -- ≤ as subobjects
  -- TODO : formalise the preorder category of subobjects
  {-# TERMINATING #-}
  perY≤perψFuncRel : FunctionalRelation perY perψ
  Predicate.isSetX (relation perY≤perψFuncRel) = isSet× (perY .isSetX) (perX .isSetX)
  Predicate.∣ relation perY≤perψFuncRel ∣ = ∣ F .relation ∣
  Predicate.isPropValued (relation perY≤perψFuncRel) = F .relation .isPropValued
  isFunctionalRelation.isStrictDomain (isFuncRel perY≤perψFuncRel) =
    isFunctionalRelation.isStrictDomain (F .isFuncRel)
  isFunctionalRelation.isStrictCodomain (isFuncRel perY≤perψFuncRel) =
    do
      (stCF , stCF⊩isStrictCodomain) ← F .isStrictCodomain
      let
        realizer : ApplStrTerm as 1
        realizer = ` pair ̇ (` stCF ̇ # zero) ̇ # zero
      return
        (λ* realizer ,
        (λ y x r ⊩Fyx →
          subst
            (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
            (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _))
            (stCF⊩isStrictCodomain y x _ ⊩Fyx) ,
          ∣ y ,
            subst
              (λ r' → r' ⊩ ∣ F .relation ∣ (y , x))
              (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _))
              ⊩Fyx ∣₁))
  isFunctionalRelation.isRelational (isFuncRel perY≤perψFuncRel) =
    do
      (relF , relF⊩isRelationalF) ← F .isRelational
      let
        realizer : ApplStrTerm as 3
        realizer = ` relF ̇ # two ̇ # one ̇ (` pr₁ ̇ # zero)
      return
        (λ*3 realizer ,
        (λ { y y' x x' a b c ⊩y~y' ⊩Fyx (⊩x~x' , ⊩Fy''x) →
          subst (λ r' → r' ⊩ ∣ F .relation ∣ (y' , x')) (sym (λ*3ComputationRule realizer a b c)) (relF⊩isRelationalF y y' x x' _ _ _ ⊩y~y' ⊩Fyx ⊩x~x') }))
  isFunctionalRelation.isSingleValued (isFuncRel perY≤perψFuncRel) =
    do
      (svF , svF⊩isSingleValuedF) ← F .isSingleValued
      let
        realizer : ApplStrTerm as 2
        realizer = ` pair ̇ (` svF ̇ # one ̇ # zero) ̇ # one
      return
        (λ*2 realizer ,
        (λ y x x' r₁ r₂ ⊩Fyx ⊩Fyx' →
          subst
            (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x'))
            (sym (cong (λ x → pr₁ ⨾ x) (λ*2ComputationRule realizer r₁ r₂) ∙ pr₁pxy≡x _ _))
            (svF⊩isSingleValuedF y x x' _ _ ⊩Fyx ⊩Fyx') ,
          ∣ y ,
            (subst
              (λ r' → r' ⊩ ∣ F .relation ∣ (y , x))
              (sym (cong (λ x → pr₂ ⨾ x) (λ*2ComputationRule realizer r₁ r₂) ∙ pr₂pxy≡y _ _))
              ⊩Fyx) ∣₁))
  isFunctionalRelation.isTotal (isFuncRel perY≤perψFuncRel) =
    do
      (tlF , tlF⊩isTotalF) ← F .isTotal
      return
        (tlF ,
        (λ y r ⊩y~y →
          do
            (x , ⊩Fyx) ← tlF⊩isTotalF y _ ⊩y~y
            return (x , ⊩Fyx)))

  -- perY truly is ≤ perψ
  opaque
    unfolding composeRTMorphism
    unfolding InducedSubobject.incFuncRel
    perY≤perψCommutes : [ perY≤perψFuncRel ] ⋆ [ InducedSubobject.incFuncRel perX ψ ] ≡ [ F ]
    perY≤perψCommutes =
      let
        answer =
          do
            (stDF , stDF⊩isStrictDomainF) ← F .isStrictDomain
            (relF , relF⊩isRelationalF) ← F .isRelational
            let
              realizer : ApplStrTerm as 1
              realizer = ` relF ̇ (` stDF ̇ (` pr₁ ̇ # zero)) ̇ (` pr₁ ̇ # zero) ̇ (` pr₁ ̇ (` pr₂ ̇ # zero))
            return
              (λ* realizer ,
              (λ y x r r⊩∃x' →
                transport
                  (propTruncIdempotent (F .relation .isPropValued _ _))
                  (do
                    (x' , ⊩Fyx' , ⊩x'~x , ⊩ψx') ← r⊩∃x'
                    return
                      (subst
                        (λ r → r ⊩ ∣ F .relation ∣ (y , x))
                        (sym (λ*ComputationRule realizer r))
                        (relF⊩isRelationalF y y x' x _ _ _ (stDF⊩isStrictDomainF y x' _ ⊩Fyx') ⊩Fyx' ⊩x'~x)))))
      in
      eq/ _ _ (answer , F≤G→G≤F perY perX (composeFuncRel _ _ _ perY≤perψFuncRel (InducedSubobject.incFuncRel perX ψ)) F answer)

  opaque
    unfolding isInjectiveFuncRel
    {-# TERMINATING #-}
    perψ≤perYFuncRel : FunctionalRelation perψ perY
    Predicate.isSetX (relation perψ≤perYFuncRel) = isSet× (perX .isSetX) (perY .isSetX)
    Predicate.∣ relation perψ≤perYFuncRel ∣ (x , y) r = r ⊩ ∣ F .relation ∣ (y , x)
    Predicate.isPropValued (relation perψ≤perYFuncRel) (x , y) r = F .relation .isPropValued _ _
    isFunctionalRelation.isStrictDomain (isFuncRel perψ≤perYFuncRel) =
      do
        (stCF , stCF⊩isStrictCodomainF) ← F .isStrictCodomain
        let
          realizer : ApplStrTerm as 1
          realizer = ` pair ̇ (` stCF ̇ # zero) ̇ # zero
        return
          (λ* realizer ,
          (λ x y r ⊩Fyx →
            (subst
              (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
              (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _))
              (stCF⊩isStrictCodomainF y x _ ⊩Fyx)) ,
            (return
              (y ,
              (subst
                (λ r' → r' ⊩ ∣ F .relation ∣ (y , x))
                (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _))
                ⊩Fyx)))))
    isFunctionalRelation.isStrictCodomain (isFuncRel perψ≤perYFuncRel) =
      do
        (stDF , stDF⊩isStrictDomainF) ← F .isStrictDomain
        return
          (stDF ,
          (λ x y r ⊩Fyx → stDF⊩isStrictDomainF y x _ ⊩Fyx))
    isFunctionalRelation.isRelational (isFuncRel perψ≤perYFuncRel) =
      do
        (relF , relF⊩isRelationalF) ← F .isRelational
        let
          realizer : ApplStrTerm as 3
          realizer = ` relF ̇ # zero ̇ # one ̇ (` pr₁ ̇ # two)
        return
          (λ*3 realizer ,
          (λ { x x' y y' a b c (⊩x~x' , ⊩ψx) ⊩Fyx ⊩y~y' →
            subst (λ r' → r' ⊩ ∣ F .relation ∣ (y' , x')) (sym (λ*3ComputationRule realizer a b c)) (relF⊩isRelationalF y y' x x' _ _ _ ⊩y~y' ⊩Fyx ⊩x~x') }))
    isFunctionalRelation.isSingleValued (isFuncRel perψ≤perYFuncRel) =
      let
        isInjectiveFuncRelF = isMonic→isInjectiveFuncRel perY perX F isMonicF
      in
      do
        (injF , injF⊩isInjectiveF) ← isInjectiveFuncRelF
        return
          (injF ,
          (λ x y y' r₁ r₂ ⊩Fyx ⊩Fy'x →
            injF⊩isInjectiveF y y' x _ _ ⊩Fyx ⊩Fy'x))
    isFunctionalRelation.isTotal (isFuncRel perψ≤perYFuncRel) =
        return
          (pr₂ ,
          (λ { x r (⊩x~x , ⊩ψx) → ⊩ψx }))

  opaque
    unfolding composeRTMorphism
    unfolding composeFuncRel
    unfolding InducedSubobject.incFuncRel
    unfolding perψ≤perYFuncRel
    perψ≤perYCommutes : [ perψ≤perYFuncRel ] ⋆ [ F ] ≡ [ InducedSubobject.incFuncRel perX ψ ]
    perψ≤perYCommutes =
      let
        answer =
          do
            (svF , svF⊩isSingleValuedF) ← F .isSingleValued
            let
              realizer : ApplStrTerm as 1
              realizer = ` pair ̇ (` svF ̇ (` pr₁ ̇ # zero) ̇ (` pr₂ ̇ # zero)) ̇ (` pr₁ ̇ # zero)
            return
              (λ* realizer ,
              (λ x x' r r⊩∃y →
                transport
                  (propTruncIdempotent (isProp× (perX .equality .isPropValued _ _) isPropPropTrunc))
                  (do
                    (y , ⊩Fyx , ⊩Fyx') ← r⊩∃y
                    return
                      (subst
                        (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x'))
                        (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _))
                        (svF⊩isSingleValuedF y x x' _ _ ⊩Fyx ⊩Fyx') ,
                      return
                        (y ,
                        (subst
                          (λ r' → r' ⊩ ∣ F .relation ∣ (y , x))
                          (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _))
                          ⊩Fyx))))))
      in
      eq/ _ _ (answer , F≤G→G≤F perψ perX (composeFuncRel _ _ _ perψ≤perYFuncRel F) (InducedSubobject.incFuncRel perX ψ) answer)

-- For strict relations, subobject inclusion is identified with pointwise entailment
module InclusionEntailment
  {X : Type ℓ'}
  (perX : PartialEquivalenceRelation X)
  (ϕ ψ : StrictRelation perX) where
  open StrictRelation
  open PredicateProperties X
  SubObjX = SubObjCat RT (X , perX)
  SubObjHom = Category.Hom[_,_] SubObjX

  perϕ = InducedSubobject.subPer perX ϕ
  perψ = InducedSubobject.subPer perX ψ

  incϕ = InducedSubobject.incFuncRel perX ϕ
  incψ = InducedSubobject.incFuncRel perX ψ

  ϕsubObject : Category.ob SubObjX
  ϕsubObject = sliceob [ InducedSubobject.incFuncRel perX ϕ ] , InducedSubobject.isMonicInc perX ϕ

  ψsubObject : Category.ob SubObjX
  ψsubObject = sliceob [ InducedSubobject.incFuncRel perX ψ ] , InducedSubobject.isMonicInc perX ψ

  opaque
    unfolding composeRTMorphism
    unfolding composeFuncRel
    unfolding InducedSubobject.incFuncRel
    SubObjHom→ϕ≤ψ : SubObjHom ϕsubObject ψsubObject → (ϕ .predicate ≤ ψ .predicate)
    SubObjHom→ϕ≤ψ (slicehom f f⋆incψ≡incϕ) =
      SQ.elimProp
        {P = λ f → (f ⋆ [ incψ ] ≡ [ incϕ ]) → ϕ .predicate ≤ ψ .predicate}
        (λ f → isPropΠ λ f⋆incψ≡incϕ → isProp≤ (ϕ .predicate) (ψ .predicate))
        (λ F F⋆incψ≡incϕ →
          let
            (p , q) =
              SQ.effective
                (isPropValuedBientailment (InducedSubobject.subPer perX ϕ) perX)
                (isEquivRelBientailment (InducedSubobject.subPer perX ϕ) perX)
                (composeFuncRel _ _ _ F incψ)
                incϕ
                F⋆incψ≡incϕ
          in
          do
            (stϕ , stϕ⊩isStrictϕ) ← ϕ .isStrict
            (relψ , relψ⊩isRelationalψ) ← ψ .isRelational
            (q , q⊩incϕ≤F⋆incψ) ← q
            let
              realizer : ApplStrTerm as 1
              realizer = ` relψ ̇ (` pr₂ ̇ (` pr₂ ̇ (` q ̇ (` pair ̇ (` stϕ ̇ # zero) ̇ # zero)))) ̇ (` pr₁ ̇ (` pr₂ ̇ (` q ̇ (` pair ̇ (` stϕ ̇ # zero) ̇ # zero))))
            return
              (λ* realizer ,
              (λ x a a⊩ϕx →
                transport
                  (propTruncIdempotent (ψ .predicate .isPropValued _ _))
                  (do
                    (x' , ⊩Fxx' , ⊩x'~x , ⊩ψx') ←
                      q⊩incϕ≤F⋆incψ
                        x x
                        (pair ⨾ (stϕ ⨾ a) ⨾ a)
                        ((subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym (pr₁pxy≡x _ _)) (stϕ⊩isStrictϕ x a a⊩ϕx)) ,
                         (subst (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x) (sym (pr₂pxy≡y _ _)) a⊩ϕx))
                    return (subst (λ r' → r' ⊩ ∣ ψ .predicate ∣ x) (sym (λ*ComputationRule realizer a)) (relψ⊩isRelationalψ x' x _ _ ⊩ψx' ⊩x'~x))))))
        f
        f⋆incψ≡incϕ

  module _ (ϕ≤ψ : ϕ .predicate ≤ ψ .predicate) where opaque
    unfolding idFuncRel
    unfolding composeRTMorphism
    unfolding composeFuncRel
    unfolding InducedSubobject.incFuncRel

    {-# TERMINATING #-}
    funcRel : FunctionalRelation perϕ perψ
    Predicate.isSetX (relation funcRel) = isSet× (perX .isSetX) (perX .isSetX)
    Predicate.∣ relation funcRel ∣ (x , x') r = (pr₁ ⨾ r) ⊩ ∣ perX .equality ∣ (x , x') × ((pr₁ ⨾ (pr₂ ⨾ r)) ⊩ ∣ ϕ .predicate ∣ x) × ((pr₂ ⨾ (pr₂ ⨾ r)) ⊩ ∣ ψ .predicate ∣ x)
    Predicate.isPropValued (relation funcRel) (x , x') r = isProp× (perX .equality .isPropValued _ _) (isProp× (ϕ .predicate .isPropValued _ _) (ψ .predicate .isPropValued _ _))
    isFunctionalRelation.isStrictDomain (isFuncRel funcRel) =
      do
        (stϕ , stϕ⊩isStrictϕ) ← ϕ .isStrict
        let
          realizer : ApplStrTerm as 1
          realizer = ` pair ̇ (` stϕ ̇ (` pr₁ ̇ (` pr₂ ̇ # zero))) ̇ (` pr₁ ̇ (` pr₂ ̇ # zero))
        return
          (λ* realizer ,
          (λ { x x' r (⊩x~x' , ⊩ϕx , ⊩ψx) →
            subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _)) (stϕ⊩isStrictϕ x _ ⊩ϕx) ,
            subst (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x) (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _)) ⊩ϕx}))
    isFunctionalRelation.isStrictCodomain (isFuncRel funcRel) =
      do
        (stCX , stCX⊩isStrictCodomainX) ← idFuncRel perX .isStrictCodomain
        (relψ , relψ⊩isRelationalψ) ← ψ .isRelational
        let
          realizer : ApplStrTerm as 1
          realizer = ` pair ̇ (` stCX ̇ (` pr₁ ̇ # zero)) ̇ (` relψ ̇ (` pr₂ ̇ (` pr₂ ̇ # zero)) ̇ (` pr₁ ̇ # zero))
        return
          (λ* realizer ,
          (λ { x x' r (⊩x~x' , ⊩ϕx , ⊩ψx) →
            subst
              (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x'))
              (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _))
              (stCX⊩isStrictCodomainX x x' _ ⊩x~x') ,
            subst
              (λ r' → r' ⊩ ∣ ψ .predicate ∣ x')
              (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _))
              (relψ⊩isRelationalψ x x' _ _ ⊩ψx ⊩x~x')}))
    isFunctionalRelation.isRelational (isFuncRel funcRel) =
      do
        (relX , relX⊩isRelationalX) ← idFuncRel perX .isRelational
        (relϕ , relϕ⊩isRelationalϕ) ← ϕ .isRelational
        (relψ , relψ⊩isRelationalψ) ← ψ .isRelational
        let
          realizer : ApplStrTerm as 3
          realizer =
            ` pair ̇ (` relX ̇ (` pr₁ ̇ # two) ̇ (` pr₁ ̇ # one) ̇ (` pr₁ ̇ # zero)) ̇ (` pair ̇ (` relϕ ̇ (` pr₂ ̇ # two) ̇ (` pr₁ ̇ # two)) ̇ (` relψ ̇ (` pr₂ ̇ (` pr₂ ̇ # one)) ̇ (` pr₁ ̇ # two)))
        return
          (λ*3 realizer ,
          λ { x₁ x₂ x₃ x₄ a b c (⊩x₁~x₂ , ⊩ϕx₁) (⊩x₁~x₃ , ⊩'ϕx₁ , ⊩ψx₁) (⊩x₃~x₄ , ⊩ψx₃) →
            subst
              (λ r' → r' ⊩ ∣ perX .equality ∣ (x₂ , x₄))
              (sym (cong (λ x → pr₁ ⨾ x) (λ*3ComputationRule realizer a b c) ∙ pr₁pxy≡x _ _))
              (relX⊩isRelationalX x₁ x₂ x₃ x₄ _ _ _ ⊩x₁~x₂ ⊩x₁~x₃ ⊩x₃~x₄) ,
            subst
              (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x₂)
              (sym (cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) (λ*3ComputationRule realizer a b c) ∙ cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₁pxy≡x _ _))
              (relϕ⊩isRelationalϕ x₁ x₂ _ _ ⊩ϕx₁ ⊩x₁~x₂) ,
            subst
              (λ r' → r' ⊩ ∣ ψ .predicate ∣ x₂)
              (sym (cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) (λ*3ComputationRule realizer a b c) ∙ cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₂pxy≡y _ _))
              (relψ⊩isRelationalψ x₁ x₂ _ _ ⊩ψx₁ ⊩x₁~x₂)})
    isFunctionalRelation.isSingleValued (isFuncRel funcRel) =
      do
        (svX , svX⊩isSingleValuedX) ← idFuncRel perX .isSingleValued
        (relψ , relψ⊩isRelationalψ) ← ψ .isRelational
        let
          realizer : ApplStrTerm as 2
          realizer = ` pair ̇ (` svX ̇ (` pr₁ ̇ # one) ̇ (` pr₁ ̇ # zero)) ̇ (` relψ ̇ (` pr₂ ̇ (` pr₂ ̇ # one)) ̇ (` pr₁ ̇ # one))
        return
          (λ*2 realizer ,
          (λ { x₁ x₂ x₃ r₁ r₂ (⊩x₁~x₂ , ⊩ϕx , ⊩ψx) (⊩x₁~x₃ , ⊩'ϕx , ⊩'ψx) →
            (subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x₂ , x₃)) (sym (cong (λ x → pr₁ ⨾ x) (λ*2ComputationRule realizer r₁ r₂) ∙ pr₁pxy≡x _ _)) (svX⊩isSingleValuedX x₁ x₂ x₃ _ _ ⊩x₁~x₂ ⊩x₁~x₃)) ,
             subst (λ r' → r' ⊩ ∣ ψ .predicate ∣ x₂) (sym (cong (λ x → pr₂ ⨾ x) (λ*2ComputationRule realizer r₁ r₂) ∙ pr₂pxy≡y _ _)) (relψ⊩isRelationalψ x₁ x₂ _ _ ⊩ψx ⊩x₁~x₂)}))
    isFunctionalRelation.isTotal (isFuncRel funcRel) =
      do
        (tl , tl⊩isTotalIncψ) ← incψ .isTotal
        (s , s⊩ϕ≤ψ) ← ϕ≤ψ
        let
          realizer : ApplStrTerm as 1
          realizer = ` pair ̇ (` pr₁ ̇ # zero) ̇ (` pair ̇ (` pr₂ ̇ # zero) ̇ (` s ̇ (` pr₂ ̇ # zero)))
        return
          (λ* realizer ,
          (λ { x r (⊩x~x , ⊩ϕx) →
            return
              (x ,
              subst
                (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
                (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _))
                ⊩x~x ,
              subst
                (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x)
                (sym (cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) (λ*ComputationRule realizer r) ∙ cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₁pxy≡x _ _))
                ⊩ϕx ,
              subst
                (λ r' → r' ⊩ ∣ ψ .predicate ∣ x)
                (sym (cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) (λ*ComputationRule realizer r) ∙ cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₂pxy≡y _ _))
                (s⊩ϕ≤ψ x _ ⊩ϕx))}))
    
    funcRel⋆incψ≡incϕ : [ funcRel ] ⋆ [ incψ ] ≡ [ incϕ ]
    funcRel⋆incψ≡incϕ =
      let
        answer =
          do
            (t , t⊩isTransitiveX) ← perX .isTransitive
            let
              realizer : ApplStrTerm as 1
              realizer = ` pair ̇ (` t ̇ (` pr₁ ̇ (` pr₁ ̇ # zero)) ̇ (` pr₁ ̇ (` pr₂ ̇ # zero))) ̇ (` pr₁ ̇ (` pr₂ ̇ (` pr₁ ̇ # zero)))
            return
              (λ* realizer ,
              (λ { x x' r ⊩∃x'' →
                transport
                  (propTruncIdempotent (isPropΣ (perX .equality .isPropValued _ _) λ _ → ϕ .predicate .isPropValued _ _))
                  (do
                    (x'' , (⊩x~x'' , ⊩ϕx , ⊩ψx) , (⊩x''~x' , ⊩'ψx)) ← ⊩∃x''
                    return
                      ((subst
                        (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x'))
                        (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _))
                        (t⊩isTransitiveX x x'' x' _ _ ⊩x~x'' ⊩x''~x')) ,
                       (subst
                         (λ r' → r' ⊩ ∣ ϕ .predicate ∣ x)
                         (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _))
                         ⊩ϕx)))}))
      in
      eq/ _ _ (answer , F≤G→G≤F perϕ perX (composeFuncRel _ _ _ funcRel incψ) incϕ answer)

    ϕ≤ψ→SubObjHom : SubObjHom ϕsubObject ψsubObject
    ϕ≤ψ→SubObjHom =
      slicehom [ funcRel ] funcRel⋆incψ≡incϕ

  SubObjHom≃ϕ≤ψ : SubObjHom ϕsubObject ψsubObject ≃ (ϕ .predicate ≤ ψ .predicate)
  SubObjHom≃ϕ≤ψ =
    propBiimpl→Equiv
      (isPropSubObjMor RT (X , perX) ϕsubObject ψsubObject)
      (isProp≤ (ϕ .predicate) (ψ .predicate))
      SubObjHom→ϕ≤ψ
      ϕ≤ψ→SubObjHom

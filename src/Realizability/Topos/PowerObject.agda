open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Pullback
open import Realizability.PropResizing
open import Realizability.CombinatoryAlgebra

module Realizability.Topos.PowerObject
  {ℓ}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  (resizing : hPropResizing ℓ)
  where
  
open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ} {ℓ'' = ℓ} ca
open import Realizability.Tripos.Prealgebra.Meets.Identity {ℓ' = ℓ} {ℓ'' = ℓ} ca
open import Realizability.Topos.Object {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial 
open import Realizability.Topos.FunctionalRelation {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.Equalizer {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.BinProducts {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.MonicReprFuncRel {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.StrictRelation {ℓ' = ℓ} {ℓ'' = ℓ} ca isNonTrivial
open import Realizability.Topos.ResizedPredicate ca isNonTrivial resizing

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate renaming (isSetX to isSetPredicateBase)
open Morphism
open PartialEquivalenceRelation
open FunctionalRelation
open Category RT
open StrictRelation

-- Power object of X

module _ (X : Type ℓ) (perX : PartialEquivalenceRelation X) where
  open ResizedPredicateProps perX

  𝓟 : PartialEquivalenceRelation (ResizedPredicate X)
  Predicate.isSetX (equality 𝓟) = isSet× isSetResizedPredicate isSetResizedPredicate
  Predicate.∣ equality 𝓟 ∣ (ϕ , ψ) r =
    (pr₁ ⨾ (pr₁ ⨾ r)) ⊩ isStrictResizedPredicate ϕ ×
    (pr₂ ⨾ (pr₁ ⨾ r)) ⊩ isRelationalResizedPredicate ϕ ×
    (pr₁ ⨾ (pr₂ ⨾ r)) ⊩ entailmentResizedPredicate ϕ ψ ×
    (pr₂ ⨾ (pr₂ ⨾ r)) ⊩ entailmentResizedPredicate ψ ϕ
  Predicate.isPropValued (equality 𝓟) (ϕ , ψ) r =
    isProp× (isPropIsStrictResizedPredicate ϕ (pr₁ ⨾ (pr₁ ⨾ r)))
      (isProp× (isPropIsRelationalResizedPredicate ϕ (pr₂ ⨾ (pr₁ ⨾ r)))
        (isProp×
          (isPropEntailmentResizedPredicate ϕ ψ (pr₁ ⨾ (pr₂ ⨾ r)))
          (isPropEntailmentResizedPredicate ψ ϕ (pr₂ ⨾ (pr₂ ⨾ r)))))
  isPartialEquivalenceRelation.isSetX (isPerEquality 𝓟) = isSetResizedPredicate
  isPartialEquivalenceRelation.isSymmetric (isPerEquality 𝓟) =
    do
      let
        strictness : ApplStrTerm as 2
        strictness = ` pr₁ ̇ (` pr₁ ̇ # zero) ̇ (` pr₂ ̇ (` pr₂ ̇ # zero) ̇ # one)

        proj : ApplStrTerm as 3
        proj = # two

        proj' : ApplStrTerm as 2
        proj' = ` pr₂ ̇ (` pr₂ ̇ # zero) ̇ # one

        proj'' : ApplStrTerm as 2
        proj'' = ` pr₁ ̇ (` pr₂ ̇ # zero) ̇ # one

        realizer : ApplStrTerm as 1
        realizer = ` pair ̇ (` pair ̇ λ*abst strictness ̇ λ*abst (λ*abst proj)) ̇ (` pair ̇ λ*abst proj' ̇ λ*abst proj'')
      return
        (λ* realizer ,
        (λ { ϕ ψ r (⊩isStrictϕ , isRelationalϕ , ⊩ϕ≤ψ , ⊩ψ≤ϕ) →
          (λ x a ⊩ψx →
            subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym {!!}) (⊩isStrictϕ x _ (⊩ψ≤ϕ x a ⊩ψx))) ,
          (λ x x' a b ⊩x~x' ⊩ψx →
            subst (λ r' → r' ⊩ ∣ toPredicate ψ ∣ x') (sym {!!}) (⊩ϕ≤ψ x' _ (isRelationalϕ x x' _ _ ⊩x~x' (⊩ψ≤ϕ x _ ⊩ψx)))) ,
          (λ x a ⊩ψx → subst (λ r' → r' ⊩ ∣ toPredicate ϕ ∣ x) (sym {!!}) (⊩ψ≤ϕ x a ⊩ψx)) ,
          (λ x a ⊩ϕx → subst (λ r' → r' ⊩ ∣ toPredicate ψ ∣ x) (sym {!!}) (⊩ϕ≤ψ x a ⊩ϕx)) }))
  isPartialEquivalenceRelation.isTransitive (isPerEquality 𝓟) =
    do
      return
        ({!!} ,
        (λ {
          ϕ ψ θ a b
          (⊩isStrictϕ , ⊩isRelationalϕ , ⊩ϕ≤ψ , ⊩ψ≤ϕ)
          (⊩isStrictψ , ⊩isRelationalψ , ⊩ψ≤θ , ⊩θ≤ψ) →
            subst (λ r' → r' ⊩ isStrictResizedPredicate ϕ) {!!} ⊩isStrictϕ ,
            subst (λ r' → r' ⊩ isRelationalResizedPredicate ϕ) {!!} ⊩isRelationalϕ ,
            (λ x r ⊩ϕx → subst (λ r' → r' ⊩ ∣ toPredicate θ ∣ x) {!!} (⊩ψ≤θ x _ (⊩ϕ≤ψ x r ⊩ϕx))) ,
            (λ x r ⊩θx → subst (λ r' → r' ⊩ ∣ toPredicate ϕ ∣ x) {!!} (⊩ψ≤ϕ x _ (⊩θ≤ψ x r ⊩θx))) }))

  opaque
    unfolding binProdObRT
    ∈StrictRel : StrictRelation (binProdObRT perX 𝓟)
    Predicate.isSetX (StrictRelation.predicate ∈StrictRel) = isSet× (perX .isSetX) isSetResizedPredicate
    Predicate.∣ StrictRelation.predicate ∈StrictRel ∣ (x , ϕ) r = (pr₁ ⨾ r) ⊩ ∣ 𝓟 .equality ∣ (ϕ , ϕ) × (pr₂ ⨾ r) ⊩ ∣ toPredicate ϕ ∣ x
    Predicate.isPropValued (StrictRelation.predicate ∈StrictRel) (x , ϕ) r =
      isProp× (𝓟 .equality .isPropValued (ϕ , ϕ) (pr₁ ⨾ r)) (toPredicate ϕ .isPropValued _ _)
    isStrictRelation.isStrict (StrictRelation.isStrictRelationPredicate ∈StrictRel) =
      do
        return
          ({!!} ,
          λ { (x , ϕ) r ((⊩isStrictϕ , ⊩isRelationalϕ , ⊩ϕ≤ϕ , ⊩'ϕ≤ϕ) , ⊩ϕx) →
            subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) {!!} (⊩isStrictϕ x _ ⊩ϕx) ,
            subst (λ r' → r' ⊩ isStrictResizedPredicate ϕ) {!!} ⊩isStrictϕ ,
            subst (λ r' → r' ⊩ isRelationalResizedPredicate ϕ) {!!} ⊩isRelationalϕ ,
            subst (λ r' → r' ⊩ entailmentResizedPredicate ϕ ϕ) {!!} ⊩ϕ≤ϕ ,
            subst (λ r' → r' ⊩ entailmentResizedPredicate ϕ ϕ) {!!} ⊩'ϕ≤ϕ })
    isStrictRelation.isRelational (StrictRelation.isStrictRelationPredicate ∈StrictRel) =
      do
        return
          ({!!} ,
          λ { (x , ϕ) (x' , ψ) a b ((⊩isStrictϕ , ⊩isRelationalϕ , ⊩ϕ≤ϕ , ⊩'ϕ≤ϕ) , ⊩ϕx) (⊩x~x' , (⊩isStrict'ϕ , ⊩isRelational'ϕ , ⊩ϕ≤ψ , ⊩ψ≤ϕ)) →
            ((λ x'' r ⊩ψx'' →
              subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x'' , x'')) {!!} (⊩isStrictϕ x'' _ (⊩ψ≤ϕ x'' r ⊩ψx''))) ,
             (λ x'' x''' p q ⊩x''~x''' ⊩ψx'' →
               subst (λ r' → r' ⊩ ∣ toPredicate ψ ∣ x''') (sym {!!}) (⊩ϕ≤ψ x''' _ (⊩isRelationalϕ x'' x''' _ _ ⊩x''~x''' (⊩ψ≤ϕ x'' _ ⊩ψx'')))) ,
             (λ x'' r ⊩ψx'' → subst (λ r' → r' ⊩ ∣ toPredicate ψ ∣ x'') {!!} ⊩ψx'') ,
             λ x'' r ⊩ψx'' → subst (λ r' → r' ⊩ ∣ toPredicate ψ ∣ x'') {!!} ⊩ψx'') ,
             subst (λ r' → r' ⊩ ∣ toPredicate ψ ∣ x') {!!} (⊩ϕ≤ψ x' _ (⊩isRelationalϕ x x' _ _ ⊩x~x' ⊩ϕx)) })

  open InducedSubobject (binProdObRT perX 𝓟) ∈StrictRel
    renaming
      ( subPer to ∈subPer
      ; incFuncRel to ∈incFuncRel
      ; isInjectiveIncFuncRel to isInjective∈IncFuncRel
      ; isMonicInc to isMonicInc∈)

  {-
  We need to show that the following is a pullback diagram and that [ F ] is the *unique* RT arrow that
  makes this diagram a pullback.

                [ top ] 
    (X × Y)ϕ - - - - - - - - - -> ∈ₓ
       Γ _|                       Γ
       |                          |
       |                          |
       |                          |
       | [ incϕ ]                 | [ inc∈ ]
       |                          |
       |                          |
       |                          |
    (X × Y)  - - - - - - - - - -> (X × 𝓟 X)
                idₓ × [ F ]
  -}
  module PowerObjectUnivProp
    {Y : Type ℓ}
    (perY : PartialEquivalenceRelation Y)
    (ϕ : StrictRelation (binProdObRT perX perY)) where

    open InducedSubobject (binProdObRT perX perY) ϕ
      renaming
        ( subPer to ϕsubPer
        ; incFuncRel to ϕincFuncRel
        ; isInjectiveIncFuncRel to isInjectiveϕIncFuncRel
        ; isMonicInc to isMonicIncϕ)

    opaque
      unfolding binProdObRT
      unfolding idFuncRel
      {-# TERMINATING #-}
      topArrowFuncRel : FunctionalRelation ϕsubPer ∈subPer
      Predicate.isSetX (relation topArrowFuncRel) = isSet× (isSet× (perX .isSetX) (perY .isSetX)) (isSet× (perX .isSetX) isSetResizedPredicate)
      Predicate.∣ relation topArrowFuncRel ∣ ((x , y) , (x' , p)) r =
        (pr₁ ⨾ r) ⊩ ∣ perX .equality ∣ (x , x') ×
        (pr₁ ⨾ (pr₂ ⨾ r)) ⊩ ∣ toPredicate p ∣ x ×
        (pr₂ ⨾ (pr₂ ⨾ r)) ⊩ ∣ ϕ .predicate ∣ (x , y)
      Predicate.isPropValued (relation topArrowFuncRel) ((x , y) , (x' , p)) r =
        isProp×
          (perX .equality .isPropValued _ _)
          (isProp×
            (toPredicate p .isPropValued _ _)
            (ϕ .predicate .isPropValued _ _))
      isFunctionalRelation.isStrictDomain (isFuncRel topArrowFuncRel) =
        do
          (stX , stX⊩isStrictDomainEqX) ← idFuncRel perX .isStrictDomain
          (stY , stY⊩isStrictDomainEqY) ← idFuncRel perY .isStrictDomain
          return
            ({!!} ,
            (λ { (x , y) (x' , p) r (⊩x~x' , ⊩ϕxy , ⊩px) →
              (subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) {!!} (stX⊩isStrictDomainEqX x x' _ ⊩x~x') ,
               {!subst !}) ,
               {!!}}))
      isFunctionalRelation.isStrictCodomain (isFuncRel topArrowFuncRel) = {!!}
      isFunctionalRelation.isRelational (isFuncRel topArrowFuncRel) = {!!}
      isFunctionalRelation.isSingleValued (isFuncRel topArrowFuncRel) = {!!}
      isFunctionalRelation.isTotal (isFuncRel topArrowFuncRel) = {!!}

    powerObjectCospan : RTMorphism (binProdObRT perX perY) (binProdObRT perX 𝓟) → Cospan RT
    Cospan.l (powerObjectCospan f) = X × Y , binProdObRT perX perY
    Cospan.m (powerObjectCospan f) = X × ResizedPredicate X , binProdObRT perX 𝓟
    Cospan.r (powerObjectCospan f) = X × ResizedPredicate X , ∈subPer
    Cospan.s₁ (powerObjectCospan f) = f
    Cospan.s₂ (powerObjectCospan f) = [ ∈incFuncRel ]

    F : FunctionalRelation (binProdObRT perX perY) (binProdObRT perX 𝓟)
    Predicate.isSetX (relation F) = isSet× (isSet× (perX .isSetX) (perY .isSetX)) (isSet× (perX .isSetX) isSetResizedPredicate)
    Predicate.∣ relation F ∣ ((x , y) , (x' , p)) r = (pr₁ ⨾ (pr₁ ⨾ r)) ⊩ ∣ perY .equality ∣ (y , y) × (pr₂ ⨾ (pr₁ ⨾ r)) ⊩ ∣ 𝓟 .equality ∣ (p , p) × {!∀ !} × {!!}
    Predicate.isPropValued (relation F) = {!!}
    isFunctionalRelation.isStrictDomain (isFuncRel F) = {!!}
    isFunctionalRelation.isStrictCodomain (isFuncRel F) = {!!}
    isFunctionalRelation.isRelational (isFuncRel F) = {!!}
    isFunctionalRelation.isSingleValued (isFuncRel F) = {!!}
    isFunctionalRelation.isTotal (isFuncRel F) = {!!}

    opaque
      unfolding composeRTMorphism
      unfolding composeFuncRel
      pullbackSquareCommutes : [ ϕincFuncRel ] ⋆ [ F ] ≡ [ topArrowFuncRel ] ⋆ [ ∈incFuncRel ]
      pullbackSquareCommutes =
        eq/ _ _ {!!}

    isPowerObjectUnivProp : Type _
    isPowerObjectUnivProp =
      ∃![ f ∈ RTMorphism (binProdObRT perX perY) (binProdObRT perX 𝓟) ]
        Σ[ commutes ∈ [ ϕincFuncRel ] ⋆ f ≡ [ topArrowFuncRel ] ⋆ [ ∈incFuncRel ] ] 
         (isPullback RT (powerObjectCospan f) {c = X × Y , ϕsubPer} [ ϕincFuncRel ] [ topArrowFuncRel ] commutes)

    isPropIsPowerObjectUnivProp : isProp isPowerObjectUnivProp
    isPropIsPowerObjectUnivProp = isPropIsContr

    isPowerObject : isPowerObjectUnivProp
    isPowerObject =
      uniqueExists
        [ F ]
        (pullbackSquareCommutes , {!!})
        (λ F' → isPropΣ (squash/ _ _) λ commutes → isPropIsPullback RT (powerObjectCospan F') [ ϕincFuncRel ] [ topArrowFuncRel ] commutes)
        (λ { f' (commutes , isPullback) →
           {!!} })

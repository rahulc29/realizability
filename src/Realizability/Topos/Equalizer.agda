{-

EQUALISERS IN RT(A)
────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────
────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────

Consider two parallel morphisms f g from (X, _=X_) to (Y , _=Y_)

In order to construct their equaliser we need to first construct an auxillary object (X , _=E_)
and construct the equaliser as an injection from (X , _=E_) to (X , _=X_)

However, we cannot, in general show that RT has equalisers because the object (X , _=E_) that injects into (X , _=X_) depends
on choice of representatives of f and g.

We can, however, prove a weaker theorem. We can show that equalisers *merely* exist.

More formally, we can show that ∃[ ob ∈ RTObject ] ∃[ eq ∈ RTMorphism ob (X , _=X_) ] (univPropEqualizer eq)

To do this, we firstly show the universal property for the case when we have already been given the
representatives.

It is possible to define things differently and quotient predicates by realizable equivalence but that causes type-checking time
to explode, so we do not do that here.

See also : Remark 2.7 of "Tripos Theory" by JHP

-}
open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm)
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinProduct

module Realizability.Topos.Equalizer
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

open FunctionalRelation
open PartialEquivalenceRelation

equalizerUnivProp :
  ∀ {X Y : Type ℓ'}
  → (perX : PartialEquivalenceRelation X)
  → (perY : PartialEquivalenceRelation Y)
  → (f g : RTMorphism perX perY)
  → (equalizerOb : PartialEquivalenceRelation X)
  → (inc : RTMorphism equalizerOb perX)
  → Type _
equalizerUnivProp {X} {Y} perX perY f g equalizerOb inc =
    ((composeRTMorphism _ _ _ inc f) ≡ (composeRTMorphism _ _ _ inc g)) ×
    ∀ {Z : Type ℓ'} (perZ : PartialEquivalenceRelation Z) (inc' : RTMorphism perZ perX)
    → (composeRTMorphism _ _ _ inc' f) ≡ (composeRTMorphism _ _ _ inc' g)
    -----------------------------------------------------------------------------------
    → ∃![ ! ∈ RTMorphism perZ equalizerOb ] (composeRTMorphism _ _ _ ! inc ≡ inc')

module _
  {X : Type ℓ'}
  {Y : Type ℓ'}
  (perX : PartialEquivalenceRelation X)
  (perY : PartialEquivalenceRelation Y)
  (f g : RTMorphism perX perY) where

  opaque
    equalizerPer : ∀ (F G : FunctionalRelation perX perY) → PartialEquivalenceRelation X
    equalizerPer F G =
      record
              { equality =
                record
                  { isSetX = isSet× (perX .isSetX) (perX .isSetX)
                  ; ∣_∣ = λ { (x , x') r →
                    ((pr₁ ⨾ r) ⊩ ∣ perX .equality ∣ (x , x')) ×
                    (∃[ y ∈ Y ] (pr₁ ⨾ (pr₂ ⨾ r)) ⊩ ∣ F .relation ∣ (x , y) × (pr₂ ⨾ (pr₂ ⨾ r)) ⊩ ∣ G .relation ∣ (x , y)) }
                  ; isPropValued = λ { (x , x') r → isProp× (perX .equality .isPropValued _ _) isPropPropTrunc } }
              ; isPerEquality =
                record
                  { isSetX = perX .isSetX
                  ; isSymmetric =
                    do
                      (s , s⊩isSymmetricX) ← perX .isSymmetric
                      (relF , relF⊩isRelationalF) ← F .isRelational
                      (relG , relG⊩isRelationalG) ← G .isRelational
                      (stFC , stFC⊩isStrictCodomainF) ← F .isStrictCodomain
                      let
                        prover : ApplStrTerm as 1
                        prover =
                          ` pair ̇
                            (` s ̇ (` pr₁ ̇ # zero)) ̇
                            (` pair ̇
                              (` relF ̇ (` pr₁ ̇ # zero) ̇ (` pr₁ ̇ (` pr₂ ̇ # zero)) ̇ (` stFC ̇ (` pr₁ ̇ (` pr₂ ̇ # zero)))) ̇
                              (` relG ̇ (` pr₁ ̇ # zero) ̇ (` pr₂ ̇ (` pr₂ ̇ # zero)) ̇ (` stFC ̇ (` pr₁ ̇ (` pr₂ ̇ # zero)))))
                      return
                        (λ* prover ,
                        (λ { x x' r (pr₁r⊩x~x' , pr₂r⊩∃) →
                          subst
                            (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x))
                            (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover r) ∙ pr₁pxy≡x _ _))
                            (s⊩isSymmetricX x x' (pr₁ ⨾ r) pr₁r⊩x~x') ,
                          do
                            (y , pr₁pr₂r⊩Fxy , pr₂pr₂r⊩Gxy) ← pr₂r⊩∃
                            return
                              (y ,
                              subst
                                (λ r' → r' ⊩ ∣ F .relation ∣ (x' , y))
                                (sym (cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) (λ*ComputationRule prover r) ∙ cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₁pxy≡x _ _))
                                (relF⊩isRelationalF
                                  x x' y y
                                  (pr₁ ⨾ r) (pr₁ ⨾ (pr₂ ⨾ r)) (stFC ⨾ (pr₁ ⨾ (pr₂ ⨾ r)))
                                  pr₁r⊩x~x'
                                  pr₁pr₂r⊩Fxy
                                  (stFC⊩isStrictCodomainF x y (pr₁ ⨾ (pr₂ ⨾ r)) pr₁pr₂r⊩Fxy)) ,
                              subst
                                (λ r' → r' ⊩ ∣ G .relation ∣ (x' , y))
                                (sym (cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) (λ*ComputationRule prover r) ∙ cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₂pxy≡y _ _))
                                (relG⊩isRelationalG
                                  x x' y y
                                  (pr₁ ⨾ r) (pr₂ ⨾ (pr₂ ⨾ r)) (stFC ⨾ (pr₁ ⨾ (pr₂ ⨾ r)))
                                  pr₁r⊩x~x'
                                  pr₂pr₂r⊩Gxy
                                  (stFC⊩isStrictCodomainF x y (pr₁ ⨾ (pr₂ ⨾ r)) pr₁pr₂r⊩Fxy))) }))
                  ; isTransitive =
                    do
                      (t , t⊩isTransitiveX) ← perX .isTransitive
                      (relF , relF⊩isRelationalF) ← F .isRelational
                      (relG , relG⊩isRelationalG) ← G .isRelational
                      let
                        prover : ApplStrTerm as 2
                        prover = ` pair ̇ (` t ̇ (` pr₁ ̇ # one) ̇ (` pr₁ ̇ # zero)) ̇ (` pair ̇ (` pr₁ ̇ (` pr₂ ̇ # one)) ̇ (` pr₂ ̇ (` pr₂ ̇ # one)))
                      return
                        (λ*2 prover ,
                        λ { x₁ x₂ x₃ a b (pr₁a⊩x₁~x₂ , pr₂a⊩∃) (pr₁b⊩x₂~x₃ , pr₂b⊩∃) →
                          subst
                            (λ r' → r' ⊩ ∣ perX .equality ∣ (x₁ , x₃))
                            (sym (cong (λ x → pr₁ ⨾ x) (λ*2ComputationRule prover a b) ∙ pr₁pxy≡x _ _))
                            (t⊩isTransitiveX x₁ x₂ x₃ (pr₁ ⨾ a) (pr₁ ⨾ b) pr₁a⊩x₁~x₂ pr₁b⊩x₂~x₃) ,
                          do
                            (y , (pr₁pr₂a⊩Fx₁y , pr₂pr₂a⊩Gx₁y)) ← pr₂a⊩∃
                            (y' , (pr₁pr₂a⊩Fx₂y' , pr₂pr₂a⊩Gx₂y')) ← pr₂b⊩∃
                            return
                              (y ,
                              subst
                                (λ r' → r' ⊩ ∣ F .relation ∣ (x₁ , y))
                                (sym (cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) (λ*2ComputationRule prover a b) ∙ cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₁pxy≡x _ _))
                                pr₁pr₂a⊩Fx₁y ,
                              subst
                                (λ r' → r' ⊩ ∣ G .relation ∣ (x₁ , y))
                                (sym (cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) (λ*2ComputationRule prover a b) ∙ cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₂pxy≡y _ _))
                                pr₂pr₂a⊩Gx₁y) }) } }

  opaque
    unfolding idFuncRel
    unfolding equalizerPer
    equalizerFuncRel : ∀ (F G : FunctionalRelation perX perY) → FunctionalRelation (equalizerPer F G) perX
    equalizerFuncRel F G =
      record
        { relation = equalizerPer F G .equality
        ; isFuncRel =
          record
           { isStrictDomain = idFuncRel (equalizerPer F G) .isStrictDomain
           ; isStrictCodomain =
             do
               (stC , stC⊩isStrictCodomain) ← idFuncRel perX .isStrictCodomain
               let
                 prover : ApplStrTerm as 1
                 prover = ` stC ̇ (` pr₁ ̇ # zero)
               return
                 (λ* prover ,
                 (λ { x x' r (pr₁r⊩x~x' , pr₂r⊩∃) →
                   subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x')) (sym (λ*ComputationRule prover r)) (stC⊩isStrictCodomain x x' (pr₁ ⨾ r) pr₁r⊩x~x') }))
           ; isRelational =
             do
               (relEqX , relEqX⊩isRelationalEqX) ← idFuncRel perX .isRelational
               (relF , relF⊩isRelationalF) ← F .isRelational
               (relG , relG⊩isRelationalG) ← G .isRelational
               (svF , svF⊩isSingleValuedF) ← F .isSingleValued
               let
                 prover : ApplStrTerm as 3
                 prover =
                   ` pair ̇
                     (` relEqX ̇ (` pr₁ ̇ # two) ̇ (` pr₁ ̇ # one) ̇ # zero) ̇
                     (` pair ̇
                       (` relF ̇ (` pr₁ ̇ # two) ̇ (` pr₁ ̇ (` pr₂ ̇ # two)) ̇ (` svF ̇ (` pr₁ ̇ (` pr₂ ̇ # two)) ̇ (` pr₁ ̇ (` pr₂ ̇ # one)))) ̇
                       (` relG ̇ (` pr₁ ̇ # two) ̇ (` pr₂ ̇ (` pr₂ ̇ # two)) ̇ (` svF ̇ (` pr₁ ̇ (` pr₂ ̇ # two)) ̇ (` pr₁ ̇ (` pr₂ ̇ # one)))))
               return
                 (λ*3 prover ,
                 (λ x₁ x₂ x₃ x₄ a b c (pr₁a⊩x₁~x₂ , pr₂a⊩) (pr₁b⊩x₁~x₃ , pr₂b⊩) c⊩x₃~x₄ →
                   subst
                     (λ r' → r' ⊩ ∣ perX .equality ∣ (x₂ , x₄))
                     (sym (cong (λ x → pr₁ ⨾ x) (λ*3ComputationRule prover a b c) ∙ pr₁pxy≡x _ _))
                     (relEqX⊩isRelationalEqX x₁ x₂ x₃ x₄ (pr₁ ⨾ a) (pr₁ ⨾ b) c pr₁a⊩x₁~x₂ pr₁b⊩x₁~x₃ c⊩x₃~x₄) ,
                   do
                     (y , pr₁pr₂a⊩Fx₁y , pr₂pr₂a⊩Gx₁y) ← pr₂a⊩
                     (y' , pr₁pr₂b⊩Fx₁y' , pr₂pr₂b⊩Gx₁y') ← pr₂b⊩
                     let
                       y~y' = svF⊩isSingleValuedF x₁ y y' (pr₁ ⨾ (pr₂ ⨾ a)) (pr₁ ⨾ (pr₂ ⨾ b)) pr₁pr₂a⊩Fx₁y pr₁pr₂b⊩Fx₁y'
                     return
                       (y' ,
                       subst
                         (λ r' → r' ⊩ ∣ F .relation ∣ (x₂ , y'))
                         (sym (cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) (λ*3ComputationRule prover a b c) ∙ cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₁pxy≡x _ _))
                         (relF⊩isRelationalF
                           x₁ x₂ y y'
                           (pr₁ ⨾ a) (pr₁ ⨾ (pr₂ ⨾ a)) (svF ⨾ (pr₁ ⨾ (pr₂ ⨾ a)) ⨾ (pr₁ ⨾ (pr₂ ⨾ b)))
                           pr₁a⊩x₁~x₂ pr₁pr₂a⊩Fx₁y y~y') ,
                       subst
                         (λ r' → r' ⊩ ∣ G .relation ∣ (x₂ , y'))
                         (sym (cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) (λ*3ComputationRule prover a b c) ∙ cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₂pxy≡y _ _))
                         (relG⊩isRelationalG
                           x₁ x₂ y y'
                           (pr₁ ⨾ a) (pr₂ ⨾ (pr₂ ⨾ a)) (svF ⨾ (pr₁ ⨾ (pr₂ ⨾ a)) ⨾ (pr₁ ⨾ (pr₂ ⨾ b)))
                           pr₁a⊩x₁~x₂ pr₂pr₂a⊩Gx₁y y~y'))))
           ; isSingleValued =
             do
               (svEqX , svEqX⊩isSingleValuedEqX) ← idFuncRel perX .isSingleValued
               let
                 prover : ApplStrTerm as 2
                 prover = ` svEqX ̇ (` pr₁ ̇ # one) ̇ (` pr₁ ̇ # zero)
               return
                 (λ*2 prover ,
                 (λ x₁ x₂ x₃ r₁ r₂ (pr₁r₁⊩x₁~x₂ , pr₁r₁⊩) (pr₁r₂⊩x₁~x₃ , pr₂r₂⊩) →
                   subst
                     (λ r' → r' ⊩ ∣ perX .equality ∣ (x₂ , x₃))
                     (sym (λ*2ComputationRule prover r₁ r₂))
                     (svEqX⊩isSingleValuedEqX x₁ x₂ x₃ (pr₁ ⨾ r₁) (pr₁ ⨾ r₂) pr₁r₁⊩x₁~x₂ pr₁r₂⊩x₁~x₃)))
           ; isTotal = idFuncRel (equalizerPer F G) .isTotal
           } }

  opaque
    equalizerMorphism : ∀ (F G : FunctionalRelation perX perY) → RTMorphism (equalizerPer F G) perX
    equalizerMorphism F G = [ equalizerFuncRel F G ]

  opaque
    unfolding equalizerMorphism
    unfolding equalizerFuncRel
    unfolding composeRTMorphism
    inc⋆f≡inc⋆g : ∀ (F G : FunctionalRelation perX perY) → composeRTMorphism _ _ _ (equalizerMorphism F G) [ F ] ≡ composeRTMorphism _ _ _ (equalizerMorphism F G) [ G ]
    inc⋆f≡inc⋆g F G =
      let
        answer =
          do
            (relG , relG⊩isRelationalG) ← G .isRelational
            (svF , svF⊩isSingleValuedF) ← F .isSingleValued
            (relF , relF⊩isRelationalF) ← F .isRelational
            (sX , sX⊩isSymmetricX) ← perX .isSymmetric
            (stCF , stCF⊩isStrictCodomainF) ← F .isStrictCodomain
            let
              realizer : ApplStrTerm as 1
              realizer =
                ` pair ̇
                  (` pair ̇ (` pr₁ ̇ (` pr₁ ̇ # zero)) ̇ (` pair ̇ (` pr₁ ̇ (` pr₂ ̇ (` pr₁ ̇ # zero))) ̇ (` pr₂ ̇ (` pr₂ ̇ (` pr₁ ̇ # zero))))) ̇
                  (` relG ̇ (` pr₁ ̇ (` pr₁ ̇ # zero)) ̇ (` pr₂ ̇ (` pr₂ ̇ (` pr₁ ̇ # zero))) ̇
                     (` svF ̇ (` pr₁ ̇ (` pr₂ ̇ (` pr₁ ̇ # zero))) ̇
                     (` relF ̇ (` sX ̇ (` pr₁ ̇ (` pr₁ ̇ # zero))) ̇ (` pr₂ ̇ # zero) ̇ (` stCF ̇ (` pr₂ ̇ # zero)))))
            return
              (λ* realizer ,
              -- unfold everything and bring it back in together
              (λ x y r r⊩∃ →
                do
                  (x' , (⊩x~x' , ∃y) , ⊩Fx'y) ← r⊩∃
                  (y' , ⊩Fxy' , ⊩Gxy') ← ∃y
                  let
                    y'~y =
                      svF⊩isSingleValuedF x y' y _ _ ⊩Fxy' (relF⊩isRelationalF x' x y y _ _ _ (sX⊩isSymmetricX x x' _ ⊩x~x') ⊩Fx'y (stCF⊩isStrictCodomainF x' y _ ⊩Fx'y))
                  return
                    (x' ,
                    (subst
                      (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x'))
                      (sym (cong (λ x → pr₁ ⨾ (pr₁ ⨾ x)) (λ*ComputationRule realizer r) ∙ cong (λ x → pr₁ ⨾ x) (pr₁pxy≡x _ _) ∙ pr₁pxy≡x _ _))
                      ⊩x~x' ,
                    do
                      return
                        (y' ,
                        subst
                          (λ r' → r' ⊩ ∣ F .relation ∣ (x , y'))
                          (sym
                            (cong (λ x → pr₁ ⨾ (pr₂ ⨾ (pr₁ ⨾ x))) (λ*ComputationRule realizer r) ∙
                             cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) (pr₁pxy≡x _ _) ∙
                             cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ∙
                             pr₁pxy≡x _ _))
                          ⊩Fxy' ,
                        subst
                          (λ r' → r' ⊩ ∣ G .relation ∣ (x , y'))
                          (sym
                            (cong (λ x → pr₂ ⨾ (pr₂ ⨾ (pr₁ ⨾ x))) (λ*ComputationRule realizer r) ∙
                             cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) (pr₁pxy≡x _ _) ∙
                             cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ∙
                             pr₂pxy≡y _ _))
                          ⊩Gxy')) ,
                    subst
                      (λ r' → r' ⊩ ∣ G .relation ∣ (x' , y))
                      (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _))
                      (relG⊩isRelationalG x x' y' y _ _ _ ⊩x~x' ⊩Gxy' y'~y))))
      in
      eq/ _ _
        (answer , F≤G→G≤F (equalizerPer F G) perY (composeFuncRel _ _ _ (equalizerFuncRel F G) F) (composeFuncRel _ _ _ (equalizerFuncRel F G) G) answer)

  module UnivProp
    (F G : FunctionalRelation perX perY)
    {Z : Type ℓ'}
    (perZ : PartialEquivalenceRelation Z)
    (h : RTMorphism perZ perX)
    (h⋆f≡h⋆g : composeRTMorphism _ _ _ h [ F ] ≡ composeRTMorphism _ _ _ h [ G ]) where opaque
    unfolding equalizerPer
    unfolding composeRTMorphism
    unfolding equalizerMorphism
    unfolding equalizerFuncRel
    
    private
      !funcRel : ∀ (H : FunctionalRelation perZ perX) (H⋆F≡H⋆G : composeRTMorphism _ _ _ [ H ] [ F ] ≡ composeRTMorphism _ _ _ [ H ] [ G ]) → FunctionalRelation perZ (equalizerPer F G)
      !funcRel H H⋆F≡H⋆G =
        let
          (p , q) =
            SQ.effective
              (isPropValuedBientailment perZ perY)
              (isEquivRelBientailment perZ perY)
              (composeFuncRel _ _ _ H F)
              (composeFuncRel _ _ _ H G)
              H⋆F≡H⋆G
        in
        record
              { relation = H .relation
              ; isFuncRel =
                record
                 { isStrictDomain = H .isStrictDomain
                 ; isStrictCodomain =
                   do
                     (p , p⊩H⋆F≤H⋆G) ← p
                     (q , q⊩H⋆G≤H⋆F) ← q
                     (tlF , tlF⊩isTotalF) ← F .isTotal
                     (stCH , stCH⊩isStrictCodomainH) ← H .isStrictCodomain
                     (relG , relG⊩isRelationalG) ← G .isRelational
                     (svH , svH⊩isSingleValuedH) ← H .isSingleValued
                     (stCF , stCF⊩isStrictCodomainF) ← F .isStrictCodomain
                     let
                       -- possibly the ugliest realizer out there
                       prover : ApplStrTerm as 1
                       prover =
                         ` pair ̇
                           (` stCH ̇ # zero) ̇
                           (` pair ̇
                             (` tlF ̇ (` stCH ̇ # zero)) ̇
                             (` relG ̇ (` svH ̇ (` pr₁ ̇ (` p ̇ (` pair ̇ # zero ̇ (` tlF ̇ (` stCH ̇ # zero))))) ̇ # zero) ̇
                             (` pr₂ ̇ (` p ̇ (` pair ̇ # zero ̇ (` tlF ̇ (` stCH ̇ # zero))))) ̇
                              (` stCF ̇ (` tlF ̇ (` stCH ̇ # zero)))))
                     return
                       (λ* prover ,
                       (λ z x r r⊩Hzx →
                         let
                             x~x = stCH⊩isStrictCodomainH z x r r⊩Hzx
                         in
                         subst (λ r → r ⊩ ∣ perX .equality ∣ (x , x)) (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover r) ∙ pr₁pxy≡x _ _)) x~x ,
                         (do
                           (y , ⊩Fxy) ← tlF⊩isTotalF x (stCH ⨾ r) x~x
                           let
                             hope =
                               p⊩H⋆F≤H⋆G
                                 z y (pair ⨾ r ⨾ (tlF ⨾ (stCH ⨾ r)))
                                 (return
                                   (x ,
                                    subst (λ r' → r' ⊩ ∣ H .relation ∣ (z , x)) (sym (pr₁pxy≡x _ _)) r⊩Hzx ,
                                    subst (λ r' → r' ⊩ ∣ F .relation ∣ (x , y)) (sym (pr₂pxy≡y _ _)) ⊩Fxy))
                           return
                             (y ,
                             subst
                               (λ r' → r' ⊩ ∣ F .relation ∣ (x , y))
                               (sym
                                 (cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) (λ*ComputationRule prover r) ∙
                                  cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ∙
                                  pr₁pxy≡x _ _))
                               ⊩Fxy ,
                             -- god I wish there was a better way to do this :(
                             transport
                               (propTruncIdempotent (G .relation .isPropValued _ _))
                               (do
                                 (x' , ⊩Hzx' , ⊩Gx'y) ← hope
                                 return
                                   (subst
                                     (λ r' → r' ⊩ ∣ G .relation ∣ (x , y))
                                     (sym
                                       (cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) (λ*ComputationRule prover r) ∙
                                        cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ∙
                                        pr₂pxy≡y _ _))
                                     (relG⊩isRelationalG x' x y y _ _ _ (svH⊩isSingleValuedH z x' x _ _ ⊩Hzx' r⊩Hzx) ⊩Gx'y (stCF⊩isStrictCodomainF x y _ ⊩Fxy))))))))
                 ; isRelational =
                   do
                     (relH , relH⊩isRelationalH) ← H .isRelational
                     let
                       prover : ApplStrTerm as 3
                       prover = ` relH ̇ # two ̇ # one ̇ (` pr₁ ̇ # zero)
                     return
                       (λ*3 prover ,
                       (λ z z' x x' a b c a⊩z~z' b⊩Hzx (pr₁c⊩x~x' , pr₂c⊩∃) →
                         subst
                           (λ r' → r' ⊩ ∣ H .relation ∣ (z' , x'))
                           (sym (λ*3ComputationRule prover a b c))
                           (relH⊩isRelationalH z z' x x' a b (pr₁ ⨾ c) a⊩z~z' b⊩Hzx pr₁c⊩x~x')))
                 ; isSingleValued =
                   do
                     (svH , svH⊩isSingleValuedH) ← H .isSingleValued
                     (tlF , tlF⊩isTotalF) ← F .isTotal
                     (tlG , tlG⊩isTotalG) ← G .isTotal
                     (stCH , stCH⊩isStrictCodomainH) ← H .isStrictCodomain
                     (stCF , stCF⊩isStrictCodomainF) ← F .isStrictCodomain
                     (relG , relG⊩isRelationalG) ← G .isRelational
                     (p , p⊩H⋆F≤H⋆G) ← p
                     let
                       prover : ApplStrTerm as 2
                       prover =
                         ` pair ̇
                           (` svH ̇ # one ̇ # zero) ̇
                           (` pair ̇
                             (` tlF ̇ (` stCH ̇ # one)) ̇
                             (` relG ̇ (` svH ̇ (` pr₁ ̇ (` p ̇ (` pair ̇ # one ̇ (` tlF ̇ (` stCH ̇ # one))))) ̇ # one) ̇
                               (` pr₂ ̇ (` p ̇ (` pair ̇ # one ̇ (` tlF ̇ (` stCH ̇ # one))))) ̇
                               (` stCF ̇(` tlF ̇ (` stCH ̇ # one)))))
                     return
                       (λ*2 prover ,
                       (λ z x x' r₁ r₂ r₁⊩Hzx r₂⊩Hzx' →
                         let
                           x~x' = svH⊩isSingleValuedH z x x' r₁ r₂ r₁⊩Hzx r₂⊩Hzx'
                           x~x = stCH⊩isStrictCodomainH z x r₁ r₁⊩Hzx
                         in
                         subst
                           (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x'))
                           (sym (cong (λ x → pr₁ ⨾ x) (λ*2ComputationRule prover r₁ r₂) ∙ pr₁pxy≡x _ _))
                           x~x' ,
                         do
                           (y , ⊩Fxy) ← tlF⊩isTotalF x _ x~x
                           let
                             y~y = stCF⊩isStrictCodomainF x y _ ⊩Fxy
                             hope =
                               p⊩H⋆F≤H⋆G z y
                               (pair ⨾ r₁ ⨾ (tlF ⨾ (stCH ⨾ r₁)))
                               (do
                                 return
                                   (x ,
                                   (subst (λ r' → r' ⊩ ∣ H .relation ∣ (z , x)) (sym (pr₁pxy≡x _ _)) r₁⊩Hzx) ,
                                   (subst (λ r' → r' ⊩ ∣ F .relation ∣ (x , y)) (sym (pr₂pxy≡y _ _)) ⊩Fxy)))
                           (x'' , ⊩Hzx'' , ⊩Gx''y) ← hope
                           -- Can not use the fact that x ≐ x''
                           let
                             x''~x = svH⊩isSingleValuedH z x'' x _ _ ⊩Hzx'' r₁⊩Hzx
                           return
                             (y ,
                             subst
                               (λ r' → r' ⊩ ∣ F .relation ∣ (x , y))
                               (sym
                                 (cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) (λ*2ComputationRule prover r₁ r₂) ∙
                                  cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ∙
                                  pr₁pxy≡x _ _)) ⊩Fxy ,
                             subst
                               (λ r' → r' ⊩ ∣ G .relation ∣ (x , y))
                               (sym
                                 (cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) (λ*2ComputationRule prover r₁ r₂) ∙
                                  cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ∙
                                  pr₂pxy≡y _ _))
                               (relG⊩isRelationalG x'' x y y _ _ _ x''~x ⊩Gx''y y~y))))
                 ; isTotal = H .isTotal
                 } }
                 
    mainMap :
      Σ[ ! ∈ RTMorphism perZ (equalizerPer F G) ]
        (composeRTMorphism _ _ _ ! (equalizerMorphism F G) ≡ h) ×
        (∀ (!' : RTMorphism perZ (equalizerPer F G)) (!'⋆inc≡h : composeRTMorphism _ _ _ !' (equalizerMorphism F G) ≡ h) → !' ≡ !)
    mainMap =
      SQ.elim
        {P =
          λ h →
          ∀ (h⋆f≡h⋆g : composeRTMorphism _ _ _ h [ F ] ≡ composeRTMorphism _ _ _ h [ G ])
          → Σ[ ! ∈ _ ] (composeRTMorphism _ _ _ ! (equalizerMorphism F G) ≡ h) ×
          (∀ (!' : RTMorphism perZ (equalizerPer F G)) (!'⋆inc≡h : composeRTMorphism _ _ _ !' (equalizerMorphism F G) ≡ h) → !' ≡ !)}
        (λ h → isSetΠ λ _ → isSetΣ squash/ λ ! → isSet× (isProp→isSet (squash/ _ _)) (isSetΠ λ !' → isSetΠ λ _ → isProp→isSet (squash/ !' !)))
        (λ H H⋆F≡H⋆G →
          [ !funcRel H H⋆F≡H⋆G ] ,
          let    
            answer =
              do
                (relH , relH⊩isRelationalH) ← H .isRelational
                (stDH , stDH⊩isStrictDomainH) ← H .isStrictDomain
                let
                  prover : ApplStrTerm as 1
                  prover = ` relH ̇ (` stDH ̇ (` pr₁ ̇ # zero)) ̇ (` pr₁ ̇ # zero) ̇ (` pr₁ ̇ (` pr₂ ̇ # zero))
                return
                  (λ* prover ,
                  (λ z x r r⊩∃x' →
                    transport
                      (propTruncIdempotent (H .relation .isPropValued _ _))
                      (do
                        (x' , pr₁r⊩Hzx' , (pr₁pr₂r⊩x'~x , _)) ← r⊩∃x'
                        return
                          (subst
                            (λ r' → r' ⊩ ∣ H .relation ∣ (z , x))
                            (sym (λ*ComputationRule prover r))
                            (relH⊩isRelationalH z z x' x _ _ _ (stDH⊩isStrictDomainH z x' (pr₁ ⨾ r) pr₁r⊩Hzx') pr₁r⊩Hzx' pr₁pr₂r⊩x'~x)))))
            !funcRel⋆inc≡H = eq/ _ _ (answer , F≤G→G≤F _ _ (composeFuncRel _ _ _ (!funcRel H H⋆F≡H⋆G) (equalizerFuncRel F G)) H answer)
          in !funcRel⋆inc≡H ,
          λ !' !'⋆inc≡H →
            SQ.elimProp
              {P =
                λ !' →
                ∀ (foo : composeRTMorphism _ _ _ !' (equalizerMorphism F G) ≡ [ H ])
                → !' ≡ [ !funcRel H H⋆F≡H⋆G ]}
              (λ !' → isPropΠ λ _ → squash/ _ _)
              (λ !'funcRel !'funcRel⋆inc≡H →
                let
                  (p , q) = SQ.effective (isPropValuedBientailment perZ perX) (isEquivRelBientailment perZ perX) (composeFuncRel _ _ _ !'funcRel (equalizerFuncRel F G)) H !'funcRel⋆inc≡H
                  (p' , q') = SQ.effective (isPropValuedBientailment perZ perY) (isEquivRelBientailment perZ perY) (composeFuncRel _ _ _ H F) (composeFuncRel _ _ _ H G) H⋆F≡H⋆G
                  answer =
                    do
                      (q , q⊩inc⋆!'≤H) ← q
                      (rel!' , rel!'⊩isRelational!'FuncRel) ← !'funcRel .isRelational
                      (stDH , stDH⊩isStrictDomainH) ← H .isStrictDomain
                      let
                        prover : ApplStrTerm as 1
                        prover = ` rel!' ̇ (` stDH ̇ # zero) ̇ (` pr₁ ̇ (` q ̇ # zero)) ̇ (` pr₂ ̇ (` q ̇ # zero))
                      return
                        (λ* prover ,
                        (λ z x r r⊩Hzx →
                          transport
                            (propTruncIdempotent (!'funcRel .relation .isPropValued _ _))
                            (do
                              (x' , pr₁qr⊩!'zx' , ⊩x~x' , foo) ← q⊩inc⋆!'≤H z x r r⊩Hzx
                              return
                                (subst
                                  (λ r' → r' ⊩ ∣ !'funcRel .relation ∣ (z , x))
                                  (sym (λ*ComputationRule prover r))
                                  (rel!'⊩isRelational!'FuncRel
                                    z z x' x _ _ _
                                    (stDH⊩isStrictDomainH z x r r⊩Hzx)
                                    pr₁qr⊩!'zx'
                                    (⊩x~x' , foo))))))
                in
                eq/ _ _ (F≤G→G≤F perZ (equalizerPer F G) (!funcRel H H⋆F≡H⋆G) !'funcRel answer , answer))
              !'
              !'⋆inc≡H)
        (λ { H H' (H≤H' , H'≤H) →
          funExtDep
            {A = λ i → composeRTMorphism _ _ _ (eq/ H H' (H≤H' , H'≤H) i) [ F ] ≡ composeRTMorphism _ _ _ (eq/ H H' (H≤H' , H'≤H) i) [ G ]}
            λ {H⋆F≡H⋆G} {H'⋆F≡H'⋆G} p →
              ΣPathPProp
                {A = λ i → RTMorphism perZ (equalizerPer F G)}
                {B = λ i ! →
                  ((composeRTMorphism _ _ _ ! (equalizerMorphism F G)) ≡ eq/ H H' (H≤H' , H'≤H) i) ×
                  (∀ (!' : RTMorphism perZ (equalizerPer F G)) → composeRTMorphism _ _ _ !' (equalizerMorphism F G) ≡ eq/ H H' (H≤H' , H'≤H) i → !' ≡ !)}
                (λ ! → isProp× (squash/ _ _) (isPropΠ λ !' → isPropΠ λ !'⋆inc≡H' → squash/ _ _))
                let
                  answer =
                    (do
                      (s , s⊩H≤H') ← H≤H'
                      return
                        (s ,
                        (λ z x r r⊩Hzx →
                          s⊩H≤H' z x r r⊩Hzx)))
                in eq/ _ _ (answer , F≤G→G≤F perZ (equalizerPer F G) (!funcRel H H⋆F≡H⋆G) (!funcRel H' H'⋆F≡H'⋆G) answer) })
        h
        h⋆f≡h⋆g
    
  -- We have now done the major work and can simply eliminate f and g
  opaque
    unfolding idFuncRel
    unfolding equalizerPer
    equalizer :
      ∃[ equalizerOb ∈ PartialEquivalenceRelation X ]
      ∃[ inc ∈ RTMorphism equalizerOb perX ]
      (equalizerUnivProp perX perY f g equalizerOb inc)
    equalizer =
      SQ.elimProp2
        {P = λ f g → ∃[ equalizerOb ∈ PartialEquivalenceRelation X ] ∃[ inc ∈ RTMorphism equalizerOb perX ] (equalizerUnivProp perX perY f g equalizerOb inc)}
        (λ f g → isPropPropTrunc)
        (λ F G →
            return
              ((equalizerPer F G) ,
              (return
                  ((equalizerMorphism F G) ,
                  ((inc⋆f≡inc⋆g F G) ,
                  (λ {Z} perZ inc' inc'⋆f≡inc'⋆g →
                    let
                      (! , !⋆inc≡inc' , unique!) = UnivProp.mainMap F G perZ inc' inc'⋆f≡inc'⋆g
                    in
                    uniqueExists
                      !
                      !⋆inc≡inc'
                      (λ ! → squash/ _ _)
                      λ !' !'⋆inc≡inc' → sym (unique! !' !'⋆inc≡inc')))))))
        f g
      

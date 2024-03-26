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
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Relation.Binary

module Realizability.Topos.FunctionalRelation
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  where

open import Realizability.Tripos.Prealgebra.Predicate {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Tripos.Prealgebra.Meets.Identity {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Topos.Object {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial 

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate renaming (isSetX to isSetPredicateBase)
open PredicateProperties
open Morphism

private λ*ComputationRule = `λ*ComputationRule as fefermanStructure
private λ* = `λ* as fefermanStructure

open PartialEquivalenceRelation

module _
  {X Y : Type ℓ'}
  (perX : PartialEquivalenceRelation X)
  (perY : PartialEquivalenceRelation Y)
  (relation : Predicate (X × Y)) where
  equalityX = perX .equality
  equalityY = perY .equality
  
  realizesStrictDomain : A → Type _
  realizesStrictDomain stD = (∀ x y r → r ⊩ ∣ relation ∣ (x , y) → (stD ⨾ r) ⊩ ∣ equalityX ∣ (x , x))

  realizesStrictCodomain : A → Type _
  realizesStrictCodomain stC = (∀ x y r → r ⊩ ∣ relation ∣ (x , y) → (stC ⨾ r) ⊩ ∣ equalityY ∣ (y , y))

  realizesRelational : A → Type _
  realizesRelational rel =
        (∀ x x' y y' a b c
        → a ⊩ ∣ equalityX ∣ (x , x')
        → b ⊩ ∣ relation ∣ (x , y)
        → c ⊩ ∣ equalityY ∣ (y , y')
        ------------------------------------------
        → (rel ⨾ a ⨾ b ⨾ c) ⊩ ∣ relation ∣ (x' , y'))

  realizesSingleValued : A → Type _
  realizesSingleValued sv =
        (∀ x y y' r₁ r₂
        → r₁ ⊩ ∣ relation ∣ (x , y)
        → r₂ ⊩ ∣ relation ∣ (x , y')
        -----------------------------------
        → (sv ⨾ r₁ ⨾ r₂) ⊩ ∣ equalityY ∣ (y , y'))

  realizesTotal : A → Type _
  realizesTotal tl =
        (∀ x r → r ⊩ ∣ equalityX ∣ (x , x) → ∃[ y ∈ Y ] (tl ⨾ r) ⊩ ∣ relation ∣ (x , y))
    
  record isFunctionalRelation : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
    field
      isStrictDomain : ∃[ stD ∈ A ] (realizesStrictDomain stD)
      isStrictCodomain : ∃[ stC ∈ A ] (realizesStrictCodomain stC)
      isRelational : ∃[ rl ∈ A ] (realizesRelational rl)
      isSingleValued : ∃[ sv ∈ A ] (realizesSingleValued sv)
      isTotal : ∃[ tl ∈ A ] (realizesTotal tl)

record FunctionalRelation {X Y : Type ℓ'} (perX : PartialEquivalenceRelation X) (perY : PartialEquivalenceRelation Y) : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  field
    relation : Predicate (X × Y)
    isFuncRel : isFunctionalRelation perX perY relation
  open isFunctionalRelation isFuncRel public
  
open FunctionalRelation

pointwiseEntailment : ∀ {X Y : Type ℓ'} → (perX : PartialEquivalenceRelation X) → (perY : PartialEquivalenceRelation Y) → (F G : FunctionalRelation perX perY) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
pointwiseEntailment {X} {Y} perX perY F G = ∃[ pe ∈ A ] (∀ x y r → r ⊩ ∣ F .relation ∣ (x , y) → (pe ⨾ r) ⊩ ∣ G .relation ∣ (x , y))

-- Directly taken from "Realizability with Scott's Graph Model" by Tom de Jong
-- Lemma 4.3.5
opaque
  F≤G→G≤F :
    ∀ {X Y : Type ℓ'}
    → (perX : PartialEquivalenceRelation X)
    → (perY : PartialEquivalenceRelation Y)
    → (F G : FunctionalRelation perX perY)
    → pointwiseEntailment perX perY F G
    → pointwiseEntailment perX perY G F
  F≤G→G≤F {X} {Y} perX perY F G F≤G =
    do
      (r , r⊩F≤G) ← F≤G
      (tlF , tlF⊩isTotalF) ← F .isTotal
      (svG , svG⊩isSingleValuedG) ← G .isSingleValued
      (rlF , rlF⊩isRelationalF) ← F .isRelational
      (stGD , stGD⊩isStrictDomainG) ← G .isStrictDomain
      let
        prover : ApplStrTerm as 1
        prover = ` rlF ̇ (` stGD ̇ # 0) ̇ (` tlF ̇ (` stGD ̇ # 0)) ̇ (` svG ̇ (` r ̇ (` tlF ̇ (` stGD ̇ # 0))) ̇ # 0)
      return
        (λ* prover ,
        (λ x y s s⊩Gxy →
          subst
            (λ r' → r' ⊩ ∣ F .relation ∣ (x , y))
            (sym (λ*ComputationRule prover (s ∷ [])))
            (transport
              (propTruncIdempotent (F .relation .isPropValued _ _))
              (do
                (y' , tlF⨾stGDs⊩Fxy') ← tlF⊩isTotalF x (stGD ⨾ s) (stGD⊩isStrictDomainG x y s s⊩Gxy)
                return
                  (rlF⊩isRelationalF
                    x x y' y
                    (stGD ⨾ s) (tlF ⨾ (stGD ⨾ s)) (svG ⨾ (r ⨾ (tlF ⨾ (stGD ⨾ s))) ⨾ s)
                    (stGD⊩isStrictDomainG x y s s⊩Gxy)
                    tlF⨾stGDs⊩Fxy'
                    (svG⊩isSingleValuedG x y' y (r ⨾ (tlF ⨾ (stGD ⨾ s))) s (r⊩F≤G x y' (tlF ⨾ (stGD ⨾ s)) tlF⨾stGDs⊩Fxy') s⊩Gxy))))))

bientailment : ∀ {X Y : Type ℓ'} → (perX : PartialEquivalenceRelation X) → (perY : PartialEquivalenceRelation Y) → FunctionalRelation perX perY → FunctionalRelation perX perY → Type _
bientailment {X} {Y} perX perY F G = pointwiseEntailment perX perY F G × pointwiseEntailment perX perY G F

isPropValuedBientailment : ∀ {X Y : Type ℓ'} → (perX : PartialEquivalenceRelation X) → (perY : PartialEquivalenceRelation Y) → (F G : FunctionalRelation perX perY) → isProp (bientailment perX perY F G)
isPropValuedBientailment {X} {Y} perX perY F G = isProp× isPropPropTrunc isPropPropTrunc

RTMorphism : ∀ {X Y : Type ℓ'} → (perX : PartialEquivalenceRelation X) → (perY : PartialEquivalenceRelation Y) → Type _
RTMorphism {X} {Y} perX perY = FunctionalRelation perX perY / bientailment perX perY

isEquivRelBientailment : ∀ {X Y : Type ℓ'} → (perX : PartialEquivalenceRelation X) → (perY : PartialEquivalenceRelation Y) → BinaryRelation.isEquivRel (bientailment perX perY)
BinaryRelation.isEquivRel.reflexive (isEquivRelBientailment {X} {Y} perX perY) =
  λ A →
  ∣ Id , (λ x y r r⊩Axy → subst (λ r' → r' ⊩ ∣ A .relation ∣ (x , y)) (sym (Ida≡a _)) r⊩Axy) ∣₁ ,
  ∣ Id , (λ x y r r⊩Axy → subst (λ r' → r' ⊩ ∣ A .relation ∣ (x , y)) (sym (Ida≡a _)) r⊩Axy) ∣₁
BinaryRelation.isEquivRel.symmetric (isEquivRelBientailment {X} {Y} perX perY) F G (F≤G , G≤F) = G≤F , F≤G
BinaryRelation.isEquivRel.transitive (isEquivRelBientailment {X} {Y} perX perY) F G H (F≤G , G≤F) (G≤H , H≤G) =
  let
    answer =
      do
        (s , s⊩F≤G) ← F≤G
        (p , p⊩G≤H) ← G≤H
        let
          prover : ApplStrTerm as 1
          prover = ` p ̇ (` s ̇ # fzero)
        return
          (λ* prover ,
          (λ x y r r⊩Fxy → subst (λ r' → r' ⊩ ∣ H .relation ∣ (x , y)) (sym (λ*ComputationRule prover (r ∷ []))) (p⊩G≤H x y (s ⨾ r) (s⊩F≤G x y r r⊩Fxy))))
  in
  answer , F≤G→G≤F perX perY F H answer

opaque
  idFuncRel : ∀ {X : Type ℓ'} → (perX : PartialEquivalenceRelation X) → FunctionalRelation perX perX
  relation (idFuncRel {X} perX) = perX .equality
  isFunctionalRelation.isStrictDomain (isFuncRel (idFuncRel {X} perX)) =
    do
      (s , s⊩isSymmetric) ← perX .isSymmetric
      (t , t⊩isTransitive) ← perX .isTransitive
      let
        prover : ApplStrTerm as 1
        prover = ` t ̇ # 0 ̇ (` s ̇ # 0)
      return
        (λ* prover ,
         λ x x' r r⊩x~x' →
           subst
             (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
             (sym (λ*ComputationRule prover (r ∷ [])))
             (t⊩isTransitive x x' x r (s ⨾ r) r⊩x~x' (s⊩isSymmetric x x' r r⊩x~x')))
  isFunctionalRelation.isStrictCodomain (isFuncRel (idFuncRel {X} perX)) =
    do
      (s , s⊩isSymmetric) ← perX .isSymmetric
      (t , t⊩isTransitive) ← perX .isTransitive
      let
        prover : ApplStrTerm as 1
        prover = ` t ̇ (` s ̇ # 0) ̇ # 0
      return
        (λ* prover ,
        (λ x x' r r⊩x~x' →
          subst
            (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x'))
            (sym (λ*ComputationRule prover (r ∷ [])))
            (t⊩isTransitive x' x x' (s ⨾ r) r (s⊩isSymmetric x x' r r⊩x~x') r⊩x~x')))
  isFunctionalRelation.isRelational (isFuncRel (idFuncRel {X} perX)) =
    do
      (s , s⊩isSymmetric) ← perX .isSymmetric
      (t , t⊩isTransitive) ← perX .isTransitive
      let
        prover : ApplStrTerm as 3
        prover = ` t ̇ (` t ̇ (` s ̇ # 0) ̇ # 1) ̇ # 2
      return
        (λ* prover ,
        (λ x₁ x₂ x₃ x₄ a b c a⊩x₁~x₂ b⊩x₁~x₃ c⊩x₃~x₄ →
          subst
            (λ r' → r' ⊩ ∣ perX .equality ∣ (x₂ , x₄))
            (sym (λ*ComputationRule prover (a ∷ b ∷ c ∷ [])))
            (t⊩isTransitive x₂ x₃ x₄ (t ⨾ (s ⨾ a) ⨾ b) c (t⊩isTransitive x₂ x₁ x₃ (s ⨾ a) b (s⊩isSymmetric x₁ x₂ a a⊩x₁~x₂) b⊩x₁~x₃) c⊩x₃~x₄)))
  isFunctionalRelation.isSingleValued (isFuncRel (idFuncRel {X} perX)) =
    do
      (s , s⊩isSymmetric) ← perX .isSymmetric
      (t , t⊩isTransitive) ← perX .isTransitive
      let
        prover : ApplStrTerm as 2
        prover = ` t ̇ (` s ̇ # 0) ̇ # 1
      return
        (λ* prover ,
        (λ x₁ x₂ x₃ r₁ r₂ r₁⊩x₁~x₂ r₂⊩x₁~x₃ →
          subst
            (λ r' → r' ⊩ ∣ perX .equality ∣ (x₂ , x₃))
            (sym (λ*ComputationRule prover (r₁ ∷ r₂ ∷ [])))
            (t⊩isTransitive x₂ x₁ x₃ (s ⨾ r₁) r₂ (s⊩isSymmetric x₁ x₂ r₁ r₁⊩x₁~x₂) r₂⊩x₁~x₃)))
  isFunctionalRelation.isTotal (isFuncRel (idFuncRel {X} perX)) =
    do
      (s , s⊩isSymmetric) ← perX .isSymmetric
      (t , t⊩isTransitive) ← perX .isTransitive
      return
        (Id ,
        (λ x r r⊩x~x → ∣ x , subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym (Ida≡a _)) r⊩x~x ∣₁))

idRTMorphism : ∀ {X : Type ℓ'} → (perX : PartialEquivalenceRelation X) → RTMorphism perX perX
idRTMorphism {X} perX = [ idFuncRel perX ]

opaque
  {-# TERMINATING #-} -- bye bye, type-checking with --safe 😔💔
  composeFuncRel :
    ∀ {X Y Z : Type ℓ'}
    → (perX : PartialEquivalenceRelation X)
    → (perY : PartialEquivalenceRelation Y)
    → (perZ : PartialEquivalenceRelation Z)
    → FunctionalRelation perX perY
    → FunctionalRelation perY perZ
    → FunctionalRelation perX perZ
  isSetPredicateBase (relation (composeFuncRel {X} {Y} {Z} perX perY perZ F G)) = isSet× (perX .isSetX) (perZ .isSetX)
  ∣ relation (composeFuncRel {X} {Y} {Z} perX perY perZ F G) ∣ (x , z) r =
    ∃[ y ∈ Y ] (pr₁ ⨾ r) ⊩ ∣ F .relation ∣ (x , y) × (pr₂ ⨾ r) ⊩ ∣ G .relation ∣ (y , z)
  isPropValued (relation (composeFuncRel {X} {Y} {Z} perX perY perZ F G)) (x , z) r = isPropPropTrunc
  isFunctionalRelation.isStrictDomain (isFuncRel (composeFuncRel {X} {Y} {Z} perX perY perZ F G)) =
    do
      (stFD , stFD⊩isStrictDomainF) ← F .isStrictDomain
      let
        prover : ApplStrTerm as 1
        prover = ` stFD ̇ (` pr₁ ̇ # 0)
      return
        (λ* prover ,
        (λ x z r r⊩∃y →
          subst
            (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
            (sym (λ*ComputationRule prover (r ∷ [])))
            (transport
              (propTruncIdempotent (perX .equality .isPropValued _ _))
              (do
                (y , pr₁r⊩Fxy , pr₂r⊩Gyz) ← r⊩∃y
                return (stFD⊩isStrictDomainF x y (pr₁ ⨾ r) pr₁r⊩Fxy)))))
  isFunctionalRelation.isStrictCodomain (isFuncRel (composeFuncRel {X} {Y} {Z} perX perY perZ F G)) =
    do
      (stGC , stGC⊩isStrictCodomainG) ← G .isStrictCodomain
      let
        prover : ApplStrTerm as 1
        prover = ` stGC ̇ (` pr₂ ̇ # 0)
      return
        (λ* prover ,
         λ x z r r⊩∃y →
           subst
             (λ r' → r' ⊩ ∣ perZ .equality ∣ (z , z))
             (sym (λ*ComputationRule prover (r ∷ [])))
             (transport
               (propTruncIdempotent (perZ .equality .isPropValued _ _))
               (do
                 (y , pr₁r⊩Fxy , pr₂r⊩Gyz) ← r⊩∃y
                 return (stGC⊩isStrictCodomainG y z (pr₂ ⨾ r) pr₂r⊩Gyz))))
  isFunctionalRelation.isRelational (isFuncRel (composeFuncRel {X} {Y} {Z} perX perY perZ F G)) =
    do
      (rlF , rlF⊩isRelationalF) ← F .isRelational
      (rlG , rlG⊩isRelationalG) ← G .isRelational
      (stFC , stFC⊩isStrictCodomainF) ← F .isStrictCodomain
      let
        prover : ApplStrTerm as 3
        prover = ` pair ̇ (` rlF ̇ # 0 ̇ (` pr₁ ̇ # 1) ̇ (` stFC ̇ (` pr₁ ̇ # 1))) ̇ (` rlG ̇ (` stFC ̇ (` pr₁ ̇ # 1)) ̇ (` pr₂ ̇ # 1) ̇ # 2)
      return
        (λ* prover ,
        (λ x x' z z' a b c a⊩x~x' b⊩∃y c⊩z~z' →
          do
            (y , pr₁b⊩Fxy , pr₂b⊩Gyz) ← b⊩∃y
            let
              pr₁proofEq : pr₁ ⨾ (λ* prover ⨾ a ⨾ b ⨾ c) ≡ rlF ⨾ a ⨾ (pr₁ ⨾ b) ⨾ (stFC ⨾ (pr₁ ⨾ b))
              pr₁proofEq = cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (a ∷ b ∷ c ∷ [])) ∙ pr₁pxy≡x _ _

              pr₂proofEq : pr₂ ⨾ (λ* prover ⨾ a ⨾ b ⨾ c) ≡ rlG ⨾ (stFC ⨾ (pr₁ ⨾ b)) ⨾ (pr₂ ⨾ b) ⨾ c
              pr₂proofEq = cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (a ∷ b ∷ c ∷ [])) ∙ pr₂pxy≡y _ _
            return
              (y ,
               subst
                 (λ r' → r' ⊩ ∣ F .relation ∣ (x' , y))
                 (sym pr₁proofEq)
                 (rlF⊩isRelationalF x x' y y a (pr₁ ⨾ b) (stFC ⨾ (pr₁ ⨾ b)) a⊩x~x' pr₁b⊩Fxy (stFC⊩isStrictCodomainF x y (pr₁ ⨾ b) pr₁b⊩Fxy)) ,
               subst
                 (λ r' → r' ⊩ ∣ G .relation ∣ (y , z'))
                 (sym pr₂proofEq)
                 (rlG⊩isRelationalG y y z z' (stFC ⨾ (pr₁ ⨾ b)) (pr₂ ⨾ b) c (stFC⊩isStrictCodomainF x y (pr₁ ⨾ b) pr₁b⊩Fxy) pr₂b⊩Gyz c⊩z~z'))))
  isFunctionalRelation.isSingleValued (isFuncRel (composeFuncRel {X} {Y} {Z} perX perY perZ F G)) =
    do
      (svF , svF⊩isSingleValuedF) ← F .isSingleValued
      (svG , svG⊩isSingleValuedG) ← G .isSingleValued
      (relG , relG⊩isRelationalG) ← G .isRelational
      (stGC , stGC⊩isStrictCodomainG) ← G .isStrictCodomain
      let
        prover : ApplStrTerm as 2
        prover = ` svG ̇ (` pr₂ ̇ # 0) ̇ (` relG ̇ (` svF ̇ (` pr₁ ̇ # 1) ̇ (` pr₁ ̇ # 0)) ̇ (` pr₂ ̇ # 1) ̇ (` stGC ̇ (` pr₂ ̇ # 1)))
      return
        (λ* prover ,
        (λ x z z' r₁ r₂ r₁⊩∃y r₂⊩∃y →
          transport
            (propTruncIdempotent (perZ .equality .isPropValued _ _))
            (do
              (y , pr₁r₁⊩Fxy , pr₂r₁⊩Gyz) ← r₁⊩∃y
              (y' , pr₁r₂⊩Fxy' , pr₂r₂⊩Gy'z') ← r₂⊩∃y
              return
                (subst
                  (λ r' → r' ⊩ ∣ perZ .equality ∣ (z , z'))
                  (sym (λ*ComputationRule prover (r₁ ∷ r₂ ∷ [])))
                  (svG⊩isSingleValuedG
                    y z z'
                    (pr₂ ⨾ r₁)
                    (relG ⨾ (svF ⨾ (pr₁ ⨾ r₂) ⨾ (pr₁ ⨾ r₁)) ⨾ (pr₂ ⨾ r₂) ⨾ (stGC ⨾ (pr₂ ⨾ r₂)))
                    pr₂r₁⊩Gyz
                    (relG⊩isRelationalG
                      y' y z' z'
                      (svF ⨾ (pr₁ ⨾ r₂) ⨾ (pr₁ ⨾ r₁))
                      (pr₂ ⨾ r₂)
                      (stGC ⨾ (pr₂ ⨾ r₂))
                      (svF⊩isSingleValuedF x y' y (pr₁ ⨾ r₂) (pr₁ ⨾ r₁) pr₁r₂⊩Fxy' pr₁r₁⊩Fxy)
                      pr₂r₂⊩Gy'z'
                      (stGC⊩isStrictCodomainG y' z' (pr₂ ⨾ r₂) pr₂r₂⊩Gy'z')))))))
  isFunctionalRelation.isTotal (isFuncRel (composeFuncRel {X} {Y} {Z} perX perY perZ F G)) =
    do
      (tlF , tlF⊩isTotalF) ← F .isTotal
      (tlG , tlG⊩isTotalG) ← G .isTotal
      (stFC , stFC⊩isStrictCodomainF) ← F .isStrictCodomain
      let
        prover : ApplStrTerm as 1
        prover = ` pair ̇ (` tlF ̇ # 0) ̇ (` tlG ̇ (` stFC ̇ (` tlF ̇ # 0)))
      return
        (λ* prover ,
        (λ x r r⊩x~x →
          do
            (y , ⊩Fxy) ← tlF⊩isTotalF x r r⊩x~x
            (z , ⊩Gyz) ← tlG⊩isTotalG y (stFC ⨾ (tlF ⨾ r)) (stFC⊩isStrictCodomainF x y (tlF ⨾ r) ⊩Fxy)
            return
              (z ,
              return
                (y ,
                ((subst (λ r' → r' ⊩ ∣ F .relation ∣ (x , y)) (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₁pxy≡x _ _)) ⊩Fxy) ,
                 (subst (λ r' → r' ⊩ ∣ G .relation ∣ (y , z)) (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₂pxy≡y _ _)) ⊩Gyz))))))

opaque
  unfolding composeFuncRel
  composeRTMorphism :
    ∀ {X Y Z : Type ℓ'}
    → (perX : PartialEquivalenceRelation X)
    → (perY : PartialEquivalenceRelation Y)
    → (perZ : PartialEquivalenceRelation Z)
    → (f : RTMorphism perX perY)
    → (g : RTMorphism perY perZ)
    ----------------------------------------
    → RTMorphism perX perZ
  composeRTMorphism {X} {Y} {Z} perX perY perZ f g =
    SQ.rec2
      squash/
      (λ F G → [ composeFuncRel perX perY perZ F G ])
      (λ { F F' G (F≤F' , F'≤F) →
        eq/ _ _
          let answer = (do
              (s , s⊩F≤F') ← F≤F'
              let
                prover : ApplStrTerm as 1
                prover = ` pair ̇ (` s ̇ (` pr₁ ̇ # 0)) ̇ (` pr₂ ̇ # 0)
              return
                (λ* prover ,
                (λ x z r r⊩∃y →
                  do
                    (y , pr₁r⊩Fxy , pr₂r⊩Gyz) ← r⊩∃y
                    return
                      (y ,
                       subst
                         (λ r' → r' ⊩ ∣ F' .relation ∣ (x , y))
                         (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₁pxy≡x _ _))
                         (s⊩F≤F' x y (pr₁ ⨾ r) pr₁r⊩Fxy) ,
                       subst
                         (λ r' → r' ⊩ ∣ G .relation ∣ (y , z))
                         (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₂pxy≡y _ _))
                         pr₂r⊩Gyz))))
          in
        (answer , F≤G→G≤F perX perZ (composeFuncRel perX perY perZ F G) (composeFuncRel perX perY perZ F' G) answer) })
      (λ { F G G' (G≤G' , G'≤G) →
        eq/ _ _
          let answer = (do
            (s , s⊩G≤G') ← G≤G'
            let
              prover : ApplStrTerm as 1
              prover = ` pair ̇ (` pr₁ ̇ # 0) ̇ (` s ̇ (` pr₂ ̇ # 0))
            return
              (λ* prover ,
              (λ x z r r⊩∃y →
                 do
                   (y , pr₁r⊩Fxy , pr₂r⊩Gyz) ← r⊩∃y

                   return
                     (y ,
                      subst (λ r' → r' ⊩ ∣ F .relation ∣ (x , y)) (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₁pxy≡x _ _)) pr₁r⊩Fxy ,
                      subst (λ r' → r' ⊩ ∣ G' .relation ∣ (y , z)) (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₂pxy≡y _ _)) (s⊩G≤G' y z (pr₂ ⨾ r) pr₂r⊩Gyz)))))
          in
        (answer , F≤G→G≤F perX perZ (composeFuncRel perX perY perZ F G) (composeFuncRel perX perY perZ F G') answer) })
      f g

opaque
  unfolding composeRTMorphism
  unfolding idFuncRel
  idLRTMorphism :
    ∀ {X Y : Type ℓ'}
    → (perX : PartialEquivalenceRelation X)
    → (perY : PartialEquivalenceRelation Y)
    → (f : RTMorphism perX perY)
    → composeRTMorphism perX perX perY (idRTMorphism perX) f ≡ f
  idLRTMorphism {X} {Y} perX perY f =
    SQ.elimProp
      (λ f → squash/ (composeRTMorphism perX perX perY (idRTMorphism perX) f) f)
      (λ F →
        let
          answer : pointwiseEntailment perX perY (composeFuncRel perX perX perY (idFuncRel perX) F) F
          answer =
            do
              (relF , relF⊩isRelationalF) ← F .isRelational
              (stFC , stFC⊩isStrictCodomainF) ← F .isStrictCodomain
              (sX , sX⊩isSymmetricX) ← perX .isSymmetric
              let
                prover : ApplStrTerm as 1
                prover = ` relF ̇ (` sX ̇ (` pr₁ ̇ # 0)) ̇ (` pr₂ ̇ # 0) ̇ (` stFC ̇ (` pr₂ ̇ # 0))
              return
                (λ* prover ,
                 (λ x y r r⊩∃x' →
                   transport
                     (propTruncIdempotent (F .relation .isPropValued _ _))
                     (do
                       (x' , pr₁r⊩x~x' , pr₂r⊩Fx'y) ← r⊩∃x'
                       return
                         (subst
                           (λ r' → r' ⊩ ∣ F .relation ∣ (x , y))
                           (sym (λ*ComputationRule prover (r ∷ [])))
                           (relF⊩isRelationalF
                             x' x y y
                             (sX ⨾ (pr₁ ⨾ r)) (pr₂ ⨾ r) (stFC ⨾ (pr₂ ⨾ r))
                             (sX⊩isSymmetricX x x' (pr₁ ⨾ r) pr₁r⊩x~x')
                             pr₂r⊩Fx'y
                             (stFC⊩isStrictCodomainF x' y (pr₂ ⨾ r) pr₂r⊩Fx'y))))))
        in
        eq/ _ _ (answer , F≤G→G≤F perX perY (composeFuncRel perX perX perY (idFuncRel perX) F) F answer))
      f

opaque
  unfolding composeRTMorphism
  unfolding idFuncRel
  idRRTMorphism :
    ∀ {X Y : Type ℓ'}
    → (perX : PartialEquivalenceRelation X)
    → (perY : PartialEquivalenceRelation Y)
    → (f : RTMorphism perX perY)
    → composeRTMorphism perX perY perY f (idRTMorphism perY) ≡ f
  idRRTMorphism {X} {Y} perX perY f =
    SQ.elimProp
      (λ f → squash/ (composeRTMorphism perX perY perY f (idRTMorphism perY)) f)
      (λ F →
        let
          answer : pointwiseEntailment perX perY (composeFuncRel perX perY perY F (idFuncRel perY)) F
          answer =
            do
              (relF , relF⊩isRelationalF) ← F .isRelational
              (stFD , stFD⊩isStrictDomainF) ← F .isStrictDomain
              let
                prover : ApplStrTerm as 1
                prover = ` relF ̇ (` stFD ̇ (` pr₁ ̇ # 0)) ̇ (` pr₁ ̇ # 0) ̇ (` pr₂ ̇ # 0)
              return
                (λ* prover ,
                (λ x y r r⊩∃y' →
                  transport
                    (propTruncIdempotent (F .relation .isPropValued _ _))
                    (do
                      (y' , pr₁r⊩Fxy' , pr₂r⊩y'~y) ← r⊩∃y'
                      return
                        (subst
                          (λ r' → r' ⊩ ∣ F .relation ∣ (x , y))
                          (sym (λ*ComputationRule prover (r ∷ [])))
                          (relF⊩isRelationalF x x y' y (stFD ⨾ (pr₁ ⨾ r)) (pr₁ ⨾ r) (pr₂ ⨾ r) (stFD⊩isStrictDomainF x y' (pr₁ ⨾ r) pr₁r⊩Fxy') pr₁r⊩Fxy' pr₂r⊩y'~y)))))
        in
        eq/ _ _ (answer , F≤G→G≤F perX perY (composeFuncRel perX perY perY F (idFuncRel perY)) F answer))
      f

opaque
  unfolding composeRTMorphism
  assocRTMorphism :
    ∀ {X Y Z W : Type ℓ'}
    → (perX : PartialEquivalenceRelation X)
    → (perY : PartialEquivalenceRelation Y)
    → (perZ : PartialEquivalenceRelation Z)
    → (perW : PartialEquivalenceRelation W)
    → (f : RTMorphism perX perY)
    → (g : RTMorphism perY perZ)
    → (h : RTMorphism perZ perW)
    → composeRTMorphism perX perZ perW (composeRTMorphism perX perY perZ f g) h ≡ composeRTMorphism perX perY perW f (composeRTMorphism perY perZ perW g h)
  assocRTMorphism {X} {Y} {Z} {W} perX perY perZ perW f g h =
    SQ.elimProp3
      (λ f g h →
        squash/
          (composeRTMorphism perX perZ perW (composeRTMorphism perX perY perZ f g) h)
          (composeRTMorphism perX perY perW f (composeRTMorphism perY perZ perW g h)))
      (λ F G H →
        let
          answer =
            do
              let
                prover : ApplStrTerm as 1
                prover = ` pair ̇ (` pr₁ ̇ (` pr₁ ̇ # 0)) ̇ (` pair ̇ (` pr₂ ̇ (` pr₁ ̇ # 0)) ̇ (` pr₂ ̇ # 0))
              return
                (λ* prover ,
                (λ x w r r⊩∃z →
                  transport
                    (propTruncIdempotent isPropPropTrunc)
                    (do
                      (z , pr₁r⊩∃y , pr₂r⊩Hzw) ← r⊩∃z
                      (y , pr₁pr₁r⊩Fxy , pr₂pr₁r⊩Gyz) ← pr₁r⊩∃y
                      return
                        (return
                          (y ,
                            (subst
                              (λ r' → r' ⊩ ∣ F .relation ∣ (x , y))
                              (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₁pxy≡x _ _))
                              pr₁pr₁r⊩Fxy ,
                            return
                              (z ,
                                ((subst
                                  (λ r' → r' ⊩ ∣ G .relation ∣ (y , z))
                                  (sym
                                    (cong (λ x → pr₁ ⨾ (pr₂ ⨾ x)) (λ*ComputationRule prover (r ∷ [])) ∙
                                     cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₁pxy≡x _ _))
                                  pr₂pr₁r⊩Gyz) ,
                                 (subst
                                  (λ r' → r' ⊩ ∣ H .relation ∣ (z , w))
                                  (sym
                                    (cong (λ x → pr₂ ⨾ (pr₂ ⨾ x)) (λ*ComputationRule prover (r ∷ [])) ∙
                                     cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ∙ pr₂pxy≡y _ _))
                                  pr₂r⊩Hzw)))))))))
        in
        eq/ _ _
          (answer ,
           F≤G→G≤F
             perX perW
             (composeFuncRel perX perZ perW (composeFuncRel perX perY perZ F G) H)
             (composeFuncRel perX perY perW F (composeFuncRel perY perZ perW G H))
             answer))
      f g h

RT : Category (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ''))) (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ'')))
Category.ob RT = Σ[ X ∈ Type ℓ' ] PartialEquivalenceRelation X
Category.Hom[_,_] RT (X , perX) (Y , perY) = RTMorphism perX perY
Category.id RT {X , perX} = idRTMorphism perX
Category._⋆_ RT {X , perX} {y , perY} {Z , perZ} f g = composeRTMorphism perX perY perZ f g
Category.⋆IdL RT {X , perX} {Y , perY} f = idLRTMorphism perX perY f
Category.⋆IdR RT {X , perX} {Y , perY} f = idRRTMorphism perX perY f
Category.⋆Assoc RT {X , perX} {Y , perY} {Z , perZ} {W , perW} f g h = assocRTMorphism perX perY perZ perW f g h
Category.isSetHom RT = squash/

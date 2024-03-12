open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm; λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Fin
open import Cubical.Data.Vec
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinProduct

module Realizability.Topos.BinProducts
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
open PartialEquivalenceRelation hiding (isSetX)
module _
  {X : Type ℓ'}
  {Y : Type ℓ'}
  (perX : PartialEquivalenceRelation X)
  (perY : PartialEquivalenceRelation Y) where

  opaque private
    isSetX : isSet X
    isSetX = PartialEquivalenceRelation.isSetX perX
    isSetY : isSet Y
    isSetY = PartialEquivalenceRelation.isSetX perY

  opaque
    {-# TERMINATING #-}
    binProdObRT : PartialEquivalenceRelation (X × Y)
    Predicate.isSetX (PartialEquivalenceRelation.equality binProdObRT) =
      isSet× (isSet× isSetX isSetY) (isSet× isSetX isSetY)
    Predicate.∣ PartialEquivalenceRelation.equality binProdObRT ∣ ((x , y) , x' , y') r =
      (pr₁ ⨾ r) ⊩ ∣ perX .equality ∣ (x , x') × (pr₂ ⨾ r) ⊩ ∣ perY .equality ∣ (y , y')
    Predicate.isPropValued (PartialEquivalenceRelation.equality binProdObRT) ((x , y) , x' , y') r =
      isProp× (perX .equality .isPropValued _ _) (perY .equality .isPropValued _ _)
    isPartialEquivalenceRelation.isSetX (PartialEquivalenceRelation.isPerEquality binProdObRT) = isSet× isSetX isSetY
    isPartialEquivalenceRelation.isSymmetric (PartialEquivalenceRelation.isPerEquality binProdObRT) =
      do
        (sX , sX⊩isSymmetricX) ← perX .isSymmetric
        (sY , sY⊩isSymmetricY) ← perY .isSymmetric
        let
          prover : ApplStrTerm as 1
          prover = ` pair ̇ (` sX ̇ (` pr₁ ̇ # fzero)) ̇ (` sY ̇ (` pr₂ ̇ # fzero))
        return
          (λ* prover ,
          (λ { (x , y) (x' , y') r (pr₁r⊩x~x' , pr₂r⊩y~y') →
            subst
              (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x))
              (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₁pxy≡x _ _))
              (sX⊩isSymmetricX x x' (pr₁ ⨾ r) pr₁r⊩x~x') ,
            subst
              (λ r' → r' ⊩ ∣ perY .equality ∣ (y' , y))
              (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₂pxy≡y _ _))
              (sY⊩isSymmetricY y y' (pr₂ ⨾ r) pr₂r⊩y~y') }))
    isPartialEquivalenceRelation.isTransitive (PartialEquivalenceRelation.isPerEquality binProdObRT) =
      do
        (tX , tX⊩isTransitiveX) ← perX .isTransitive
        (tY , tY⊩isTransitiveY) ← perY .isTransitive
        let
          prover : ApplStrTerm as 2
          prover = ` pair ̇ (` tX ̇ (` pr₁ ̇ # fzero) ̇ (` pr₁ ̇ # fone)) ̇ (` tY ̇ (` pr₂ ̇ # fzero) ̇ (` pr₂ ̇ # fone))
        return
          (λ* prover ,
          (λ { (x , y) (x' , y') (x'' , y'') a b (pr₁a⊩x~x' , pr₂a⊩y~y') (pr₁b⊩x'~x'' , pr₂b⊩y'~y'') →
            subst
              (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x''))
              (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (a ∷ b ∷ [])) ∙ pr₁pxy≡x _ _))
              (tX⊩isTransitiveX x x' x'' (pr₁ ⨾ a) (pr₁ ⨾ b) pr₁a⊩x~x' pr₁b⊩x'~x'') ,
            subst
              (λ r' → r' ⊩ ∣ perY .equality ∣ (y , y''))
              (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (a ∷ b ∷ [])) ∙ pr₂pxy≡y _ _))
              (tY⊩isTransitiveY y y' y'' (pr₂ ⨾ a) (pr₂ ⨾ b) pr₂a⊩y~y' pr₂b⊩y'~y'') }))

  opaque
    unfolding binProdObRT
    unfolding idFuncRel
    binProdPr₁FuncRel : FunctionalRelation binProdObRT perX
    FunctionalRelation.relation binProdPr₁FuncRel =
      record
        { isSetX = isSet× (isSet× isSetX isSetY) isSetX
        ; ∣_∣ = λ { ((x , y) , x') r → (pr₁ ⨾ r) ⊩ ∣ perX .equality ∣ (x , x') × (pr₂ ⨾ r) ⊩ ∣ perY .equality ∣ (y , y) }
        ; isPropValued = (λ { ((x , y) , x') r → isProp× (perX .equality .isPropValued _ _) (perY .equality .isPropValued _ _) }) }
    FunctionalRelation.isFuncRel binProdPr₁FuncRel =
      record
       { isStrictDomain =
         do
           (stD , stD⊩isStrictDomainEqX) ← idFuncRel perX .isStrictDomain
           let
             prover : ApplStrTerm as 1
             prover = ` pair ̇ (` stD ̇ (` pr₁ ̇ # fzero)) ̇ (` pr₂ ̇ (# fzero))
           return
             (λ* prover ,
             (λ { (x , y) x' r (pr₁r⊩x~x' , pr₂r⊩y~y) →
               subst
                 (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
                 (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₁pxy≡x _ _))
                 (stD⊩isStrictDomainEqX x x' (pr₁ ⨾ r) pr₁r⊩x~x') ,
               subst
                 (λ r' → r' ⊩ ∣ perY .equality ∣ (y , y))
                 (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₂pxy≡y _ _))
                 pr₂r⊩y~y }))
       ; isStrictCodomain =
         do
           (stC , stC⊩isStrictCodomainEqX) ← idFuncRel perX .isStrictCodomain
           let
             prover : ApplStrTerm as 1
             prover = ` stC ̇ (` pr₁ ̇ # fzero)
           return
             (λ* prover ,
              λ { (x , y) x' r (pr₁r⊩x~x' , pr₂r⊩y~y) →
                subst
                  (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x'))
                  (sym (λ*ComputationRule prover (r ∷ [])))
                  (stC⊩isStrictCodomainEqX x x' (pr₁ ⨾ r) pr₁r⊩x~x') })
       ; isRelational =
         do
           (stC , stC⊩isStrictCodomainEqY) ← idFuncRel perY .isStrictCodomain
           (t , t⊩isTransitiveX) ← perX .isTransitive
           (s , s⊩isSymmetricX) ← perX .isSymmetric
           let
             prover : ApplStrTerm as 3
             prover = ` pair ̇ (` t ̇ (` s ̇ (` pr₁ ̇ # fzero)) ̇ (` t ̇ (` pr₁ ̇ # fone) ̇ # (fsuc fone))) ̇ (` stC ̇ (` pr₂ ̇ # fzero))
           return
             (λ* prover ,
              ((λ { (x , y) (x' , y') x'' x''' a b c (pr₁a⊩x~x' , pr₂a⊩y~y') (pr₁b⊩x~x'' , pr₂b⊩y~y) c⊩x''~x''' →
                subst
                  (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x'''))
                  (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (a ∷ b ∷ c ∷ [])) ∙ pr₁pxy≡x _ _))
                  (t⊩isTransitiveX
                    x' x x'''
                    (s ⨾ (pr₁ ⨾ a)) (t ⨾ (pr₁ ⨾ b) ⨾ c)
                    (s⊩isSymmetricX x x' (pr₁ ⨾ a) pr₁a⊩x~x')
                    (t⊩isTransitiveX x x'' x''' (pr₁ ⨾ b) c pr₁b⊩x~x'' c⊩x''~x''')) ,
                subst
                  (λ r' → r' ⊩ ∣ perY .equality ∣ (y' , y'))
                  (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (a ∷ b ∷ c ∷ [])) ∙ pr₂pxy≡y _ _))
                  (stC⊩isStrictCodomainEqY y y' (pr₂ ⨾ a) pr₂a⊩y~y') })))
       ; isSingleValued =
         do
           (t , t⊩isTransitive) ← perX .isTransitive
           (s , s⊩isSymmetric) ← perX .isSymmetric
           let
             prover : ApplStrTerm as 2
             prover = ` t ̇ (` s ̇ (` pr₁ ̇ # fzero)) ̇ (` pr₁ ̇ # fone)
           return
             (λ* prover ,
              (λ { (x , y) x' x'' r₁ r₂ (pr₁r₁⊩x~x' , pr₂r₁⊩y~y) (pr₁r₂⊩x~x'' , pr₂r₂⊩y~y) →
                subst
                  (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x''))
                  (sym (λ*ComputationRule prover (r₁ ∷ r₂ ∷ [])))
                  (t⊩isTransitive x' x x'' (s ⨾ (pr₁ ⨾ r₁)) (pr₁ ⨾ r₂) (s⊩isSymmetric x x' (pr₁ ⨾ r₁) pr₁r₁⊩x~x') pr₁r₂⊩x~x'')}))
       ; isTotal =
         do
           return
             (Id ,
              (λ { (x , y) r (pr₁r⊩x~x , pr₂r⊩y~y) →
                return
                  (x ,
                  ((subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (cong (λ x → pr₁ ⨾ x) (sym (Ida≡a _))) pr₁r⊩x~x) ,
                   (subst (λ r' → r' ⊩ ∣ perY .equality ∣ (y , y)) (cong (λ x → pr₂ ⨾ x) (sym (Ida≡a _))) pr₂r⊩y~y))) }))
       }

  opaque
    binProdPr₁RT : RTMorphism binProdObRT perX
    binProdPr₁RT = [ binProdPr₁FuncRel ]

  -- Code repetition to a degree
  -- TODO : Refactor into a proper abstraction
  opaque
    unfolding binProdObRT
    unfolding idFuncRel
    binProdPr₂FuncRel : FunctionalRelation binProdObRT perY
    FunctionalRelation.relation binProdPr₂FuncRel =
      record
        { isSetX = isSet× (isSet× isSetX isSetY) isSetY
        ; ∣_∣ = λ { ((x , y) , y') r → (pr₁ ⨾ r) ⊩ ∣ perY .equality ∣ (y , y') × (pr₂ ⨾ r) ⊩ ∣ perX .equality ∣ (x , x) }
        ; isPropValued = λ { ((x , y) , y') r → isProp× (perY .equality .isPropValued _ _) (perX .equality .isPropValued _ _) } }
    FunctionalRelation.isFuncRel binProdPr₂FuncRel =
      record
       { isStrictDomain =
         do
           (stD , stD⊩isStrictDomainEqY) ← idFuncRel perY .isStrictDomain
           let
             prover : ApplStrTerm as 1
             prover = ` pair ̇ (` pr₂ ̇ (# fzero)) ̇ (` stD ̇ (` pr₁ ̇ # fzero))
           return
             (λ* prover ,
             (λ { (x , y) y' r (pr₁r⊩y~y' , pr₂r⊩x~x) →
                subst
                  (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
                  (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₁pxy≡x _ _))
                  pr₂r⊩x~x ,
                subst
                  (λ r' → r' ⊩ ∣ perY .equality ∣ (y , y))
                  (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₂pxy≡y _ _))
                  (stD⊩isStrictDomainEqY y y' (pr₁ ⨾ r) pr₁r⊩y~y') }))
       ; isStrictCodomain =
         do
           (stC , stC⊩isStrictCodomainEqY) ← idFuncRel perY .isStrictCodomain
           let
             prover : ApplStrTerm as 1
             prover = ` stC ̇ (` pr₁ ̇ # fzero)
           return
             (λ* prover ,
             (λ { (x , y) y' r (pr₁r⊩y~y' , pr₂r⊩x~x) →
               subst
                 (λ r' → r' ⊩ ∣ perY .equality ∣ (y' , y'))
                 (sym (λ*ComputationRule prover (r ∷ [])))
                 (stC⊩isStrictCodomainEqY y y' (pr₁ ⨾ r) pr₁r⊩y~y') }))
       ; isRelational =
         do
           (stC , stC⊩isStrictCodomainEqX) ← idFuncRel perX .isStrictCodomain
           (relY , relY⊩isRelationalEqY) ← idFuncRel perY .isRelational
           let
             prover : ApplStrTerm as 3
             prover = ` pair ̇ (` relY ̇ (` pr₂ ̇ # fzero) ̇ (` pr₁ ̇ # fone) ̇ # (fsuc fone)) ̇ (` stC ̇ (` pr₁ ̇ # fzero))
           return
             (λ* prover ,
             (λ { (x , y₁) (x' , y₂) y₃ y₄ a b c (pr₁a⊩x~x' , pr₂a⊩y₁~y₂) (pr₁b⊩y₁~y₃ , pr₂b⊩x~x) c⊩y₃~y₄ →
               subst
                 (λ r' → r' ⊩ ∣ perY .equality ∣ (y₂ , y₄))
                 (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (a ∷ b ∷ c ∷ [])) ∙ pr₁pxy≡x _ _))
                 (relY⊩isRelationalEqY y₁ y₂ y₃ y₄ (pr₂ ⨾ a) (pr₁ ⨾ b) c pr₂a⊩y₁~y₂ pr₁b⊩y₁~y₃ c⊩y₃~y₄) ,
               subst
                 (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x'))
                 (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (a ∷ b ∷ c ∷ [])) ∙ pr₂pxy≡y _ _))
                 (stC⊩isStrictCodomainEqX x x' (pr₁ ⨾ a) pr₁a⊩x~x') }))
       ; isSingleValued =
         do
           (svY , svY⊩isSingleValuedY) ← idFuncRel perY .isSingleValued
           let
             prover : ApplStrTerm as 2
             prover = ` svY ̇ (` pr₁ ̇ # fzero) ̇ (` pr₁ ̇ # fone)
           return
             (λ* prover ,
             (λ { (x , y) y' y'' r₁ r₂ (pr₁r₁⊩y~y' , pr₂r₁⊩x~x) (pr₁r₂⊩y~y'' , pr₂r₂⊩) →
               subst
                 (λ r' → r' ⊩ ∣ perY .equality ∣ (y' , y''))
                 (sym (λ*ComputationRule prover (r₁ ∷ r₂ ∷ [])))
                 (svY⊩isSingleValuedY y y' y'' (pr₁ ⨾ r₁) (pr₁ ⨾ r₂) pr₁r₁⊩y~y' pr₁r₂⊩y~y'') }))
       ; isTotal =
         do
           let
             prover : ApplStrTerm as 1
             prover = ` pair ̇ (` pr₂ ̇ # fzero) ̇ (` pr₁ ̇ # fzero)
           return
             (λ* prover ,
             (λ { (x , y) r (pr₁r⊩x~x , pr₂r⊩y~y) →
               return
                 (y ,
                   (subst
                     (λ r' → r' ⊩ ∣ perY .equality ∣ (y , y))
                     (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₁pxy≡x _ _))
                     pr₂r⊩y~y ,
                    subst
                     (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
                     (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₂pxy≡y _ _))
                     pr₁r⊩x~x)) }))
       }

  binProdPr₂RT : RTMorphism binProdObRT perY
  binProdPr₂RT = [ binProdPr₂FuncRel ]

  module UnivProp
    {Z : Type ℓ'}
    (perZ : PartialEquivalenceRelation Z)
    (f : RTMorphism perZ perX)
    (g : RTMorphism perZ perY) where

    isSetZ = PartialEquivalenceRelation.isSetX perZ

    opaque
      unfolding binProdObRT
      theFuncRel : (F : FunctionalRelation perZ perX) → (G : FunctionalRelation perZ perY) → FunctionalRelation perZ binProdObRT
      theFuncRel F G =
        record
              { relation =
                record
                  { isSetX = isSet× isSetZ (isSet× isSetX isSetY)
                  ; ∣_∣ = λ { (z , x , y) r → (pr₁ ⨾ r) ⊩ ∣ F .relation ∣ (z , x) × (pr₂ ⨾ r) ⊩ ∣ G .relation ∣ (z , y) }
                ; isPropValued = λ { (z , x , y) r → isProp× (F .relation .isPropValued _ _) (G .relation .isPropValued _ _) } }
              ; isFuncRel =
                record
                 { isStrictDomain =
                   do
                     (stFD , stFD⊩isStrictDomain) ← F .isStrictDomain
                     let
                       prover : ApplStrTerm as 1
                       prover = ` stFD ̇ (` pr₁ ̇ # fzero)
                     return
                       (λ* prover ,
                        (λ { z (x , y) r (pr₁r⊩Fzx , pr₂r⊩Gzy) →
                          subst
                            (λ r' → r' ⊩ ∣ perZ .equality ∣ (z , z))
                            (sym (λ*ComputationRule prover (r ∷ [])))
                            (stFD⊩isStrictDomain z x (pr₁ ⨾ r) pr₁r⊩Fzx) }))
                 ; isStrictCodomain =
                   do
                     (stFC , stFC⊩isStrictCodomainF) ← F .isStrictCodomain
                     (stGC , stGC⊩isStrictCodomainG) ← G .isStrictCodomain
                     let
                       prover : ApplStrTerm as 1
                       prover = ` pair ̇ (` stFC ̇ (` pr₁ ̇ # fzero)) ̇ (` stGC ̇ (` pr₂ ̇ # fzero))
                     return
                       (λ* prover ,
                       (λ { z (x , y) r (pr₁r⊩Fzx , pr₂r⊩Gzy) →
                         subst
                           (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x))
                           (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₁pxy≡x _ _))
                           (stFC⊩isStrictCodomainF z x (pr₁ ⨾ r) pr₁r⊩Fzx) ,
                         subst
                           (λ r' → r' ⊩ ∣ perY .equality ∣ (y , y))
                           (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₂pxy≡y _ _))
                           (stGC⊩isStrictCodomainG z y (pr₂ ⨾ r) pr₂r⊩Gzy) }))
                 ; isRelational =
                   do
                     (relF , relF⊩isRelationalF) ← F .isRelational
                     (relG , relG⊩isRelationalG) ← G .isRelational
                     let
                       prover : ApplStrTerm as 3
                       prover = ` pair ̇ (` relF ̇ # fzero ̇ (` pr₁ ̇ # fone) ̇ (` pr₁ ̇ # (fsuc fone))) ̇ (` relG ̇ # fzero ̇ (` pr₂ ̇ # fone) ̇ (` pr₂ ̇ # (fsuc fone)))
                     return
                       (λ* prover ,
                       (λ { z z' (x , y) (x' , y') a b c a⊩z~z' (pr₁b⊩Fzx , pr₂b⊩Gzy) (pr₁c⊩x~x' , pr₂c⊩y~y') →
                         (subst
                           (λ r → r ⊩ ∣ F .relation ∣ (z' , x'))
                           (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (a ∷ b ∷ c ∷ [])) ∙ pr₁pxy≡x _ _))
                           (relF⊩isRelationalF z z' x x' a (pr₁ ⨾ b) (pr₁ ⨾ c) a⊩z~z' pr₁b⊩Fzx pr₁c⊩x~x')) ,
                         (subst
                           (λ r → r ⊩ ∣ G .relation ∣ (z' , y'))
                           (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (a ∷ b ∷ c ∷ [])) ∙ pr₂pxy≡y _ _))
                           (relG⊩isRelationalG z z' y y' a (pr₂ ⨾ b) (pr₂ ⨾ c) a⊩z~z' pr₂b⊩Gzy pr₂c⊩y~y')) }))
                 ; isSingleValued =
                   do
                     (svF , svF⊩isSingleValuedF) ← F .isSingleValued
                     (svG , svG⊩isSingleValuedG) ← G .isSingleValued
                     let
                       prover : ApplStrTerm as 2
                       prover = ` pair ̇ (` svF ̇ (` pr₁ ̇ # fzero) ̇ (` pr₁ ̇ # fone)) ̇ (` svG ̇ (` pr₂ ̇ # fzero) ̇ (` pr₂ ̇ # fone))
                     return
                       (λ* prover ,
                       (λ { z (x , y) (x' , y') r₁ r₂ (pr₁r₁⊩Fzx , pr₂r₁⊩Gzy) (pr₁r₂⊩Fzx' , pr₂r₂⊩Gzy') →
                         subst
                           (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x'))
                           (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r₁ ∷ r₂ ∷ [])) ∙ pr₁pxy≡x _ _))
                           (svF⊩isSingleValuedF z x x' (pr₁ ⨾ r₁) (pr₁ ⨾ r₂) pr₁r₁⊩Fzx pr₁r₂⊩Fzx') ,
                         subst
                           (λ r' → r' ⊩ ∣ perY .equality ∣ (y , y'))
                           (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r₁ ∷ r₂ ∷ [])) ∙ pr₂pxy≡y _ _))
                           (svG⊩isSingleValuedG z y y' (pr₂ ⨾ r₁) (pr₂ ⨾ r₂) pr₂r₁⊩Gzy pr₂r₂⊩Gzy') }))
                 ; isTotal =
                   do
                     (tlF , tlF⊩isTotalF) ← F .isTotal
                     (tlG , tlG⊩isTotalG) ← G .isTotal
                     let
                       prover : ApplStrTerm as 1
                       prover = ` pair ̇ (` tlF ̇ # fzero) ̇ (` tlG ̇ # fzero)
                     return
                       (λ* prover ,
                       (λ { z r r⊩z~z →
                         do
                           (x , tlFr⊩Fzx) ← tlF⊩isTotalF z r r⊩z~z
                           (y , tlGr⊩Gzy) ← tlG⊩isTotalG z r r⊩z~z
                           return
                             ((x , y) ,
                              (subst
                                (λ r' → r' ⊩ ∣ F .relation ∣ (z , x))
                                (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₁pxy≡x _ _))
                                tlFr⊩Fzx ,
                               subst
                                (λ r' → r' ⊩ ∣ G .relation ∣ (z , y))
                                (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₂pxy≡y _ _))
                                tlGr⊩Gzy)) }))
                 }}

    opaque
      unfolding binProdObRT
      unfolding theFuncRel
      theMap : RTMorphism perZ binProdObRT
      theMap =
        SQ.rec2
          squash/
          (λ F G →
            [ theFuncRel F G ])
          (λ { F F' G (F≤F' , F'≤F) →
            let
              answer =
                do
                  (s , s⊩F≤F') ← F≤F'
                  let
                    prover : ApplStrTerm as 1
                    prover = ` pair ̇ (` s ̇ (` pr₁ ̇ # fzero)) ̇ (` pr₂ ̇ # fzero)
                  return
                    (λ* prover ,
                     (λ { z (x , y) r (pr₁r⊩Fzx , pr₂r⊩Gzy) →
                       subst
                         (λ r' → r' ⊩ ∣ F' .relation ∣ (z , x))
                         (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₁pxy≡x _ _))
                         (s⊩F≤F' z x (pr₁ ⨾ r) pr₁r⊩Fzx) ,
                       subst
                         (λ r' → r' ⊩ ∣ G .relation ∣ (z , y))
                         (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₂pxy≡y _ _))
                         pr₂r⊩Gzy }))
            in
            eq/ _ _ (answer , F≤G→G≤F perZ binProdObRT (theFuncRel F G) (theFuncRel F' G) answer) })
          (λ { F G G' (G≤G' , G'≤G) →
            let
              answer =
                do
                  (s , s⊩G≤G') ← G≤G'
                  let
                    prover : ApplStrTerm as 1
                    prover = ` pair ̇ (` pr₁ ̇ # fzero) ̇ (` s ̇ (` pr₂ ̇ # fzero))
                  return
                    (λ* prover ,
                    (λ { z (x , y) r (pr₁r⊩Fzx , pr₂r⊩Gzy) →
                      (subst
                        (λ r' → r' ⊩ ∣ F .relation ∣ (z , x))
                        (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₁pxy≡x _ _))
                        pr₁r⊩Fzx) ,
                      (subst
                        (λ r' → r' ⊩ ∣ G' .relation ∣ (z , y))
                        (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ∙ pr₂pxy≡y _ _))
                        (s⊩G≤G' z y (pr₂ ⨾ r) pr₂r⊩Gzy)) }))
            in eq/ _ _ (answer , (F≤G→G≤F perZ binProdObRT (theFuncRel F G) (theFuncRel F G') answer)) })
          f g
  opaque
    unfolding UnivProp.theMap
    unfolding UnivProp.theFuncRel
    unfolding binProdPr₁RT
    unfolding binProdPr₁FuncRel
    unfolding composeRTMorphism
    unfolding binProdPr₂FuncRel
    binProductRT : BinProduct RT (X , perX) (Y , perY)
    BinProduct.binProdOb binProductRT = X × Y , binProdObRT
    BinProduct.binProdPr₁ binProductRT = binProdPr₁RT
    BinProduct.binProdPr₂ binProductRT = binProdPr₂RT
    BinProduct.univProp binProductRT {Z , perZ} f g =
      uniqueExists
        (UnivProp.theMap perZ f g)
        -- There is probably a better less kluged version of this proof
        -- But this is the best I could do
        (SQ.elimProp3
          {P = λ f g theMap' → ∀ (foo : theMap' ≡ (UnivProp.theMap perZ f g)) → composeRTMorphism _ _ _ theMap' binProdPr₁RT ≡ f}
          (λ f g h → isPropΠ λ h≡ → squash/ _ _)
          (λ F G theFuncRel' [theFuncRel']≡theMap →
            let
              answer =
                do
                  let
                    (p , q) = (SQ.effective
                        (λ a b → isProp× isPropPropTrunc isPropPropTrunc)
                        (isEquivRelBientailment perZ binProdObRT)
                        theFuncRel'
                        (UnivProp.theFuncRel perZ [ F ] [ G ] F G)
                        [theFuncRel']≡theMap)
                  (p , p⊩theFuncRel'≤theFuncRel) ← p
                  (q , q⊩theFuncRel≤theFuncRel') ← q
                  (relF , relF⊩isRelationalF) ← F .isRelational
                  (stD , stD⊩isStrictDomain) ← theFuncRel' .isStrictDomain
                  let
                    prover : ApplStrTerm as 1
                    prover = ` relF ̇ (` stD ̇ (` pr₁ ̇ # fzero)) ̇ (` pr₁ ̇ (` p ̇ (` pr₁ ̇ # fzero))) ̇ (` pr₁ ̇ (` pr₂ ̇ # fzero))
                  return
                    (λ* prover ,
                    λ z x r r⊩∃ →
                      transport
                        (propTruncIdempotent (F .relation .isPropValued _ _))
                        (do
                          ((x' , y) , (pr₁r⊩theFuncRel'zx'y , (pr₁pr₂r⊩x~x' , pr₂pr₂r⊩y~y))) ← r⊩∃
                          return
                            (subst
                              (λ r' → r' ⊩ ∣ F .relation ∣ (z , x))
                              (sym (λ*ComputationRule prover (r ∷ [])))
                              (relF⊩isRelationalF
                                z z x' x
                                (stD ⨾ (pr₁ ⨾ r)) (pr₁ ⨾ (p ⨾ (pr₁ ⨾ r))) (pr₁ ⨾ (pr₂ ⨾ r))
                                (stD⊩isStrictDomain z (x' , y) (pr₁ ⨾ r) pr₁r⊩theFuncRel'zx'y )
                                (p⊩theFuncRel'≤theFuncRel z (x' , y) (pr₁ ⨾ r) pr₁r⊩theFuncRel'zx'y .fst)
                                 pr₁pr₂r⊩x~x'))))
            in
            eq/ _ _ (answer , F≤G→G≤F perZ perX (composeFuncRel _ _ _ theFuncRel' binProdPr₁FuncRel) F answer))
          f
          g
          (UnivProp.theMap perZ f g)
          refl ,
        SQ.elimProp3
          {P = λ f g theMap' → ∀ (foo : theMap' ≡ (UnivProp.theMap perZ f g)) → composeRTMorphism _ _ _ theMap' binProdPr₂RT ≡ g}
          (λ f g  h → isPropΠ λ h≡ → squash/ _ _)
          (λ F G theFuncRel' [theFuncRel']≡theMap →
            let
              answer =
                do
                  let
                    (p , q) = (SQ.effective
                        (λ a b → isProp× isPropPropTrunc isPropPropTrunc)
                        (isEquivRelBientailment perZ binProdObRT)
                        theFuncRel'
                        (UnivProp.theFuncRel perZ [ F ] [ G ] F G)
                        [theFuncRel']≡theMap)
                  (p , p⊩theFuncRel'≤theFuncRel) ← p
                  (q , q⊩theFuncRel≤theFuncRel') ← q
                  (relG , relG⊩isRelationalG) ← G .isRelational
                  (st , st⊩isStrictDomainTheFuncRel') ← theFuncRel' .isStrictDomain
                  let
                    prover : ApplStrTerm as 1
                    prover = ` relG ̇ (` st ̇ (` pr₁ ̇ # fzero)) ̇ (` pr₂ ̇ (` p ̇ (` pr₁ ̇ # fzero))) ̇ (` pr₁ ̇ (` pr₂ ̇ # fzero))
                  return
                    (λ* prover ,
                    (λ z y r r⊩∃ →
                      transport
                        (propTruncIdempotent (G .relation .isPropValued _ _))
                        (do
                          ((x , y') , (pr₁r⊩theFuncRel'zxy' , pr₁pr₂r⊩y'~y , pr₂pr₂r⊩x~x)) ← r⊩∃
                          return
                            (subst
                              (λ r' → r' ⊩ ∣ G .relation ∣ (z , y))
                              (sym (λ*ComputationRule prover (r ∷ []))) 
                              (relG⊩isRelationalG
                                z z y' y
                                (st ⨾ (pr₁ ⨾ r)) (pr₂ ⨾ (p ⨾ (pr₁ ⨾ r))) (pr₁ ⨾ (pr₂ ⨾ r))
                                (st⊩isStrictDomainTheFuncRel' z (x , y') (pr₁ ⨾ r) pr₁r⊩theFuncRel'zxy')
                                (p⊩theFuncRel'≤theFuncRel z (x , y') (pr₁ ⨾ r) pr₁r⊩theFuncRel'zxy' .snd)
                                pr₁pr₂r⊩y'~y)))))
            in
            eq/ _ _ (answer , F≤G→G≤F perZ perY (composeFuncRel _ _ _ theFuncRel' binProdPr₂FuncRel) G answer))
          f g
          (UnivProp.theMap perZ f g)
          refl)
        (λ ! → isProp× (squash/ _ _) (squash/ _ _))
        λ { !' (!'⋆π₁≡f , !'⋆π₂≡g) →
          SQ.elimProp3
            {P = λ !' f g → ∀ (foo : composeRTMorphism _ _ _ !' binProdPr₁RT ≡ f) (bar : composeRTMorphism _ _ _ !' binProdPr₂RT ≡ g) → UnivProp.theMap perZ f g ≡ !'}
            (λ f g !' → isPropΠ λ _ → isPropΠ λ _ → squash/ _ _)
            (λ !' F G !'⋆π₁≡F !'⋆π₂≡G →
              let
                answer =
                  do
                    let
                      (p , q)   = SQ.effective (isPropValuedBientailment perZ perX) (isEquivRelBientailment perZ perX) (composeFuncRel _ _ _ !' binProdPr₁FuncRel) F !'⋆π₁≡F
                      (p' , q') = SQ.effective (isPropValuedBientailment perZ perY) (isEquivRelBientailment perZ perY) (composeFuncRel _ _ _ !' binProdPr₂FuncRel) G !'⋆π₂≡G
                    (q , q⊩F≤!'⋆π₁) ← q
                    (q' , q'⊩G≤!'⋆π₂) ← q'
                    (rel!' , rel!'⊩isRelational!') ← !' .isRelational
                    (sv!' , sv!'⊩isSingleValued!') ← !' .isSingleValued
                    (tX , tX⊩isTransitiveX) ← perX .isTransitive
                    (sX , sX⊩isSymmetricX) ← perX .isSymmetric
                    (stD!' , stD!'⊩isStrictDomain!') ← !' .isStrictDomain
                    let
                      realizer : ApplStrTerm as 1 -- cursed
                      realizer =
                        ` rel!' ̇ (` stD!' ̇ (` pr₁ ̇ (` q ̇ (` pr₁ ̇ # fzero)))) ̇
                          (` pr₁ ̇ (` q' ̇ (` pr₂ ̇ # fzero))) ̇
                          (` pair ̇
                           (` tX ̇
                            (` sX ̇
                             (` pr₁ ̇
                              (` sv!' ̇ (` pr₁ ̇ (` q ̇ (` pr₁ ̇ # fzero))) ̇ (` pr₁ ̇ (` q' ̇ (` pr₂ ̇ # fzero)))))) ̇
                            (` pr₁ ̇ (` pr₂ ̇ (` q ̇ (` pr₁ ̇ # fzero))))) ̇
                           (` pr₁ ̇ (` pr₂ ̇ (` q' ̇ (` pr₂ ̇ # fzero)))))
                    return
                      (λ* realizer ,
                      (λ { z (x , y) r (pr₁r⊩Fzx , pr₂r⊩Gzy) →
                        transport
                          (propTruncIdempotent (!' .relation .isPropValued _ _))
                          (do
                            ((x' , y') , ⊩!'zx'y' , ⊩x'~x , ⊩y'~y') ← q⊩F≤!'⋆π₁ z x _ pr₁r⊩Fzx
                            ((x'' , y'') , ⊩!'zx''y'' , ⊩y''~y , ⊩x''~x'') ← q'⊩G≤!'⋆π₂ z y _ pr₂r⊩Gzy
                            let
                              (⊩x'~x'' , ⊩y'~y'') = sv!'⊩isSingleValued!' z (x' , y') (x'' , y'') _ _ ⊩!'zx'y' ⊩!'zx''y''
                              ⊩x''~x = tX⊩isTransitiveX x'' x' x _ _ (sX⊩isSymmetricX x' x'' _ ⊩x'~x'') ⊩x'~x 
                            return
                              (subst
                                (λ r' → r' ⊩ ∣ !' .relation ∣ (z , x , y))
                                (sym (λ*ComputationRule realizer (r ∷ [])))
                                (rel!'⊩isRelational!'
                                  z z
                                  (x'' , y'')
                                  (x , y)
                                  _ _ _
                                  (stD!'⊩isStrictDomain!' z (x' , y') _ ⊩!'zx'y') ⊩!'zx''y'' ((subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x'' , x)) (sym (pr₁pxy≡x _ _)) ⊩x''~x) , (subst (λ r' → r' ⊩ ∣ perY .equality ∣ (y'' , y)) (sym (pr₂pxy≡y _ _)) ⊩y''~y))))) }))
              in
              eq/ _ _ (answer , F≤G→G≤F perZ binProdObRT (UnivProp.theFuncRel perZ [ F ] [ G ] F G)
                                 !' answer))
            !' f g !'⋆π₁≡f !'⋆π₂≡g }

binProductsRT : BinProducts RT
binProductsRT (X , perX) (Y , perY) = binProductRT perX perY

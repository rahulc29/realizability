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

  opaque
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

  opaque
    

  opaque
    binProductRT : BinProduct RT (X , perX) (Y , perY)
    BinProduct.binProdOb binProductRT = X × Y , binProdObRT
    BinProduct.binProdPr₁ binProductRT = binProdPr₁RT
    BinProduct.binProdPr₂ binProductRT = {!!}
    BinProduct.univProp binProductRT = {!!}

binProductsRT : BinProducts RT
binProductsRT (X , perX) (Y , perY) = binProductRT perX perY

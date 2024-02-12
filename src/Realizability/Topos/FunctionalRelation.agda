{-# OPTIONS --allow-unsolved-metas #-}
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
open import Cubical.HITs.SetQuotients renaming (rec to setQuotRec; rec2 to setQuotRec2; elimProp to setQuotElimProp; elimProp2 to setQuotElimProp2; elimProp3 to setQuotElimProp3)
open import Cubical.Categories.Category

module Realizability.Topos.FunctionalRelation
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  where

open import Realizability.Tripos.Logic.Syntax {ℓ = ℓ'}
open import Realizability.Tripos.Logic.Semantics {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
open import Realizability.Tripos.Prealgebra.Predicate.Base ca renaming (Predicate to Predicate')
open import Realizability.Tripos.Prealgebra.Predicate.Properties ca
open import Realizability.Tripos.Prealgebra.Meets.Identity ca
open import Realizability.Topos.Object {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial 

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Predicate' renaming (isSetX to isSetPredicateBase)
open PredicateProperties
open Morphism

private λ*ComputationRule = `λ*ComputationRule as fefermanStructure
private λ* = `λ* as fefermanStructure

private
  Predicate = Predicate' {ℓ' = ℓ'} {ℓ'' = ℓ''}

open PartialEquivalenceRelation

record FunctionalRelation {X Y : Type ℓ'} (perX : PartialEquivalenceRelation X) (perY : PartialEquivalenceRelation Y) : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  equalityX = perX .equality
  equalityY = perY .equality

  field
    relation : Predicate (X × Y)
    isStrict :
      ∃[ st ∈ A ]
      (∀ x y r
      → r ⊩ ∣ relation ∣ (x , y)
      ------------------------------------------------------------------------------------
      → (pr₁ ⨾ (st ⨾ r)) ⊩ ∣ equalityX ∣ (x , x) × ((pr₂ ⨾ (st ⨾ r)) ⊩ ∣ equalityY ∣ (y , y)))
    isRelational :
      ∃[ rl ∈ A ]
      (∀ x x' y y' a b c
      → a ⊩ ∣ equalityX ∣ (x , x')
      → b ⊩ ∣ relation ∣ (x , y)
      → c ⊩ ∣ equalityY ∣ (y , y')
      ------------------------------------------
      → (rl ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c))) ⊩ ∣ relation ∣ (x' , y'))
    isSingleValued :
      ∃[ sv ∈ A ]
      (∀ x y y' r₁ r₂
      → r₁ ⊩ ∣ relation ∣ (x , y)
      → r₂ ⊩ ∣ relation ∣ (x , y')
      -----------------------------------
      → (sv ⨾ (pair ⨾ r₁ ⨾ r₂)) ⊩ ∣ equalityY ∣ (y , y'))
    isTotal :
      ∃[ tl ∈ A ]
      (∀ x r → r ⊩ ∣ equalityX ∣ (x , x) → ∃[ y ∈ Y ] (tl ⨾ r) ⊩ ∣ relation ∣ (x , y))

open FunctionalRelation

pointwiseEntailment : ∀ {X Y : Type ℓ'} → (perX : PartialEquivalenceRelation X) → (perY : PartialEquivalenceRelation Y) → (F G : FunctionalRelation perX perY) → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
pointwiseEntailment {X} {Y} perX perY F G = ∃[ pe ∈ A ] (∀ x y r → r ⊩ ∣ F .relation ∣ (x , y) → (pe ⨾ r) ⊩ ∣ G .relation ∣ (x , y))

-- Directly taken from "Realizability with Scott's Graph Model" by Tom de Jong
-- Lemma 4.3.5
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
    (stG , stG⊩isStrictG) ← G .isStrict
    (tlF , tlF⊩isTotalF) ← F .isTotal
    (svG , svG⊩isSingleValuedG) ← G .isSingleValued
    (rlF , rlF⊩isRelational) ← F .isRelational
    let
      prover : ApplStrTerm as 1
      prover = ` rlF ̇ (` pair ̇ (` pr₁ ̇ (` stG ̇ # fzero)) ̇ (` pair ̇ (` tlF ̇ (` pr₁ ̇ (` stG ̇ # fzero))) ̇ (` svG ̇ (` pair ̇ (` r ̇ (` tlF ̇ (` pr₁ ̇ (` stG ̇ # fzero)))) ̇ # fzero))))
    return
      (λ* prover ,
      (λ x y r' r'⊩Gxy →
        subst
          (λ r'' → r'' ⊩ ∣ F .relation ∣ (x , y))
          (sym (λ*ComputationRule prover (r' ∷ [])))
          (transport
            (propTruncIdempotent (F .relation .isPropValued (x , y) _))
            (do
              (y' , Fxy') ← tlF⊩isTotalF x (pr₁ ⨾ (stG ⨾ r')) (stG⊩isStrictG x y r' r'⊩Gxy .fst)
              return
                (rlF⊩isRelational
                  x x y' y
                  (pr₁ ⨾ (stG ⨾ r'))
                  (tlF ⨾ (pr₁ ⨾ (stG ⨾ r')))
                  (svG ⨾ (pair ⨾ (r ⨾ (tlF ⨾ (pr₁ ⨾ (stG ⨾ r')))) ⨾ r'))
                  (stG⊩isStrictG x y r' r'⊩Gxy .fst)
                  Fxy'
                  (svG⊩isSingleValuedG x y' y (r ⨾ (tlF ⨾ (pr₁ ⨾ (stG ⨾ r')))) r' (r⊩F≤G x y' (tlF ⨾ (pr₁ ⨾ (stG ⨾ r'))) Fxy') r'⊩Gxy))))))

equalityFuncRel : ∀ {X : Type ℓ'} → (perX : PartialEquivalenceRelation X) → FunctionalRelation perX perX
relation (equalityFuncRel {X} perX) = perX .equality
isStrict (equalityFuncRel {X} perX) =
  do
    (s , s⊩isSymmetric) ← perX .isSymmetric
    (t , t⊩isTransitive) ← perX .isTransitive
    let
      prover : ApplStrTerm as 1
      prover = ` pair ̇ (` t ̇ (` pair ̇ # fzero ̇ (` s ̇ # fzero))) ̇ (` t ̇ (` pair ̇ (` s ̇ # fzero) ̇ # fzero))
    return
      (λ* prover ,
      λ x x' r r⊩x~x' →
        let
          pr₁proofEq : pr₁ ⨾ (λ* prover ⨾ r) ≡ t ⨾ (pair ⨾ r ⨾ (s ⨾ r))
          pr₁proofEq =
            pr₁ ⨾ (λ* prover ⨾ r)
              ≡⟨ cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ⟩
            pr₁ ⨾ (pair ⨾ (t ⨾ (pair ⨾ r ⨾ (s ⨾ r))) ⨾ (t ⨾ (pair ⨾ (s ⨾ r) ⨾ r)))
              ≡⟨ pr₁pxy≡x _ _ ⟩
            t ⨾ (pair ⨾ r ⨾ (s ⨾ r))
              ∎

          pr₂proofEq : pr₂ ⨾ (λ* prover ⨾ r) ≡ t ⨾ (pair ⨾ (s ⨾ r) ⨾ r)
          pr₂proofEq =
            pr₂ ⨾ (λ* prover ⨾ r)
              ≡⟨ cong (λ x → pr₂ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ⟩
            pr₂ ⨾ (pair ⨾ (t ⨾ (pair ⨾ r ⨾ (s ⨾ r))) ⨾ (t ⨾ (pair ⨾ (s ⨾ r) ⨾ r)))
              ≡⟨ pr₂pxy≡y _ _ ⟩
            t ⨾ (pair ⨾ (s ⨾ r) ⨾ r)
              ∎
        in
        subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym pr₁proofEq) (t⊩isTransitive x x' x r (s ⨾ r) r⊩x~x' (s⊩isSymmetric x x' r r⊩x~x')) ,
        subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x' , x')) (sym pr₂proofEq) (t⊩isTransitive x' x x' (s ⨾ r) r (s⊩isSymmetric x x' r r⊩x~x') r⊩x~x'))
isRelational (equalityFuncRel {X} perX) =
  do
    (s , s⊩isSymmetric) ← perX .isSymmetric
    (t , t⊩isTransitive) ← perX .isTransitive
    let
      prover : ApplStrTerm as 1
      prover = ` t ̇ (` pair ̇ (` t ̇ (` pair ̇ (` s ̇ (` pr₁ ̇ # fzero)) ̇ (` pr₁ ̇ (` pr₂ ̇ # fzero)))) ̇ (` pr₂ ̇ (` pr₂ ̇ # fzero)))

    return
      (λ* prover ,
      (λ x x' y y' a b c a⊩x~x' b⊩x~y c⊩y~y' →
        let
          proofNormalForm : (λ* prover ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c))) ≡ (t ⨾ (pair ⨾ (t ⨾ (pair ⨾ (s ⨾ a) ⨾ b)) ⨾ c))
          proofNormalForm =
            λ* prover ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c))
              ≡⟨ λ*ComputationRule prover ((pair ⨾ a ⨾ (pair ⨾ b ⨾ c)) ∷ []) ⟩
            (t ⨾
            (pair ⨾
             (t ⨾
              (pair ⨾ (s ⨾ (pr₁ ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c)))) ⨾
               (pr₁ ⨾ (pr₂ ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c))))))
             ⨾ (pr₂ ⨾ (pr₂ ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c))))))
             ≡⟨
               cong₂
                 (λ x y → (t ⨾ (pair ⨾ (t ⨾ (pair ⨾ (s ⨾ x) ⨾ y)) ⨾ (pr₂ ⨾ (pr₂ ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c)))))))
                 (pr₁pxy≡x _ _)
                 (pr₁ ⨾ (pr₂ ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c)))
                   ≡⟨ cong (λ x → pr₁ ⨾ x) (pr₂pxy≡y _ _) ⟩
                 pr₁ ⨾ (pair ⨾ b ⨾ c)
                   ≡⟨ pr₁pxy≡x _ _ ⟩
                 b
                   ∎)
              ⟩
            t ⨾ (pair ⨾ (t ⨾ (pair ⨾ (s ⨾ a) ⨾ b)) ⨾ (pr₂ ⨾ (pr₂ ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c)))))
              ≡⟨
                cong
                  (λ x → t ⨾ (pair ⨾ (t ⨾ (pair ⨾ (s ⨾ a) ⨾ b)) ⨾ x))
                  (pr₂ ⨾ (pr₂ ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c)))
                    ≡⟨ cong (λ x → pr₂ ⨾ x) (pr₂pxy≡y _ _) ⟩
                  pr₂ ⨾ (pair ⨾ b ⨾ c)
                    ≡⟨ pr₂pxy≡y _ _ ⟩
                  c
                    ∎)
               ⟩
            t ⨾ (pair ⨾ (t ⨾ (pair ⨾ (s ⨾ a) ⨾ b)) ⨾ c)
              ∎
        in
        subst
          (λ r → r ⊩ ∣ perX .equality ∣ (x' , y'))
          (sym proofNormalForm)
          (t⊩isTransitive x' y y' (t ⨾ (pair ⨾ (s ⨾ a) ⨾ b)) c (t⊩isTransitive x' x y (s ⨾ a) b (s⊩isSymmetric x x' a a⊩x~x') b⊩x~y) c⊩y~y')))
isSingleValued (equalityFuncRel {X} perX) =
  do
    (s , s⊩isSymmetric) ← perX .isSymmetric
    (t , t⊩isTransitive) ← perX .isTransitive
    let
      prover : ApplStrTerm as 1
      prover = ` t ̇ (` pair ̇ (` s ̇ (` pr₁ ̇ # fzero)) ̇ (` pr₂ ̇ # fzero))
    return
      (λ* prover ,
      (λ x y y' r₁ r₂ r₁⊩x~y r₂⊩x~y' →
        let
          proofEq : λ* prover ⨾ (pair ⨾ r₁ ⨾ r₂) ≡ t ⨾ (pair ⨾ (s ⨾ r₁) ⨾ r₂)
          proofEq = {!!}
        in
        subst
          (λ r → r ⊩ ∣ perX .equality ∣ (y , y'))
          (sym proofEq)
          (t⊩isTransitive y x y' (s ⨾ r₁) r₂ (s⊩isSymmetric x y r₁ r₁⊩x~y) r₂⊩x~y')))
isTotal (equalityFuncRel {X} perX) =
  do
    (s , s⊩isSymmetric) ← perX .isSymmetric
    (t , t⊩isTransitive) ← perX .isTransitive
    return (Id , (λ x r r⊩x~x → ∣ x , (subst (λ r → r ⊩ ∣ perX .equality ∣ (x , x)) (sym (Ida≡a r)) r⊩x~x) ∣₁))

composeFuncRel :
  ∀ {X Y Z : Type ℓ'}
  → (perX : PartialEquivalenceRelation X)
  → (perY : PartialEquivalenceRelation Y)
  → (perZ : PartialEquivalenceRelation Z)
  → (F : FunctionalRelation perX perY)
  → (G : FunctionalRelation perY perZ)
  → FunctionalRelation perX perZ

(relation (composeFuncRel {X} {Y} {Z} perX perY perZ F G)) =
  record
    { isSetX = isSet× (perX .isSetX) (perZ .isSetX)
    ; ∣_∣ = λ { (x , z) r → ∃[ y ∈ Y ] (pr₁ ⨾ r) ⊩ ∣ F .relation ∣ (x , y) × (pr₂ ⨾ r) ⊩ ∣ G .relation ∣ (y , z) }
    ; isPropValued = λ x a → isPropPropTrunc }
isStrict (composeFuncRel {X} {Y} {Z} perX perY perZ F G) =
  do
    (stF , stF⊩isStrictF) ← F .isStrict
    (stG , stG⊩isStrictG) ← G .isStrict
    let
      prover : ApplStrTerm as 1
      prover = ` pair ̇ (` pr₁ ̇ (` stF ̇ (` pr₁ ̇ # fzero))) ̇ (` pr₂ ̇ (` stG ̇ (` pr₂ ̇ # fzero)))
    return
      (λ* prover ,
      (λ x z r r⊩∃y →
        transport (propTruncIdempotent {!!})
        (do
          (y , pr₁r⊩Fxy , pr₂r⊩Gxy) ← r⊩∃y
          let
            pr₁proofEq : pr₁ ⨾ (λ* prover ⨾ r) ≡ pr₁ ⨾ (stF ⨾ (pr₁ ⨾ r))
            pr₁proofEq =
              pr₁ ⨾ (λ* prover ⨾ r)
                ≡⟨ cong (λ x → pr₁ ⨾ x) (λ*ComputationRule prover (r ∷ [])) ⟩
              pr₁ ⨾ (pair ⨾ (pr₁ ⨾ (stF ⨾ (pr₁ ⨾ r))) ⨾ (pr₂ ⨾ (stG ⨾ (pr₂ ⨾ r))))
                ≡⟨ pr₁pxy≡x _ _ ⟩
              pr₁ ⨾ (stF ⨾ (pr₁ ⨾ r))
                ∎

            pr₂proofEq : pr₂ ⨾ (λ* prover ⨾ r) ≡ pr₂ ⨾ (stG ⨾ (pr₂ ⨾ r))
            pr₂proofEq = {!!}
          return
            ((subst (λ r' → r' ⊩ ∣ perX .equality ∣ (x , x)) (sym pr₁proofEq) (stF⊩isStrictF x y (pr₁ ⨾ r) pr₁r⊩Fxy .fst)) ,
              subst (λ r' → r' ⊩ ∣ perZ .equality ∣ (z , z)) (sym pr₂proofEq) (stG⊩isStrictG y z (pr₂ ⨾ r) pr₂r⊩Gxy .snd)))))
isRelational (composeFuncRel {X} {Y} {Z} perX perY perZ F G) =
  do
    (rlF , rlF⊩isRelationalF) ← F .isRelational
    (stF , stF⊩isStrictF) ← F .isStrict
    (rlG , rlG⊩isRelationalG) ← G .isRelational
    let
      prover : ApplStrTerm as 1
      prover =
        ` pair ̇
          (` rlF ̇ (` pair ̇ (` pr₁ ̇ # fzero) ̇ (` pair ̇ (` pr₁ ̇ (` pr₁ ̇ (` pr₂ ̇ # fzero))) ̇ (` pr₂ ̇ (` stF ̇ (` pr₁ ̇ (` pr₁ ̇ (` pr₂ ̇ # fzero)))))))) ̇
          (` rlG ̇ (` pair ̇ (` pr₂ ̇ (` stF ̇ (` pr₁ ̇ (` pr₁ ̇ (` pr₂ ̇ # fzero))))) ̇ (` pair ̇ (` pr₂ ̇ (` pr₁ ̇ (` pr₂ ̇ # fzero))) ̇ (` pr₂ ̇ (` pr₂ ̇ # fzero)))))
    return
      (λ* prover ,
      (λ x x' z z' a b c a⊩x~x' b⊩∃y c⊩z~z' →
        do
          (y , pr₁b⊩Fxy , pr₂b⊩Gyz) ← b⊩∃y
          let
            proofEq : λ* prover ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c)) ≡ pair ⨾ (rlF ⨾ (pair ⨾ a ⨾ (pair ⨾ (pr₁ ⨾ b) ⨾ (pr₂ ⨾ (stF ⨾ (pr₁ ⨾ b)))))) ⨾ (rlG ⨾ (pair ⨾ (pr₂ ⨾ (stF ⨾ (pr₁ ⨾ b))) ⨾ (pair ⨾ (pr₂ ⨾ b) ⨾ c)))
            proofEq =
              λ* prover ⨾ (pair ⨾ a ⨾ (pair ⨾ b ⨾ c))
                ≡⟨ λ*ComputationRule prover ((pair ⨾ a ⨾ (pair ⨾ b ⨾ c)) ∷ []) ⟩
              {!!}
          return
            (y ,
            (subst (λ r → r ⊩ ∣ F .relation ∣ (x' , y)) (sym {!!}) (rlF⊩isRelationalF x x' y y a (pr₁ ⨾ b) (pr₂ ⨾ (stF ⨾ (pr₁ ⨾ b))) a⊩x~x' pr₁b⊩Fxy (stF⊩isStrictF x y (pr₁ ⨾ b) pr₁b⊩Fxy .snd)) ,
            (subst (λ r → r ⊩ ∣ G .relation ∣ (y , z')) (sym {!!}) (rlG⊩isRelationalG y y z z' (pr₂ ⨾ (stF ⨾ (pr₁ ⨾ b))) (pr₂ ⨾ b) c (stF⊩isStrictF x y (pr₁ ⨾ b) pr₁b⊩Fxy .snd) pr₂b⊩Gyz c⊩z~z'))))))
isSingleValued (composeFuncRel {X} {Y} {Z} perX perY perZ F G) = {!!}
isTotal (composeFuncRel {X} {Y} {Z} perX perY perZ F G) = {!!}

RTMorphism : ∀ {X Y : Type ℓ'} → (perX : PartialEquivalenceRelation X) → (perY : PartialEquivalenceRelation Y) → Type _
RTMorphism {X} {Y} perX perY = FunctionalRelation perX perY / λ F G → pointwiseEntailment perX perY F G × pointwiseEntailment perX perY G F

idRTMorphism : ∀ {X : Type ℓ'} → (perX : PartialEquivalenceRelation X) → RTMorphism perX perX
idRTMorphism {X} perX = [ equalityFuncRel perX ]

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
  setQuotRec2
    squash/
    (λ F G → [ composeFuncRel perX perY perZ F G ])
    (λ { F F' G (F≤F' , F'≤F) → eq/ (composeFuncRel perX perY perZ F G) (composeFuncRel perX perY perZ F' G) ({!!} , {!!}) })
    (λ { F G G' (G≤G' , G'≤G) → eq/ (composeFuncRel perX perY perZ F G) (composeFuncRel perX perY perZ F G') ({!!} , {!!}) })
    f g

idLRTMorphism :
  ∀ {X Y : Type ℓ'}
  → (perX : PartialEquivalenceRelation X)
  → (perY : PartialEquivalenceRelation Y)
  → (f : RTMorphism perX perY)
  → composeRTMorphism perX perX perY (idRTMorphism perX) f ≡ f
idLRTMorphism {X} {Y} perX perY f =
  setQuotElimProp
    (λ f → squash/ (composeRTMorphism perX perX perY (idRTMorphism perX) f) f)
    (λ f → eq/ _ _ ({!!} , {!!}))
    f

idRRTMorphism :
  ∀ {X Y : Type ℓ'}
  → (perX : PartialEquivalenceRelation X)
  → (perY : PartialEquivalenceRelation Y)
  → (f : RTMorphism perX perY)
  → composeRTMorphism perX perY perY f (idRTMorphism perY) ≡ f
idRRTMorphism {X} {Y} perX perY f =
  setQuotElimProp
    (λ f → squash/ (composeRTMorphism perX perY perY f (idRTMorphism perY)) f)
    (λ f → eq/ _ _ ({!!} , {!!}))
    f

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
  setQuotElimProp3
    (λ f g h →
      squash/
        (composeRTMorphism perX perZ perW (composeRTMorphism perX perY perZ f g) h)
        (composeRTMorphism perX perY perW f (composeRTMorphism perY perZ perW g h)))
    (λ f g h → eq/ _ _ ({!!} , {!!}))
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

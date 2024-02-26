{-# OPTIONS --allow-unsolved-metas #-}
open import Realizability.ApplicativeStructure renaming (Term to ApplStrTerm; λ*-naturality to `λ*ComputationRule; λ*-chain to `λ*) hiding (λ*)
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Fin hiding (Fin; _/_)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category

module Realizability.Topos.FunctionalRelation
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  where

open import Realizability.Tripos.Prealgebra.Predicate ca as Pred hiding (Predicate)
open import Realizability.Tripos.Algebra.Base {ℓ' = ℓ'} {ℓ'' = ℓ''} ca renaming (AlgebraicPredicate to Predicate)
open import Realizability.Topos.Object {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} ca isNonTrivial

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

private λ*ComputationRule = `λ*ComputationRule as fefermanStructure
private λ* = `λ* as fefermanStructure

open PartialEquivalenceRelation

record FunctionalRelation {X Y : Type ℓ'} (perX : PartialEquivalenceRelation X) (perY : PartialEquivalenceRelation Y) : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  equalityX = perX .equality
  equalityY = perY .equality

  field
    relation : Predicate (X × Y)
    isStrictDomain : ∃[ stD ∈ A ] (∀ x y r → r ⊩[ relation ] (x , y) → (stD ⨾ r) ⊩[ equalityX ] (x , x))
    isStrictCodomain : ∃[ stC ∈ A ] (∀ x y r → r ⊩[ relation ] (x , y) → (stC ⨾ r) ⊩[ equalityY ] (y , y))
    isExtensional : ∃[ ext ∈ A ] (∀ x x' y y' r s p → r ⊩[ equalityX ] (x , x') → s ⊩[ equalityY ] (y , y') → p ⊩[ relation ] (x , y) → (ext ⨾ r ⨾ s ⨾ p) ⊩[ relation ] (x' , y'))
    isSingleValued : ∃[ sv ∈ A ] (∀ x y y' r s → r ⊩[ relation ] (x , y) → s ⊩[ relation ] (x , y') → (sv ⨾ r ⨾ s) ⊩[ equalityY ] (y , y'))
    isTotal : ∃[ tl ∈ A ] (∀ x x' r → r ⊩[ equalityX ] (x , x') → ∃[ y ∈ Y ] (tl ⨾ r) ⊩[ relation ] (x , y))


open FunctionalRelation

opaque
  idFuncRel : ∀ {X : Type ℓ'} → (perX : PartialEquivalenceRelation X) → FunctionalRelation perX perX
  relation (idFuncRel {X} perX) = perX .equality
  isStrictDomain (idFuncRel {X} perX) =
    do
      (sm , sm⊩isSymmetric) ← perX .isSymmetric
      (ts , ts⊩isTransitive) ← perX .isTransitive
      let
        prover : ApplStrTerm as 1
        prover = ` ts ̇ # fzero ̇ (` sm ̇ # fzero)
      return
        (λ* prover ,
         λ x x' r r⊩x~x' →
           subst
             (λ r' → r' ⊩[ perX .equality ] (x , x))
             (sym (λ*ComputationRule prover (r ∷ [])))
             (ts⊩isTransitive x x' x r (sm ⨾ r) r⊩x~x' (sm⊩isSymmetric x x' r r⊩x~x')))
  isStrictCodomain (idFuncRel {X} perX) =
    do
      (sm , sm⊩isSymmetric) ← perX .isSymmetric
      (ts , ts⊩isTransitive) ← perX .isTransitive
      let
        prover : ApplStrTerm as 1
        prover = ` ts ̇ (` sm ̇ # fzero) ̇ # fzero
      return
        ((λ* prover) ,
         (λ x x' r r⊩x~x' → subst (λ r' → r' ⊩[ perX .equality ] (x' , x')) (sym (λ*ComputationRule prover (r ∷ []))) (ts⊩isTransitive x' x x' (sm ⨾ r) r (sm⊩isSymmetric x x' r r⊩x~x') r⊩x~x')))
  isExtensional (idFuncRel {X} perX) =
    do
      (sm , sm⊩isSymmetric) ← perX .isSymmetric
      (ts , ts⊩isTransitive) ← perX .isTransitive
      let
        prover : ApplStrTerm as 3
        prover = ` ts ̇ (` ts ̇ (` sm ̇ # 0) ̇ # 2) ̇ # 1
      return
        (λ* prover ,
        (λ x₁ x₂ x₃ x₄ r s p r⊩x₁~x₂ s⊩x₃~x₄ p⊩x₁~x₃ →
          subst
            (λ r' → r' ⊩[ perX .equality ] (x₂ , x₄))
            (sym (λ*ComputationRule prover (r ∷ s ∷ p ∷ [])))
            (ts⊩isTransitive
              x₂ x₃ x₄
              (ts ⨾ (sm ⨾ r) ⨾ p)
              s
              (ts⊩isTransitive
                x₂ x₁ x₃
                (sm ⨾ r) p
                (sm⊩isSymmetric x₁ x₂ r r⊩x₁~x₂)
              p⊩x₁~x₃) s⊩x₃~x₄)))
  isSingleValued (idFuncRel {X} perX) =
    do
      (sm , sm⊩isSymmetric) ← perX .isSymmetric
      (ts , ts⊩isTransitive) ← perX .isTransitive
      let
        prover : ApplStrTerm as 2
        prover = ` ts ̇ (` sm ̇ # 0) ̇ # 1
      return (λ* prover , (λ x x' x'' r s r⊩x~x' s⊩x~x'' → subst (λ r' → r' ⊩[ perX .equality ] (x' , x'')) (sym (λ*ComputationRule prover (r ∷ s ∷ []))) (ts⊩isTransitive x' x x'' (sm ⨾ r) s (sm⊩isSymmetric x x' r r⊩x~x') s⊩x~x'')))
  isTotal (idFuncRel {X} perX) =
    do
      (sm , sm⊩isSymmetric) ← perX .isSymmetric
      (ts , ts⊩isTransitive) ← perX .isTransitive
      return (Id , (λ x x' r r⊩x~x' → ∣ x' , (subst (λ r' → r' ⊩[ perX .equality ] (x , x')) (sym (Ida≡a _)) r⊩x~x') ∣₁))

opaque
  unfolding _⊩[_]_
  composeFuncRel :
    ∀ {X Y Z : Type ℓ'}
    → (perX : PartialEquivalenceRelation X)
    → (perY : PartialEquivalenceRelation Y)
    → (perZ : PartialEquivalenceRelation Z)
    → FunctionalRelation perX perY
    → FunctionalRelation perY perZ
    → FunctionalRelation perX perZ
  relation (composeFuncRel {X} {Y} {Z} perX perY perZ F G) =
    [ record
        { isSetX = isSet× (perX .isSetX) (perZ .isSetX)
        ; ∣_∣ = λ { (x , z) r → ∃[ y ∈ Y ] (pr₁ ⨾ r) ⊩[ F .relation ] (x , y) × (pr₂ ⨾ r) ⊩[ G .relation ] (y , z) }
        ; isPropValued = λ { (x , z) r → isPropPropTrunc } } ]
  isStrictDomain (composeFuncRel {X} {Y} {Z} perX perY perZ F G) =
    do
      (stF , stF⊩isStrictF) ← F .isStrictDomain
      return
        (Id ,
        (λ x z r r⊩∃y →
          transport
            (propTruncIdempotent (isProp⊩ _ (perX .equality) (x , x)))
            (do
              (s , sr⊩) ← r⊩∃y
              (y , pr₁sr⊩Fxy , pr₂sr⊩Gyz) ← sr⊩
              (eqX , [eqX]≡perX) ← []surjective (perX .equality)
              return
                (subst
                  (λ per → (Id ⨾ r) ⊩[ per ] (x , x))
                  [eqX]≡perX
                  (transformRealizes (Id ⨾ r) eqX (x , x) {!!})))))
  isStrictCodomain (composeFuncRel {X} {Y} {Z} perX perY perZ F G) = {!!}
  isExtensional (composeFuncRel {X} {Y} {Z} perX perY perZ F G) = {!!}
  isSingleValued (composeFuncRel {X} {Y} {Z} perX perY perZ F G) = {!!}
  isTotal (composeFuncRel {X} {Y} {Z} perX perY perZ F G) = {!!}

  RT : Category (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ''))) (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ'')))
  Category.ob RT = Σ[ X ∈ Type ℓ' ] PartialEquivalenceRelation X
  Category.Hom[_,_] RT (X , perX) (Y , perY) = FunctionalRelation perX perY
  Category.id RT {X , perX} = idFuncRel perX
  Category._⋆_ RT {X , perX} {Y , perY} {Z , perZ} F G = {!!}
  Category.⋆IdL RT = {!!}
  Category.⋆IdR RT = {!!}
  Category.⋆Assoc RT = {!!}
  Category.isSetHom RT = {!!}

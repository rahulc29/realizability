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
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category

module Realizability.Topos.FunctionalRelation
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  where

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
  isStrictCodomain (idFuncRel {X} perX) = {!!}
  isExtensional (idFuncRel {X} perX) = {!!}
  isSingleValued (idFuncRel {X} perX) = {!!}
  isTotal (idFuncRel {X} perX) = {!!}

  RT : Category (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ''))) (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ'')))
  RT = {!!}

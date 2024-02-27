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

open import Realizability.Tripos.Logic.Syntax {ℓ = ℓ'}
open import Realizability.Tripos.Logic.Semantics {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
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

record FunctionalRelation {X Y : Type ℓ'} (perX : PartialEquivalenceRelation X) (perY : PartialEquivalenceRelation Y) : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  equalityX = perX .equality
  equalityY = perY .equality

  field
    relation : Predicate (X × Y)
    isStrictDomain :
      ∃[ stD ∈ A ]
      (∀ x y r
      → r ⊩ ∣ relation ∣ (x , y)
      ----------------------------------
      → (stD ⨾ r) ⊩ ∣ equalityX ∣ (x , x))
    isStrictCodomain :
      ∃[ stC ∈ A ]
      (∀ x y r
      → r ⊩ ∣ relation ∣ (x , y)
      ----------------------------------
      → (stC ⨾ r) ⊩ ∣ equalityY ∣ (y , y))
    isRelational :
      ∃[ rl ∈ A ]
      (∀ x x' y y' a b c
      → a ⊩ ∣ equalityX ∣ (x , x')
      → b ⊩ ∣ relation ∣ (x , y)
      → c ⊩ ∣ equalityY ∣ (y , y')
      ------------------------------------------
      → (rl ⨾ a ⨾ b ⨾ c) ⊩ ∣ relation ∣ (x' , y'))
    isSingleValued :
      ∃[ sv ∈ A ]
      (∀ x y y' r₁ r₂
      → r₁ ⊩ ∣ relation ∣ (x , y)
      → r₂ ⊩ ∣ relation ∣ (x , y')
      -----------------------------------
      → (sv ⨾ r₁ ⨾ r₂) ⊩ ∣ equalityY ∣ (y , y'))
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
    (tlF , tlF⊩isTotalF) ← F .isTotal
    (svG , svG⊩isSingleValuedG) ← G .isSingleValued
    (rlF , rlF⊩isRelational) ← F .isRelational
    let
      prover : ApplStrTerm as 1
      prover = {!!}
    return {!!}

RTMorphism : ∀ {X Y : Type ℓ'} → (perX : PartialEquivalenceRelation X) → (perY : PartialEquivalenceRelation Y) → Type _
RTMorphism {X} {Y} perX perY = FunctionalRelation perX perY / λ F G → pointwiseEntailment perX perY F G × pointwiseEntailment perX perY G F

idRTMorphism : ∀ {X : Type ℓ'} → (perX : PartialEquivalenceRelation X) → RTMorphism perX perX
idRTMorphism {X} perX = {!!}

composeRTMorphism :
  ∀ {X Y Z : Type ℓ'}
  → (perX : PartialEquivalenceRelation X)
  → (perY : PartialEquivalenceRelation Y)
  → (perZ : PartialEquivalenceRelation Z)
  → (f : RTMorphism perX perY)
  → (g : RTMorphism perY perZ)
  ----------------------------------------
  → RTMorphism perX perZ
composeRTMorphism {X} {Y} {Z} perX perY perZ f g = {!!}

idLRTMorphism :
  ∀ {X Y : Type ℓ'}
  → (perX : PartialEquivalenceRelation X)
  → (perY : PartialEquivalenceRelation Y)
  → (f : RTMorphism perX perY)
  → composeRTMorphism perX perX perY (idRTMorphism perX) f ≡ f
idLRTMorphism {X} {Y} perX perY f = {!!}

idRRTMorphism :
  ∀ {X Y : Type ℓ'}
  → (perX : PartialEquivalenceRelation X)
  → (perY : PartialEquivalenceRelation Y)
  → (f : RTMorphism perX perY)
  → composeRTMorphism perX perY perY f (idRTMorphism perY) ≡ f
idRRTMorphism {X} {Y} perX perY f = {!!}

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
assocRTMorphism {X} {Y} {Z} {W} perX perY perZ perW f g h = {!!}

RT : Category (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ''))) (ℓ-max (ℓ-suc ℓ) (ℓ-max (ℓ-suc ℓ') (ℓ-suc ℓ'')))
Category.ob RT = Σ[ X ∈ Type ℓ' ] PartialEquivalenceRelation X
Category.Hom[_,_] RT (X , perX) (Y , perY) = RTMorphism perX perY
Category.id RT {X , perX} = idRTMorphism perX
Category._⋆_ RT {X , perX} {y , perY} {Z , perZ} f g = composeRTMorphism perX perY perZ f g
Category.⋆IdL RT {X , perX} {Y , perY} f = idLRTMorphism perX perY f
Category.⋆IdR RT {X , perX} {Y , perY} f = idRRTMorphism perX perY f
Category.⋆Assoc RT {X , perX} {Y , perY} {Z , perZ} {W , perW} f g h = assocRTMorphism perX perY perZ perW f g h
Category.isSetHom RT = squash/

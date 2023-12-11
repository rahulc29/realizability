-- It is convenient to have the statement of the characterisation lemma
-- seperate of the actual implementation. The other modules can then simply
-- assume this lemma by importing this.
-- Besides, the proof is a little hairy and we'd rather not think about it too much 😉
{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection
open import Cubical.Categories.Category
open import Cubical.Categories.Regular.Base
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Realizability.CombinatoryAlgebra

module Realizability.Assembly.Regular.CharLemma {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.BinProducts ca

module _
    {X Y : Type ℓ}
    (xs : Assembly X)
    (ys : Assembly Y)
    (e : AssemblyMorphism xs ys)
    where
      _⊩X_ = xs ._⊩_
      _⊩Y_ = ys ._⊩_

      tracksSurjection : (a : A) → Type ℓ
      tracksSurjection a = ∀ y b → (b ⊩Y y) → ∃[ x ∈ X ] (e .map x ≡ y) × ((a ⨾ b) ⊩X x)

      isSurjectivelyTracked : Type ℓ
      isSurjectivelyTracked = ∃[ a ∈ A ] tracksSurjection a

      isSurjectivelyTracked→isSurjective : isSurjectivelyTracked → isSurjection (e .map)
      isSurjectivelyTracked→isSurjective tracked y =
                                                 do
                                                   (a , aTracksSurjection) ← tracked
                                                   (b , bRealizes) ← ys .⊩surjective y
                                                   (x , ex≡y , ab⊩x) ← aTracksSurjection y b bRealizes
                                                   return (x , ex≡y)

      isPropIsSurjectivelyTracked : isProp isSurjectivelyTracked
      isPropIsSurjectivelyTracked = isPropPropTrunc

CharLemma : Type (ℓ-suc ℓ)
CharLemma = ∀ {X Y} (xs : Assembly X) (ys : Assembly Y) e
            → (isRegularEpic ASM e → isSurjectivelyTracked xs ys e)
            × (isSurjectivelyTracked xs ys e → isRegularEpic ASM e)


module CharLemmaConsequences (cl : CharLemma) where
  isRegularEpicASM≃isSurjectivelyTracked : ∀ {X Y} (xs : Assembly X) (ys : Assembly Y) e
                                         → isRegularEpic ASM e ≃ isSurjectivelyTracked xs ys e
  isRegularEpicASM≃isSurjectivelyTracked xs ys e =
    propBiimpl→Equiv
      (isPropIsRegularEpic ASM e)
      (isPropIsSurjectivelyTracked xs ys e)
      (cl xs ys e .fst)
      (cl xs ys e .snd)

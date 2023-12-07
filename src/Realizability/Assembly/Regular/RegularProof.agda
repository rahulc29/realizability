{-# OPTIONS --cubical #-}
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Regular.Base

module Realizability.Assembly.Regular.RegularProof {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Regular.CharLemma ca
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca

module _
  (charLemma :
    ∀ {X Y}
      (xs : Assembly X)
      (ys : Assembly Y)
      (e : AssemblyMorphism xs ys)
    → CharLemma xs ys e) where

  open IsRegular
  RegularASM : IsRegular ASM
  RegularASM = record
                 { arrowHasKernelPairs = {!!}
                 ; kPairHasCoequalizer = λ f → {!!}
                 ; regularEpiPreservedPullback = λ f g x p → {!!}
                 }
       

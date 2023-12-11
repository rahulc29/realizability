{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Regular.Base

module Realizability.Assembly.Regular.RegularProof {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Regular.CharLemma ca
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
-- See Cobase instead
module _
  (charLemma : CharLemma) where

  open IsRegular
  RegularASM : IsRegular ASM
  RegularASM = record
                 { arrowHasKernelPairs = {!!}
                 ; kPairHasCoequalizer = λ f → {!!}
                 ; regularEpiPreservedPullback = λ f g x p → {!!}
                 }
       

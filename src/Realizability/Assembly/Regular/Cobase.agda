{-# OPTIONS --cubical --allow-unsolved-metas #-}

open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.Surjection
open import Cubical.Categories.Regular.Base
open import Cubical.Categories.Regular.KernelPair
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Coequalizers
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad

module Realizability.Assembly.Regular.Cobase {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Regular.CharLemma ca
open import Realizability.Assembly.BinProducts ca
open import Realizability.Assembly.Coequalizers ca
open import Realizability.Assembly.Regular.KernelPairs ca

open ASMKernelPairs
open Pullback
module
  PullbackPreservation
  {X Y Z}
  (xs : Assembly X)
  (ys : Assembly Y)
  (zs : Assembly Z)
  (e : AssemblyMorphism xs ys)
  (f : AssemblyMorphism zs ys)
  (eIsRegular : isRegularEpic ASM e)
  (cl : CharLemma)
  (p : Pullback ASM (cospan (X , xs) (Y , ys) (Z , zs) e f)) where
    p₁ = p .pbPr₁
    p₂ = p .pbPr₂

    isSurjectivelyTrackedE : isSurjectivelyTracked _ _ e
    isSurjectivelyTrackedE = cl xs ys e .fst eIsRegular

    eIsSurjection : isSurjection (e .map)
    eIsSurjection = isSurjectivelyTracked→isSurjective _ _ e isSurjectivelyTrackedE

    isSurjectivelyTrackedP₂ : isSurjectivelyTracked _ _ p₂
    isSurjectivelyTrackedP₂ =
      do
        (f~ , f~tracks) ← f .tracker
        (b  , bTracksSurjectivity) ← isSurjectivelyTrackedE
        return
          (s ⨾ (s ⨾ (k ⨾ pair) ⨾ (s ⨾ (k ⨾ b) ⨾ (s ⨾ (k ⨾ f~) ⨾ Id))) ⨾ Id ,
          λ z zᵣ zᵣ⊩z →
            do
              return ({!!} , {!!}))

module _ (cl : CharLemma) where
  open ASMKernelPairs
  open PullbackPreservation
  RegularASM : IsRegular ASM
  RegularASM = record
                 { arrowHasKernelPairs = ∣ (λ {xs} {ys} f → makeKernelPair (xs .snd) (ys .snd) f) ∣₁
                 ; kPairHasCoequalizer = λ {xs} {ys} f kpF → ∣ ASMCoequalizer (kpF .pbOb .snd) (xs .snd) (kpF .pbPr₁) (kpF .pbPr₂) ∣₁
                 ; regularEpiPreservedPullback = λ {Y} {Z} {X} f e eIsRegular p
                 → cl (p .pbOb .snd) (Z .snd) (p .pbPr₂) .snd (isSurjectivelyTrackedP₂ (X .snd) (Y .snd) (Z .snd) e f eIsRegular cl p)
                 }


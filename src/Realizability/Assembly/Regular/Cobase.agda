{-# OPTIONS --cubical #-}

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

module ASMKernelPairs {X Y} (xs : Assembly X) (ys : Assembly Y) (f : AssemblyMorphism xs ys) where

  xs⊗xs = xs ⊗ xs

  kernelPairType = Σ[ x ∈ X ] Σ[ x' ∈ X ] f .map x ≡ f .map x'

  kernelPairOb : Assembly kernelPairType
  kernelPairOb .isSetX = isSetΣ (xs .isSetX) λ x → isSetΣ (xs .isSetX) (λ x' → isProp→isSet (ys .isSetX _ _))
  kernelPairOb ._⊩_ a (x , x' , fx≡fx') = xs⊗xs ._⊩_ a (x , x')
  kernelPairOb .⊩isPropValued a (x , x' , fx≡fx') = xs⊗xs .⊩isPropValued a (x , x')
  kernelPairOb .⊩surjective (x , x' , fx≡fx') = xs⊗xs .⊩surjective (x , x')

  k₁ : AssemblyMorphism kernelPairOb xs
  k₁ .map (x , x' , fx≡fx') = x
  k₁ .tracker = ∣ pr₁ , (λ (x , x' , fx≡fx') r r⊩xx' → r⊩xx' .fst) ∣₁

  k₂ : AssemblyMorphism kernelPairOb xs
  k₂ .map (x , x' , fx≡fx') = x'
  k₂ .tracker = ∣ pr₂ , (λ (x , x' , fx≡fx') r r⊩xx' → r⊩xx' .snd) ∣₁

  k₁⊚f≡k₂⊚f : k₁ ⊚ f ≡ k₂ ⊚ f
  k₁⊚f≡k₂⊚f =
    AssemblyMorphism≡ _ _
      (funExt λ (x , x' , fx≡fx')
        → f .map (k₁ .map (x , x' , fx≡fx'))
              ≡⟨ refl ⟩
            f .map x
              ≡⟨ fx≡fx' ⟩
            f .map x'
              ≡⟨ refl ⟩
            f .map (k₂ .map (x , x' , fx≡fx'))
              ∎)

  module KPUnivProp {Z} {zs : Assembly Z}
                    (l₁ l₂ : AssemblyMorphism zs xs)
                    (l₁⊚f≡l₂⊚f : l₁ ⊚ f ≡ l₂ ⊚ f) where

         m : AssemblyMorphism zs kernelPairOb
         m .map z = l₁ .map z , l₂ .map z , λ i → l₁⊚f≡l₂⊚f i .map z
         m .tracker = {!!}

         module _ (! : AssemblyMorphism zs kernelPairOb)
                  (l₁≡!⊚k₁ : l₁ ≡ ! ⊚ k₁)
                  (l₂≡!⊚k₂ : l₂ ≡ ! ⊚ k₂)
                  (z : Z) where
                l₁z≡fst! : l₁ .map z ≡ ! .map z .fst
                l₁z≡fst! = l₁ .map z
                             ≡[ i ]⟨ l₁≡!⊚k₁ i .map z ⟩
                           k₁ .map (! .map z)
                             ≡⟨ refl ⟩
                           ! .map z .fst
                             ∎
                l₂z≡sndfst! : l₂ .map z ≡  ! .map z .snd .fst
                l₂z≡sndfst! = l₂ .map z
                                 ≡[ i ]⟨ l₂≡!⊚k₂ i .map z ⟩
                              k₂ .map (! .map z)
                                 ≡⟨ refl ⟩
                              ! .map z .snd .fst
                                 ∎

                isSet'Y = isSet→isSet' (ys .isSetX)
                {-
                This is an important proof in the sense that it is slightly cubical.
                Recall the definition of a set : X is a set iff ∀ (x y : X) (p q : x ≡ y) → p ≡ q
                Notice that this (mainstream) definition of a set can also be conceptualised as
                saying that the following square always has a filler (there is a homotopy between p and q)
                    p
                x — — — > y
                ‖         ‖
                ‖         ‖          ^
                ‖         ‖        j |
                x — — — > y          ∙ — >
                    q                 i

                always has a filler.
                However, for this proof to work we require *all* squares to have a filler.
                I'm not sure how this could be done in the HoTT book.
                Applying J twice should work, but for some reason, when I tried it,
                it did not work. 
                -}
                uglyPathLemma : PathP (λ i → f .map (l₁z≡fst! i) ≡  f .map (l₂z≡sndfst! i)) (λ i → l₁⊚f≡l₂⊚f i .map z) (snd (snd (! .map z)))
                uglyPathLemma i j =
                              isSet'Y
                               {a₀₀ = f .map (l₁ .map z)}
                               {a₀₁ = f .map (l₂ .map z)}
                               (λ k → l₁⊚f≡l₂⊚f k .map z)
                               {a₁₀ = f .map (! .map z .fst)}
                               {a₁₁ = f .map (! .map z .snd .fst)}
                               (! .map z .snd .snd)
                               (cong (f .map) l₁z≡fst!)
                               (cong (f .map) l₂z≡sndfst!)
                               i j
                  {- This is what I had attempted :
                  
                    explicitJ (f .map (l₁ .map z)) -- J₁ ⊢ x
                            (f .map (l₂ .map z)) -- J₁ ⊢ y
                            (λ k → l₁⊚f≡l₂⊚f k .map z) -- J₁ ⊢ x ≡ y
                            (λ l₁⊚fz l₂⊚fz l₁⊚fz≡l₂⊚fz → {!!}) -- J₁ ⊢ P
                            (explicitJ -- J₁ ⊢ P x x refl
                              (f .map (! .map z .fst)) -- J₂ ⊢ x
                              (f .map (! .map z .snd .fst)) -- J₂ ⊢ y
                              (! .map z .snd .snd) -- J₂ ⊢ x ≡ y
                              (λ f!zfst f!zsndfst f!zfst≡f!zsndfst → Y) -- J₂ ⊢ P 
                              (ys .isSetX (f .map (l₁ .map z))
                                          (f .map (! .map z .fst))
                                          (cong (f .map) l₁z≡fst!)
                                          {!cong (f .map) l₂z≡sndfst!!} i j)) -- J₂ ⊢ P x x refl -}

         uniqueness : ∀ (! : AssemblyMorphism zs kernelPairOb) → ((l₁ ≡ ! ⊚ k₁) × (l₂ ≡ ! ⊚ k₂)) → m ≡ !
         uniqueness ! (l₁≡!⊚k₁ , l₂≡!⊚k₂) =
           AssemblyMorphism≡ _ _
             (funExt (λ z →
               ΣPathP (l₁z≡fst! ! l₁≡!⊚k₁ l₂≡!⊚k₂ z ,
               ΣPathP ((l₂z≡sndfst! ! l₁≡!⊚k₁ l₂≡!⊚k₂ z) , uglyPathLemma ! l₁≡!⊚k₁ l₂≡!⊚k₂ z))))

  open KPUnivProp
  kpUnivProp : isPullback ASM (kernelPairCospan ASM f) k₁ k₂ k₁⊚f≡k₂⊚f
  kpUnivProp {Z , zs} l₁ l₂ l₁⊚f≡l₂⊚f =
    uniqueExists
      (m l₁ l₂ l₁⊚f≡l₂⊚f)
      ((AssemblyMorphism≡ _ _ (funExt (λ z → refl))) , AssemblyMorphism≡ _ _ (funExt (λ z → refl)))
      (λ ! → isProp× (isSetAssemblyMorphism zs xs _ _) (isSetAssemblyMorphism zs xs _ _))
      λ ! eq@(l₁≡!⊚k₁ , l₂≡!⊚k₂) → uniqueness l₁ l₂ l₁⊚f≡l₂⊚f ! eq

  makeKernelPair : KernelPair ASM f
  makeKernelPair = record
                             { pbOb = kernelPairType , kernelPairOb
                             ; pbPr₁ = k₁
                             ; pbPr₂ = k₂
                             ; pbCommutes = k₁⊚f≡k₂⊚f
                             ; univProp = kpUnivProp
                             }
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
        return (s ⨾ (s ⨾ (k ⨾ pair) ⨾ (s ⨾ (k ⨾ b) ⨾ (s ⨾ (k ⨾ f~) ⨾ Id))) ⨾ Id , λ z zᵣ zᵣ⊩z → ∣ {!!} , {!!} , {!!} ∣₁)

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


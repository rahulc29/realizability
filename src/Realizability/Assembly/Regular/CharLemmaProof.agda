{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Realizability.CombinatoryAlgebra
open import Realizability.Choice
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Data.Sigma
open import Cubical.Categories.Limits.Coequalizers
open import Cubical.Categories.Regular.Base

module Realizability.Assembly.Regular.CharLemmaProof {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) (choice : Choice ℓ ℓ) where

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.BinProducts ca
open import Realizability.Assembly.Regular.CharLemma ca
open import Realizability.Assembly.Regular.KernelPairs ca

module SurjectiveTrackingMakesRegularEpic
  {X Y : Type ℓ} 
  (xs : Assembly X)
  (ys : Assembly Y)
  (f : AssemblyMorphism xs ys)
  (fIsSurjectivelyTracked : isSurjectivelyTracked xs ys f) where

  open ASMKernelPairs xs ys f

  fIsSurjection : isSurjection (f .map)
  fIsSurjection = isSurjectivelyTracked→isSurjective xs ys f fIsSurjectivelyTracked

  module _
    {Z}
    (zs : Assembly Z)
    (g : AssemblyMorphism xs zs)
    (k₁⊚g≡k₂⊚g : k₁ ⊚ g ≡ k₂ ⊚ g) where

    _⊩Z_ = zs ._⊩_

    fx≡fx'→gx≡gx' : ∀ x x' → f .map x ≡ f .map x' → g .map x ≡ g .map x'
    fx≡fx'→gx≡gx' x x' fx≡fx' i = k₁⊚g≡k₂⊚g i .map (x , x' , fx≡fx')

    module _
           (h h' : AssemblyMorphism ys zs)
           (f⊚h≡q : f ⊚ h ≡ g)
           (f⊚h'≡q : f ⊚ h' ≡ g) where
             hIsUnique : h ≡ h'
             hIsUnique =
               AssemblyMorphism≡ _ _
                 (funExt λ y → equivFun (propTruncIdempotent≃ (zs .isSetX _ _))
                   (do
                     (x , fx≡y) ← fIsSurjection y
                     return (h .map y
                               ≡⟨ sym (cong (λ t → h .map t) fx≡y) ⟩
                            h .map (f .map x)
                              ≡[ i ]⟨ f⊚h≡q i .map x ⟩
                            (g .map x)
                              ≡[ i ]⟨ f⊚h'≡q (~ i) .map x ⟩
                            h' .map (f .map x)
                              ≡⟨ cong (λ t → h' .map t) fx≡y ⟩
                            h' .map y
                              ∎)))

    f⊚h≡gIsProp : isProp (Σ[ h ∈ AssemblyMorphism ys zs ] (f ⊚ h ≡ g))
    f⊚h≡gIsProp = λ { (h , e⊚h≡q) (h' , e⊚h'≡q)
                   → Σ≡Prop (λ x → isSetAssemblyMorphism xs zs (f ⊚ x) g) (hIsUnique h h' e⊚h≡q e⊚h'≡q ) }

    ∃h→Σh : ∃[ h ∈ AssemblyMorphism ys zs ] (f ⊚ h ≡ g) → Σ[ h ∈ AssemblyMorphism ys zs ] (f ⊚ h ≡ g)
    ∃h→Σh ∃h = equivFun (propTruncIdempotent≃ f⊚h≡gIsProp) ∃h

    module _
      (f⁻¹ : Y → X)
      (f⁻¹IsSection : section (f .map) f⁻¹) where

        -- I will fix having to do this one day
        uglyCalculation : ∀ b g~ r → (s ⨾ (k ⨾ g~) ⨾ (s ⨾ (k ⨾ r) ⨾ Id) ⨾ b) ≡ g~ ⨾ (r ⨾ b)
        uglyCalculation b g~ r =
          s ⨾ (k ⨾ g~) ⨾ (s ⨾ (k ⨾ r) ⨾ Id) ⨾ b
            ≡⟨ sabc≡ac_bc _ _ _ ⟩
          k ⨾ g~ ⨾ b ⨾ (s ⨾ (k ⨾ r) ⨾ Id ⨾ b)
            ≡⟨ cong (λ x → x ⨾ _) (kab≡a _ _) ⟩
          g~ ⨾ (s ⨾ (k ⨾ r) ⨾ Id ⨾ b)
            ≡⟨ cong (λ x → g~ ⨾ x) (sabc≡ac_bc _ _ _) ⟩
          g~ ⨾ (k ⨾ r ⨾ b ⨾ (Id ⨾ b))
            ≡⟨ cong (λ x → g~ ⨾ (x ⨾ (Id ⨾ b))) (kab≡a _ _) ⟩
          g~ ⨾ (r ⨾ (Id ⨾ b))
            ≡⟨ cong (λ x → g~ ⨾ (r ⨾ x)) (Ida≡a _) ⟩
          g~ ⨾ (r ⨾ b)
            ∎

        hMap : Y → Z
        hMap y = g .map (f⁻¹ y)

        fx≡ff⁻¹fx : ∀ x → f .map (f⁻¹ (f .map x)) ≡ f .map x
        fx≡ff⁻¹fx x = f⁻¹IsSection (f .map x)

        gx≡gf⁻¹fx : ∀ x → g .map (f⁻¹ (f .map x)) ≡ g .map x
        gx≡gf⁻¹fx x = fx≡fx'→gx≡gx' (f⁻¹ (f .map x)) x (fx≡ff⁻¹fx x)
        
        hfx≡gx : ∀ x → hMap (f .map x) ≡ g .map x
        hfx≡gx x = gx≡gf⁻¹fx x
        
        h : AssemblyMorphism ys zs
        h .map y = hMap y
        h .tracker =
          do
            (g~ , g~tracks) ← g .tracker
            (r , rWitness) ← fIsSurjectivelyTracked
            return
              (s ⨾ (k ⨾ g~) ⨾ (s ⨾ (k ⨾ r) ⨾ Id) ,
              (λ y b b⊩y →
                equivFun
                  (propTruncIdempotent≃ (zs .⊩isPropValued _ _))
                  (do
                    (x , fx≡y , rb⊩x) ← rWitness y b b⊩y
                    return
                      (subst
                        (λ h~ → h~ ⊩Z (h .map y))
                        (sym (uglyCalculation b g~ r))
                        (subst (λ x → (g~ ⨾ (r ⨾ b)) ⊩Z x)
                        (sym (subst (λ y → hMap y ≡ g .map x) fx≡y (hfx≡gx x)))
                        (g~tracks x (r ⨾ b) rb⊩x))))))

        

        f⊚h≡g : f ⊚ h ≡ g
        f⊚h≡g = AssemblyMorphism≡ _ _ (funExt λ x → hfx≡gx x)

    ∃h : ∃[ h ∈ AssemblyMorphism ys zs ] (f ⊚ h ≡ g)
    ∃h =
      do
        (f⁻¹ , f⁻¹IsSection) ← choice X Y (xs .isSetX) (ys .isSetX) (f .map) fIsSurjection
        return (h f⁻¹ f⁻¹IsSection , f⊚h≡g f⁻¹ f⁻¹IsSection)

    Σh : Σ[ h ∈ AssemblyMorphism ys zs ] (f ⊚ h ≡ g)
    Σh = ∃h→Σh ∃h

  kernelPairCoeqUnivProp : ∀ {Z} {zs : Assembly Z} → (g : AssemblyMorphism xs zs) → (k₁ ⊚ g ≡ k₂ ⊚ g) → ∃![ ! ∈ AssemblyMorphism ys zs ] (f ⊚ ! ≡ g)
  kernelPairCoeqUnivProp {Z} {zs} g k₁⊚g≡k₂⊚g =
    uniqueExists
      (Σh zs g k₁⊚g≡k₂⊚g .fst)
      (Σh zs g k₁⊚g≡k₂⊚g .snd)
      (λ ! → isSetAssemblyMorphism _ _ _ _)
      λ ! f⊚!≡g → hIsUnique zs g k₁⊚g≡k₂⊚g (Σh zs g k₁⊚g≡k₂⊚g .fst) ! (Σh zs g k₁⊚g≡k₂⊚g .snd) f⊚!≡g

  kernelPairCoequalizer : IsCoequalizer {C = ASM} k₁ k₂ f
  kernelPairCoequalizer = record { glues = k₁⊚f≡k₂⊚f ; univProp = λ q qGlues → kernelPairCoeqUnivProp q qGlues }

  isRegularEpicASMe : isRegularEpic ASM f
  isRegularEpicASMe = ∣ (kernelPairType , kernelPairOb) , ∣ k₁ , ∣ k₂ , kernelPairCoequalizer ∣₁ ∣₁ ∣₁

open SurjectiveTrackingMakesRegularEpic

charLemmaProof : CharLemma
charLemmaProof = λ xs ys e → (λ eIsRegular → {!!}) , λ eIsSurjectivelyTracked → isRegularEpicASMe xs ys e eIsSurjectivelyTracked

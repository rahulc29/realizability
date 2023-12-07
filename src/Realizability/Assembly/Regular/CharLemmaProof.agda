{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Data.Sigma
open import Cubical.Categories.Limits.Coequalizers

module Realizability.Assembly.Regular.CharLemmaProof {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.BinProducts ca
open import Realizability.Choice

open AssemblyMorphism

module _
    {X Y : Type ℓ}
    (xs : Assembly X)
    (ys : Assembly Y)
    (e : AssemblyMorphism xs ys)
    where
      _⊩X_ = xs ._⊩_
      _⊩Y_ = ys ._⊩_
      _⊩X×X_ = (xs ⊗ xs) ._⊩_
      
      -- First, isSurjection(e .map) and surjective tracking
      -- together create a regular epi in ASM

      tracksSurjection : (a : A) → Type ℓ
      tracksSurjection a = ∀ y b → (b ⊩Y y) → ∃[ x ∈ X ] (e .map x ≡ y) × ((a ⨾ b) ⊩X x)
      module _
        (surjection : isSurjection (e .map))
        (surjectionIsTracked : ∃[ a ∈ A ] tracksSurjection a)
        (choice : Choice ℓ ℓ)
        where

        kernelType : Type ℓ
        kernelType = Σ[ x ∈ X ] Σ[ x' ∈ X ] (e .map x ≡ e .map x')

        kernelAssembly : Assembly kernelType
        kernelAssembly .isSetX = isSetΣ (xs .isSetX) (λ x → isSetΣ (xs .isSetX) (λ x' → isProp→isSet (ys .isSetX _ _)))
        kernelAssembly ._⊩_ r (x , x' , ex≡ex') = (xs ⊗ xs) ._⊩_ r (x , x')
        kernelAssembly .⊩isPropValued r (x , x' , ex≡ex') = (xs ⊗ xs) .⊩isPropValued r (x , x')
        kernelAssembly .⊩surjective (x , x' , ex≡ex') = (xs ⊗ xs) .⊩surjective (x , x')

        -- Kernel Pairs
        k₁ : AssemblyMorphism kernelAssembly xs
        k₁ .map (x , x' , ex≡ex') = x
        k₁ .tracker = ∣ pr₁ , (λ (x , x' , ex≡ex') r r⊩xx' → r⊩xx' .fst) ∣₁

        
        k₂ : AssemblyMorphism kernelAssembly xs
        k₂ .map (x , x' , ex≡ex') = x'
        k₂ .tracker = ∣ pr₂ , (λ (x , x' , ex≡ex') r r⊩xx' → r⊩xx' .snd) ∣₁

        module _ {W : Type ℓ}
                 {ws : Assembly W}
                 (q : AssemblyMorphism xs ws)
                 (k₁q≡k₂q : k₁ ⊚ q ≡ k₂ ⊚ q) where

                 module _
                   (h h' : AssemblyMorphism ys ws)
                   (e⊚h≡q : e ⊚ h ≡ q)
                   (e⊚h'≡q : e ⊚ h' ≡ q) where
                   hIsUnique : h ≡ h'
                   hIsUnique =
                     AssemblyMorphism≡ _ _
                       (funExt λ y → equivFun (propTruncIdempotent≃ (ws .isSetX _ _))
                         (do
                           (x , ex≡y) ← surjection y
                           return (h .map y
                                     ≡⟨ sym (cong (λ t → h .map t) ex≡y) ⟩
                                   h .map (e .map x)
                                     ≡[ i ]⟨ e⊚h≡q i .map x ⟩
                                  (q .map x)
                                     ≡[ i ]⟨ e⊚h'≡q (~ i) .map x ⟩
                                  h' .map (e .map x)
                                     ≡⟨ cong (λ t → h' .map t) ex≡y ⟩
                                  h' .map y
                                     ∎)))
                   
                 e⊚t≡qIsProp : isProp (Σ[ t ∈ AssemblyMorphism ys ws ] (e ⊚ t ≡ q))
                 e⊚t≡qIsProp = λ { (h , e⊚h≡q) (h' , e⊚h'≡q)
                   → Σ≡Prop (λ x → isSetAssemblyMorphism xs ws (e ⊚ x) q) (hIsUnique h h' e⊚h≡q e⊚h'≡q ) }

                 ∃t→Σt : ∃[ t ∈ AssemblyMorphism ys ws ] (e ⊚ t ≡ q) → Σ[ t ∈ AssemblyMorphism ys ws ] (e ⊚ t ≡ q)
                 ∃t→Σt ∃t = equivFun (propTruncIdempotent≃ e⊚t≡qIsProp) ∃t

        -- I have cooked one ugly proof ngl 😀🔫
        open IsCoequalizer
        eIsCoequalizer : IsCoequalizer {C = ASM} k₁ k₂ e
        eIsCoequalizer .glues = AssemblyMorphism≡ _ _ (funExt λ (x , x' , ex≡ex') → ex≡ex')
        eIsCoequalizer .univProp {W , ws} q k₁q≡k₂q =
          uniqueExists
          (∃t→Σt q k₁q≡k₂q ∃t .fst)
          (∃t→Σt q k₁q≡k₂q ∃t .snd)
          (λ t → isSetAssemblyMorphism _ _ _ _)
          λ t e⊚t≡q → λ i → e⊚t≡qIsProp q k₁q≡k₂q (∃t→Σt q k₁q≡k₂q ∃t) (t , e⊚t≡q) i .fst where
            _⊩W_ = ws ._⊩_
            ∃t : ∃[ t ∈ AssemblyMorphism ys ws ] (e ⊚ t ≡ q)
            ∃t = (do
                 (e⁻¹ , e⁻¹IsSection) ← choice X Y (xs .isSetX) (ys .isSetX) (e .map) surjection
                 return (h e⁻¹ e⁻¹IsSection , {!!})) where
                                 module _
                                  (e⁻¹ : Y → X)
                                  (e⁻¹IsSection : section (e .map) e⁻¹) where     
                                    h : AssemblyMorphism ys ws
                                    h .map y = q .map (e⁻¹ y)
                                    h .tracker = 
                                      do
                                        (q~ , q~tracks) ← q .tracker
                                        (r , rWitness) ← surjectionIsTracked
                                        return (s ⨾ (k ⨾ q~) ⨾ (s ⨾ (k ⨾ r) ⨾ Id) , (λ y b b⊩y → {!!}))

                                    e⊚h≡q : e ⊚ h ≡ q
                                    e⊚h≡q = AssemblyMorphism≡ _ _
                                            (funExt λ x → 
                                                      h .map (e .map x)
                                                        ≡⟨ refl ⟩
                                                      q .map (e⁻¹ (e .map x))
                                                        ≡⟨ {!(e⁻¹IsSection (e .map x))!} ⟩
                                                      q .map x
                                                        ∎)

                                    hy≡qx : ∀ x y → e .map x ≡ y → h .map y ≡ q .map x
                                    hy≡qx x y ex≡y =
                                       h .map y
                                        ≡⟨ refl ⟩
                                       q .map (e⁻¹ y)
                                        ≡⟨ {!e⁻¹IsSection (e .map x)!} ⟩
                                       q .map x
                                         ∎

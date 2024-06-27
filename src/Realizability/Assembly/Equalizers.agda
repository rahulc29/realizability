{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Realizability.CombinatoryAlgebra

module Realizability.Assembly.Equalizers {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca

module _ {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} (f g : AssemblyMorphism as bs) where
  _⊩A_ = as ._⊩_
  equalizer : Assembly (Σ[ a ∈ A ] f .map a ≡ g .map a)
  equalizer .isSetX = isSetΣ (as .isSetX) λ x → isProp→isSet (bs .isSetX (f .map x) (g .map x))
  equalizer ._⊩_ r (a , fa≡ga) = as ._⊩_ r a
  equalizer .⊩isPropValued r (a , fa≡ga) = as .⊩isPropValued r a
  equalizer .⊩surjective (a , fa≡ga) = as .⊩surjective a

  ιequalizer : AssemblyMorphism equalizer as
  ιequalizer .map (a , fa≡ga) = a
  ιequalizer .tracker = ∣ Id , (λ x aₓ aₓ⊩x → subst (λ y → y ⊩A (x .fst)) (sym (Ida≡a aₓ)) aₓ⊩x) ∣₁
                                                                                                 
  equalizerFactors : ((Z , zs) : Σ[ Z ∈ Type ℓ ] (Assembly Z))
                   → (ι' : AssemblyMorphism zs as)
                   → (ι' ⊚ f ≡ ι' ⊚ g)
                   → ∃![ ! ∈ AssemblyMorphism zs equalizer ] (! ⊚ ιequalizer ≡ ι')
  equalizerFactors (Z , zs) ι' ι'f≡ι'g =
                   uniqueExists (λ where
                                   .map z → ι' .map z , λ i → ι'f≡ι'g i .map z
                                   .tracker → ι' .tracker)
                                   (AssemblyMorphism≡ _ _ refl)
                                   (λ ! → isSetAssemblyMorphism _ _ (! ⊚ ιequalizer) ι')
                                   λ !' !'⊚ι≡ι' → AssemblyMorphism≡ _ _
                                                  (funExt λ z → Σ≡Prop (λ x → bs .isSetX (f .map x) (g .map x))
                                                          (λ i → !'⊚ι≡ι' (~ i) .map z))


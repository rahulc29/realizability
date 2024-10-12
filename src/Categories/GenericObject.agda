open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Categories.CartesianMorphism

module Categories.GenericObject where

module _
  {ℓB ℓ'B ℓE ℓ'E}
  {B : Category ℓB ℓ'B}
  (E : Categoryᴰ B ℓE ℓ'E) where

  open Category B
  open Categoryᴰ E
  open Contravariant E

  record GenericObject : Type (ℓ-max (ℓ-max ℓB ℓ'B) (ℓ-max ℓE ℓ'E)) where
    constructor makeGenericObject
    field
      base : ob
      displayed : ob[ base ]
      isGeneric :
        ∀ {t : ob} (tᴰ : ob[ t ])
        → Σ[ f ∈ Hom[ t , base ] ] Σ[ fᴰ ∈ Hom[ f ][ tᴰ , displayed ] ] isCartesian f fᴰ

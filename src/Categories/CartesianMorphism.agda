open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation

module Categories.CartesianMorphism where

module Contravariant
  {ℓB ℓ'B ℓE ℓ'E}
  {B : Category ℓB ℓ'B}
  (E : Categoryᴰ B ℓE ℓ'E) where

  open Category B
  open Categoryᴰ E

  opaque
    isCartesian :
      {a b : ob} (f : B [ a , b ])
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      (fᴰ : Hom[ f ][ aᴰ , bᴰ ]) →
      Type (ℓ-max (ℓ-max ℓB ℓ'B) (ℓ-max ℓE ℓ'E))
    isCartesian {a} {b} f {aᴰ} {bᴰ} fᴰ =
      ∀ {c : ob} {cᴰ : ob[ c ]} (g : B [ c , a ]) → isEquiv λ (gᴰ : Hom[ g ][ cᴰ , aᴰ ]) → gᴰ ⋆ᴰ fᴰ

  opaque
    unfolding isCartesian
    isPropIsCartesian :
      {a b : ob} (f : B [ a , b ])
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      (fᴰ : Hom[ f ][ aᴰ , bᴰ ]) →
      isProp (isCartesian f fᴰ)
    isPropIsCartesian f fᴰ = isPropImplicitΠ2 λ c cᴰ → isPropΠ λ g → isPropIsEquiv (_⋆ᴰ fᴰ)

  opaque
    isCartesian' :
      {a b : ob} (f : B [ a , b ])
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      (fᴰ : Hom[ f ][ aᴰ , bᴰ ]) →
      Type (ℓ-max (ℓ-max ℓB ℓ'B) (ℓ-max ℓE ℓ'E))
    isCartesian' {a} {b} f {aᴰ} {bᴰ} fᴰ =
      ∀ {c : ob} {cᴰ : ob[ c ]} (g : B [ c , a ]) →
        (∀ (hᴰ : Hom[ g ⋆ f ][ cᴰ , bᴰ ]) → ∃![ gᴰ ∈ Hom[ g ][ cᴰ , aᴰ ] ] gᴰ ⋆ᴰ fᴰ ≡ hᴰ)

  opaque
    unfolding isCartesian'
    isPropIsCartesian' :
      {a b : ob} {f : B [ a , b ]}
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      (fᴰ : Hom[ f ][ aᴰ , bᴰ ]) →
      isProp (isCartesian' f fᴰ)
    isPropIsCartesian' {a} {b} {f} {aᴰ} {bᴰ} fᴰ =
      isPropImplicitΠ2 λ c cᴰ → isPropΠ2 λ g hᴰ → isPropIsContr

  opaque
    unfolding isCartesian
    unfolding isCartesian'
    isCartesian→isCartesian' :
      {a b : ob} (f : B [ a , b ])
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      (fᴰ : Hom[ f ][ aᴰ , bᴰ ]) →
      isCartesian f fᴰ →
      isCartesian' f fᴰ
    isCartesian→isCartesian' {a} {b} f {aᴰ} {bᴰ} fᴰ cartfᴰ g hᴰ =
      ((invIsEq (cartfᴰ g) hᴰ) , (secIsEq (cartfᴰ g) hᴰ)) ,
      (λ { (gᴰ , gᴰ⋆fᴰ≡hᴰ) → cartfᴰ g .equiv-proof hᴰ .snd (gᴰ , gᴰ⋆fᴰ≡hᴰ) })

  opaque
    unfolding isCartesian
    unfolding isCartesian'
    isCartesian'→isCartesian :
      {a b : ob} (f : B [ a , b ])
      {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
      (fᴰ : Hom[ f ][ aᴰ , bᴰ ]) →
      isCartesian' f fᴰ →
      isCartesian f fᴰ
    equiv-proof (isCartesian'→isCartesian {a} {b} f {aᴰ} {bᴰ} fᴰ cart'fᴰ g) hᴰ = (cart'fᴰ g hᴰ .fst) , (cart'fᴰ g hᴰ .snd)

  isCartesian≃isCartesian' :
    {a b : ob} (f : B [ a , b ])
    {aᴰ : ob[ a ]} {bᴰ : ob[ b ]}
    (fᴰ : Hom[ f ][ aᴰ , bᴰ ]) →
    isCartesian f fᴰ ≃ isCartesian' f fᴰ
  isCartesian≃isCartesian' {a} {b} f {aᴰ} {bᴰ} fᴰ =
    propBiimpl→Equiv (isPropIsCartesian f fᴰ) (isPropIsCartesian' fᴰ) (isCartesian→isCartesian' f fᴰ) (isCartesian'→isCartesian f fᴰ)

  cartesianLift : {a b : ob} (f : B [ a , b ]) (bᴰ : ob[ b ]) → Type _
  cartesianLift {a} {b} f bᴰ = Σ[ aᴰ ∈ ob[ a ] ] Σ[ fᴰ ∈ Hom[ f ][ aᴰ , bᴰ ] ] isCartesian f fᴰ

  isCartesianFibration : Type _
  isCartesianFibration =
    ∀ {a b : ob} {bᴰ : ob[ b ]}
    → (f : Hom[ a , b ])
    → ∥ cartesianLift f bᴰ ∥₁

  isPropIsCartesianFibration : isProp isCartesianFibration
  isPropIsCartesianFibration = isPropImplicitΠ3 λ a b bᴰ → isPropΠ λ f → isPropPropTrunc

  cleavage : Type _
  cleavage = {a b : ob} (f : Hom[ a , b ]) (bᴰ : ob[ b ]) → cartesianLift f bᴰ

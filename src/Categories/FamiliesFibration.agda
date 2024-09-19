open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.Sets
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Categories.CartesianMorphism
open import Categories.GenericObject
module Categories.FamiliesFibration where

module FamiliesFibration
  {ℓ ℓ'}
  (C : Category ℓ ℓ')
  (ℓ'' : Level) where
  open Category C
  Families : Categoryᴰ (SET ℓ'') (ℓ-max ℓ ℓ'') (ℓ-max ℓ' ℓ'')
  Categoryᴰ.ob[ Families ] (I , isSetI) = I → ob
  Categoryᴰ.Hom[_][_,_] Families {I , isSetI} {J , isSetJ} u X Y = (i : I) → Hom[ X i , Y (u i) ]
  Categoryᴰ.idᴰ Families {I , isSetI} {X} i = id
  Categoryᴰ._⋆ᴰ_ Families {I , isSetI} {J , isSetJ} {K , isSetK} {f} {g} {X} {Y} {Z} fᴰ gᴰ i =
    fᴰ i ⋆ gᴰ (f i)
  Categoryᴰ.⋆IdLᴰ Families {I , isSetI} {J , isSetJ} {f} {X} {Y} fᴰ =
    funExt λ i → ⋆IdL (fᴰ i)
  Categoryᴰ.⋆IdRᴰ Families {I , isSetI} {J , isSetJ} {f} {X} {Y} fᴰ =
    funExt λ i → ⋆IdR (fᴰ i)
  Categoryᴰ.⋆Assocᴰ Families {I , isSetI} {J , isSetJ} {K , isSetK} {L , isSetL} {f} {g} {h} {X} {Y} {Z} {W} fᴰ gᴰ hᴰ =
    funExt λ i → ⋆Assoc (fᴰ i) (gᴰ (f i)) (hᴰ (g (f i)))
  Categoryᴰ.isSetHomᴰ Families {I , isSetI} {J , isSetJ} {f} {X} {Y} = isSetΠ λ i → isSetHom

  open Contravariant Families
  open Categoryᴰ Families
  cleavageFamilies : cleavage
  cleavageFamilies a@{I , isSetI} b@{J , isSetJ} f Y =
    X ,
    fᴰ ,
    cart where

      X : I → ob
      X i = Y (f i)

      fᴰ : (i : I) → Hom[ X i , Y (f i) ]
      fᴰ i = id

      opaque
        unfolding isCartesian'
        cart' : isCartesian' {a = a} {b = b} f {bᴰ = Y} fᴰ
        cart' k@{K , isSetK} {Z} g hᴰ =
          (hᴰ , (funExt (λ k → ⋆IdR (hᴰ k)))) ,
          λ { (! , !comm) →
            Σ≡Prop
              (λ ! → isSetHomᴰ {x = k} {y = b} {xᴰ = Z} {yᴰ = Y} (λ k → ! k ⋆ fᴰ (g k)) hᴰ)
              (funExt
                (λ k →
                  sym
                    (! k
                      ≡⟨ sym (⋆IdR (! k)) ⟩
                    (! k ⋆ fᴰ (g k))
                      ≡[ i ]⟨ !comm i k ⟩
                    hᴰ k
                      ∎))) }

      cart : isCartesian {a = a} {b = b} f {bᴰ = Y} fᴰ
      cart = isCartesian'→isCartesian {a = a} {b = b} f {bᴰ = Y} fᴰ cart'

module GenericFamily
  {ℓ ℓ'}
  (C : Category ℓ ℓ')
  (isSetCOb : isSet (C .Category.ob)) where

  open FamiliesFibration C ℓ
  open Category C
  open Categoryᴰ Families
  open Contravariant Families
  genericFamily : GenericObject Families
  GenericObject.base genericFamily = ob , isSetCOb
  GenericObject.displayed genericFamily = λ x → x
  GenericObject.isGeneric genericFamily i@{I , isSetI} X =
    f ,
    fᴰ ,
    cart where
      f : I → ob
      f = X

      fᴰ : Hom[_][_,_] {x = i} {y = ob , isSetCOb} f X (λ x → x)
      fᴰ i = id

      opaque
        unfolding isCartesian'
        cart' : isCartesian' {a = i} {b = ob , isSetCOb} f {bᴰ = λ x → x} fᴰ
        cart' {J , isSetJ} {Z} g hᴰ =
          (hᴰ , funExt λ j → ⋆IdR (hᴰ j)) ,
          λ { (! , !comm) →
            Σ≡Prop
              (λ ! → isSetHomᴰ {x = J , isSetJ} {y = i} {f = g} {xᴰ = Z} {yᴰ = f} (λ j → ! j ⋆ fᴰ (g j)) hᴰ)
              (funExt
                λ j →
                  sym
                    (! j
                      ≡⟨ sym (⋆IdR (! j)) ⟩
                    ! j ⋆ fᴰ (g j)
                      ≡[ i ]⟨ !comm i j ⟩
                    hᴰ j
                      ∎)) }

      cart : isCartesian {a = i} {b = ob , isSetCOb} f {bᴰ = λ x → x} fᴰ
      cart = isCartesian'→isCartesian f fᴰ cart'

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Realizability.CombinatoryAlgebra

module Realizability.Assembly.SIP {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca

module _ {X : Type ℓ} where

  Assembly≡Iso : ∀ (asmA asmB : Assembly X) → Iso (asmA ≡ asmB) (∀ r x → r ⊩[ asmA ] x ≡ r ⊩[ asmB ] x)
  Iso.fun (Assembly≡Iso asmA asmB) path r x i = r ⊩[ path i ] x
  Assembly._⊩_ (Iso.inv (Assembly≡Iso asmA asmB) pointwisePath i) r x = pointwisePath r x i
  Assembly.isSetX (Iso.inv (Assembly≡Iso asmA asmB) pointwisePath i) = isPropIsSet {A = X} (asmA .isSetX) (asmB .isSetX) i
  Assembly.⊩isPropValued (Iso.inv (Assembly≡Iso asmA asmB) pointwisePath i) r x = isProp→PathP {B = λ j → isProp (pointwisePath r x j)} (λ j → isPropIsProp) (asmA .⊩isPropValued r x) (asmB .⊩isPropValued r x) i
  Assembly.⊩surjective (Iso.inv (Assembly≡Iso asmA asmB) pointwisePath i) x = isProp→PathP {B = λ j → ∃[ a ∈ A ] (pointwisePath a x j)} (λ j → isPropPropTrunc) (asmA .⊩surjective x) (asmB .⊩surjective x) i
  Iso.rightInv (Assembly≡Iso asmA asmB) pointwise = funExt₂ λ r x → refl
  Iso.leftInv (Assembly≡Iso asmA asmB) path = isSetAssembly X asmA asmB _ _

  Assembly≡Equiv : ∀ (asmA asmB : Assembly X) → (asmA ≡ asmB) ≃ (∀ r x → r ⊩[ asmA ] x ≡ r ⊩[ asmB ] x)
  Assembly≡Equiv asmA asmB = isoToEquiv (Assembly≡Iso asmA asmB)

  Assembly≡ : ∀ (asmA asmB : Assembly X) → (∀ r x → r ⊩[ asmA ] x ≡ r ⊩[ asmB ] x) → (asmA ≡ asmB)
  Assembly≡ asmA asmB pointwise = Iso.inv (Assembly≡Iso asmA asmB) pointwise

{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Reflection.RecordEquiv
open import Realizability.CombinatoryAlgebra

module Realizability.Assembly.Base {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
  record Assembly (X : Type ℓ) : Type (ℓ-suc ℓ) where
    constructor makeAssembly
    infix 25 _⊩_
    field
      _⊩_ : A → X → Type ℓ
      isSetX : isSet X
      ⊩isPropValued : ∀ a x → isProp (a ⊩ x)
      ⊩surjective : ∀ x → ∃[ a ∈ A ] a ⊩ x

  open Assembly public
  _⊩[_]_ : ∀ {X : Type ℓ} → A → Assembly X → X → Type ℓ
  a ⊩[ A ] x = A ._⊩_ a x

  AssemblyΣ : Type ℓ → Type _
  AssemblyΣ X =
    Σ[ _⊩_ ∈ (A → X → hProp ℓ) ]
    (∀ x → ∃[ a ∈ A ] ⟨ a ⊩ x ⟩) ×
    (isSet X)

  isSetAssemblyΣ : ∀ X → isSet (AssemblyΣ X)
  isSetAssemblyΣ X = isSetΣ (isSetΠ2 λ _ _ → isSetHProp) (λ rel → isSet× (isSetΠ λ x → isProp→isSet isPropPropTrunc) (isProp→isSet isPropIsSet))
  
  AssemblyΣ≡Equiv : ∀ X → (a b : AssemblyΣ X) → (a ≡ b) ≃ (∀ r x → ⟨ a .fst r x ⟩ ≃ ⟨ b .fst r x ⟩)
  AssemblyΣ≡Equiv X a b =
    a ≡ b
      ≃⟨ invEquiv (Σ≡PropEquiv (λ rel → isProp× (isPropΠ λ x → isPropPropTrunc) isPropIsSet) {u = a} {v = b}) ⟩
    a .fst ≡ b .fst
      ≃⟨ invEquiv (funExt₂Equiv {f = a .fst} {g = b .fst}) ⟩
    (∀ (r : A) (x : X) → a .fst r x ≡ b .fst r x)
      ≃⟨
        equivΠCod
          (λ r →
            equivΠCod
              λ x →
                compEquiv
                  (invEquiv (Σ≡PropEquiv (λ _ → isPropIsProp) {u = a .fst r x} {v = b .fst r x}))
                  (univalence {A = a .fst r x .fst} {B = b .fst r x .fst}))
       ⟩
    (∀ (r : A) (x : X) → ⟨ a .fst r x ⟩ ≃ ⟨ b .fst r x ⟩)
      ■

  -- definitional isomorphism
  AssemblyΣIsoAssembly : ∀ X → Iso (AssemblyΣ X) (Assembly X)
  _⊩_ (Iso.fun (AssemblyΣIsoAssembly X) (rel , surj , isSetX)) a x = ⟨ rel a x ⟩
  Assembly.isSetX (Iso.fun (AssemblyΣIsoAssembly X) (rel , surj , isSetX)) = isSetX
  ⊩isPropValued (Iso.fun (AssemblyΣIsoAssembly X) (rel , surj , isSetX)) a x = str (rel a x)
  ⊩surjective (Iso.fun (AssemblyΣIsoAssembly X) (rel , surj , isSetX)) x = surj x
  Iso.inv (AssemblyΣIsoAssembly X) asm = (λ a x → (a ⊩[ asm ] x) , (asm .⊩isPropValued a x)) , (λ x → asm .⊩surjective x) , asm .isSetX
  Iso.rightInv (AssemblyΣIsoAssembly X) asm = refl
  Iso.leftInv (AssemblyΣIsoAssembly X) (rel , surj , isSetX) = refl

  AssemblyΣ≃Assembly : ∀ X → AssemblyΣ X ≃ Assembly X
  AssemblyΣ≃Assembly X = isoToEquiv (AssemblyΣIsoAssembly X)

  isSetAssembly : ∀ X → isSet (Assembly X)
  isSetAssembly X = isOfHLevelRespectEquiv 2 (AssemblyΣ≃Assembly X) (isSetAssemblyΣ X)

module Tripoi.HeytingAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Algebra.Lattice

private
  variable
    ℓ ℓ' : Level
record IsHeytingAlgebra {H : Type ℓ} (0l 1l : H) (_∨l_  _∧l_ _→l_ : H → H → H) : Type ℓ where
  field
    isSetH : isSet H
    lattice : IsLattice 0l 1l _∨l_ _∧l_
  open IsLattice lattice public
  _≤_ : H → H → Type ℓ
  x ≤ y = x ∨l y ≡ y

  _≤'_ : H → H → Type ℓ
  x ≤' y = x ∧l y ≡ x

  ≤→≤' : ∀ x y → x ≤ y → x ≤' y
  ≤→≤' x y x≤y =
    x ∧l y
      ≡⟨ cong (λ y → x ∧l y) (sym x≤y) ⟩
    x ∧l (x ∨l y)
      ≡⟨ absorb x y .snd ⟩
    x
      ∎

  ≤'→≤ : ∀ x y → x ≤' y → x ≤ y
  ≤'→≤ x y x≤'y =
     x ∨l y
       ≡⟨ cong (λ x → x ∨l y) (sym x≤'y) ⟩
     (x ∧l y) ∨l y
       ≡⟨ ∨lComm _ _ ⟩
     y ∨l (x ∧l y)
       ≡⟨ cong (λ x → y ∨l x) (∧lComm _ _) ⟩
     y ∨l (y ∧l x)
       ≡⟨ absorb y x .fst ⟩
     y
       ∎

  ≤≡≤' : ∀ x y → x ≤ y ≡ x ≤' y
  ≤≡≤' x y = hPropExt (isSetH _ _) (isSetH _ _) (≤→≤' x y) (≤'→≤ x y)

  isRefl≤ : ∀ h → h ≤ h
  isRefl≤ h = ∨lIdem h

  isAntiSym≤ : ∀ x y → x ≤ y → y ≤ x → x ≡ y
  isAntiSym≤ x y x≤y y≤x =
    x
       ≡⟨ sym y≤x ⟩
     y ∨l x
       ≡⟨ ∨lComm y x ⟩
     x ∨l y
       ≡⟨ x≤y ⟩
     y ∎

  isTrans≤ : ∀ x y z → x ≤ y → y ≤ z → x ≤ z
  isTrans≤ x y z x≤y y≤z =
     x ∨l z
       ≡⟨ cong (λ z → x ∨l z) (sym y≤z) ⟩
     x ∨l (y ∨l z)
       ≡⟨ ∨lAssoc x y z ⟩
     (x ∨l y) ∨l z
       ≡⟨ cong (λ y → y ∨l z) x≤y ⟩
     y ∨l z
       ≡⟨ y≤z ⟩
     z
       ∎

  isBottom0l : ∀ x → 0l ≤ x
  isBottom0l x = ∨lLid x

  isTop1l : ∀ x → x ≤ 1l
  isTop1l x = ≤'→≤ x 1l (∧lRid x)

  -- Heyting implication

  field
    →isHeytingImplication : ∀ x y z → (x ∧l y) ≤ z → x ≤ (y →l z)
    
record HeytingAlgebraStr (A : Type ℓ) : Type ℓ where
  field
    0l : A
    1l : A
    _∨l_ : A → A → A
    _∧l_ : A → A → A
    _→l_ : A → A → A
    isHeytingAlgebra : IsHeytingAlgebra 0l 1l _∨l_ _∧l_ _→l_

record IsHeytingAlgebraHom {A : Type ℓ} {B : Type ℓ'} (strA : HeytingAlgebraStr A) (f : A → B) (strB : HeytingAlgebraStr B) : Type (ℓ-max ℓ ℓ') where
  private
    module A = HeytingAlgebraStr strA
    module B = HeytingAlgebraStr strB
  field
    pres0 : f A.0l ≡ B.0l
    pres1 : f A.1l ≡ B.1l
    pres∨l : ∀ x y → f (x A.∨l y) ≡ (f x B.∨l f y)
    pres∧l : ∀ x y → f (x A.∧l y) ≡ (f x B.∧l f y)
    pres→l : ∀ x y → f (x A.→l y) ≡ (f x B.→l f y)

{-# OPTIONS --cubical #-}
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.Categories.Category

module Realizability.Assembly.Path {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca

private
  variable
    X Y : Type ℓ

open isIso

CatIsoToPath : ∀ {x y} → (CatIso ASM x y) → (x ≡ y)
CatIsoToPath {X , xs} {Y , ys} x∼y = ΣPathP (P , λ i → record
                                                         { isSetX = isSetOverP i
                                                         ; _⊩_ = ⊩overP i
                                                         ; ⊩isPropValued = ⊩isPropValuedOverP i
                                                         ; ⊩surjective = ⊩surjectiveOverP i }) where
  f = x∼y .fst .map
  g = x∼y .snd .inv .map
  sect = x∼y .snd .sec
  retr = x∼y .snd .ret
  f~ = x∼y .fst .tracker
  g~ = x∼y .snd .inv .tracker

  _⊩X_ = xs ._⊩_
  _⊩Y_ = ys ._⊩_
  
  P = isoToPath (iso f g (λ b i → sect i .map b) λ a i → retr i .map a)
  
  isSetOverP : PathP (λ i → isSet (P i)) (xs .isSetX) (ys .isSetX)
  isSetOverP i = isProp→PathP {B = λ i → isSet (P i)} (λ i → isPropIsSet) (xs .isSetX) (ys .isSetX) i
  
  ⊩overP : PathP (λ i → (∀ (a : A) (p : (P i)) → Type ℓ)) (xs ._⊩_) (ys ._⊩_)
  ⊩overP =
    funExtDep
      {A = λ i → A}
      {B = λ i a → ((P i) → Type ℓ)}
      {f = xs ._⊩_}
      {g = ys ._⊩_}
      λ {xᵣ yᵣ} (p : xᵣ ≡ yᵣ) →
        funExtDep
          {A = λ i → P i}
          {B = λ i p' → Type ℓ}
          {f = xs ._⊩_ xᵣ}
          {g = ys ._⊩_ yᵣ}
          λ {x y} p' → hPropExt {A = xᵣ ⊩X x} {B = yᵣ ⊩Y y} (xs .⊩isPropValued xᵣ x) (ys .⊩isPropValued yᵣ y) (λ xᵣ⊩x → {!!}) λ yᵣ⊩y → {!!}
  
  ⊩isPropValuedOverP : PathP (λ i → ∀ (a : A) (p : P i) → isProp (⊩overP i a p)) (xs .⊩isPropValued) (ys .⊩isPropValued)
  ⊩isPropValuedOverP =
    funExtDep
      {A = λ i → A}
      {B = λ i a → ∀ (p : P i) → isProp (⊩overP i a p)}
      {f = xs .⊩isPropValued}
      {g = ys .⊩isPropValued}
      λ {xᵣ yᵣ} (p : xᵣ ≡ yᵣ) →
        funExtDep
          {A = λ i → P i}
          {B = λ i p' → isProp (⊩overP i (p i) p')}
          {f = xs .⊩isPropValued xᵣ}
          {g = ys .⊩isPropValued yᵣ}
          λ {x y} p' →
            isProp→PathP
              {B = λ i → isProp (⊩overP i (p i) (p' i))}
              (λ i → isPropIsProp)
              (xs .⊩isPropValued xᵣ x)
              (ys .⊩isPropValued yᵣ y)
  
  ⊩surjectiveDependency = (λ i → ∀ (p : P i) → ∃[ a ∈ A ] ⊩overP i a p)
  ⊩surjectiveOverP : PathP ⊩surjectiveDependency (xs .⊩surjective) (ys .⊩surjective)
  ⊩surjectiveOverP =
    funExtDep
      {A = λ i → P i}
      {B = λ i p → ∃[ a ∈ A ] ⊩overP i a p}
      {f = xs .⊩surjective}
      {g = ys .⊩surjective}
      λ {x y} p →
        isProp→PathP
          {B = λ i → ∃[ a ∈ A ] ⊩overP i a (p i)}
          (λ i → isPropPropTrunc)
          (xs .⊩surjective x)
          (ys .⊩surjective y)

IsoPathCatIsoASM : ∀ {x y} → Iso (x ≡ y) (CatIso ASM x y)
IsoPathCatIsoASM {x} {y} = iso pathToIso CatIsoToPath {!!} {!!}

-- Conjecture : ASM is univalent
isUnivalentASM : isUnivalent ASM
isUnivalentASM = record { univ = λ x y → isoToEquiv IsoPathCatIsoASM .snd }

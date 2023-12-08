{-# OPTIONS --cubical #-}
open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
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
  P = isoToPath (iso f g (λ b i → sect i .map b) λ a i → retr i .map a)
  isSetOverP : PathP (λ i → isSet (P i)) (xs .isSetX) (ys .isSetX)
  isSetOverP = {!!}
  ⊩overP : PathP (λ i → (∀ (a : A) (p : (P i)) → Type ℓ)) (xs ._⊩_) (ys ._⊩_)
  ⊩overP = {!!}
  ⊩isPropValuedOverP : PathP (λ i → ∀ (a : A) (p : P i) → isProp (⊩overP i a p)) (xs .⊩isPropValued) (ys .⊩isPropValued)
  ⊩isPropValuedOverP = {!!}
  ⊩surjectiveOverP : PathP (λ i → ∀ (p : P i) → ∃[ a ∈ A ] ⊩overP i a p) (xs .⊩surjective) (ys .⊩surjective)
  ⊩surjectiveOverP = {!!}

IsoPathCatIsoASM : ∀ {x y} → Iso (x ≡ y) (CatIso ASM x y)
IsoPathCatIsoASM {x} {y} = iso pathToIso CatIsoToPath {!!} {!!}

isUnivalentASM : isUnivalent ASM
isUnivalentASM = record { univ = λ x y → isoToEquiv IsoPathCatIsoASM .snd }

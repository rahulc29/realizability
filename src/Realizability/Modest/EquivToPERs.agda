open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Functor hiding (Id)
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.Equivalence
open import Cubical.Categories.NaturalTransformation
open import Categories.CartesianMorphism
open import Categories.GenericObject
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure
open import Realizability.PropResizing

module Realizability.Modest.EquivToPERs {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Terminal ca
open import Realizability.Assembly.SetsReflectiveSubcategory ca
open import Realizability.Modest.Base ca
open import Realizability.Modest.UniformFamily ca
open import Realizability.Modest.CanonicalPER ca
open import Realizability.Modest.SubQuotientCanonicalPERIso ca
open import Realizability.PERs.PER ca
open import Realizability.PERs.SubQuotient ca

open Assembly
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Contravariant UNIMOD
open UniformFamily
open DisplayedUFamMap

CanonicalPERWeakInverseOfSubQuotient : WeakInverse subQuotientFunctor
WeakInverse.invFunc CanonicalPERWeakInverseOfSubQuotient = CanonicalPERFunctor
NatTrans.N-ob (NatIso.trans (WeakInverse.η CanonicalPERWeakInverseOfSubQuotient)) R = [ Id , isTrackerId ] where
  isTrackerId : isTracker R (canonicalPER (subQuotientAssembly R) (isModestSubQuotientAssembly R)) Id
  isTrackerId r r' r~r' =
    subst2
      _~[ canonicalPER (subQuotientAssembly R) (isModestSubQuotientAssembly R) ]_
      (sym (Ida≡a r))
      (sym (Ida≡a r'))
      ([ r , r~r ] , (r~r , PER.isSymmetric R r r' r~r')) where
    r~r : r ~[ R ] r
    r~r = PER.isTransitive R r r' r r~r' (PER.isSymmetric R r r' r~r')
NatTrans.N-hom (NatIso.trans (WeakInverse.η CanonicalPERWeakInverseOfSubQuotient)) {R} {S} f = {!!}
isIso.inv (NatIso.nIso (WeakInverse.η CanonicalPERWeakInverseOfSubQuotient) R) = {!!}
isIso.sec (NatIso.nIso (WeakInverse.η CanonicalPERWeakInverseOfSubQuotient) R) = {!!}
isIso.ret (NatIso.nIso (WeakInverse.η CanonicalPERWeakInverseOfSubQuotient) R) = {!!}
NatTrans.N-ob (NatIso.trans (WeakInverse.ε CanonicalPERWeakInverseOfSubQuotient)) (X , asmX , isModestAsmX)= {!invert asmX isModestAsmX!}
NatTrans.N-hom (NatIso.trans (WeakInverse.ε CanonicalPERWeakInverseOfSubQuotient)) {X , asmX , isModestAsmX} {Y , asmY , isModestAsmY} f = {!forward!}
isIso.inv (NatIso.nIso (WeakInverse.ε CanonicalPERWeakInverseOfSubQuotient) (X , asmX , isModestAsmX)) = {!!}
isIso.sec (NatIso.nIso (WeakInverse.ε CanonicalPERWeakInverseOfSubQuotient) (X , asmX , isModestAsmX)) = {!!}
isIso.ret (NatIso.nIso (WeakInverse.ε CanonicalPERWeakInverseOfSubQuotient) (X , asmX , isModestAsmX)) = {!!}

isEquivalenceSubQuotient : isEquivalence subQuotientFunctor
isEquivalenceSubQuotient = ∣ CanonicalPERWeakInverseOfSubQuotient ∣₁

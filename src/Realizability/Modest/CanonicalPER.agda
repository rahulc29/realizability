{-# OPTIONS --allow-unsolved-metas #-}
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
open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Functor hiding (Id)
open import Cubical.Categories.Constructions.Slice
open import Categories.CartesianMorphism
open import Categories.GenericObject
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure
open import Realizability.PropResizing

module Realizability.Modest.CanonicalPER {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Terminal ca
open import Realizability.Assembly.SetsReflectiveSubcategory ca
open import Realizability.Modest.Base ca
open import Realizability.Modest.UniformFamily ca
open import Realizability.PERs.PER ca
open import Realizability.PERs.SubQuotient ca

open Assembly
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Contravariant UNIMOD
open UniformFamily
open DisplayedUFamMap

module _
  {X : Type ℓ}
  (asmX : Assembly X)
  (isModestAsmX : isModest asmX) where

  canonicalPER : PER
  PER.relation canonicalPER a b = Σ[ x ∈ X ] a ⊩[ asmX ] x × b ⊩[ asmX ] x
  PER.isPropValued canonicalPER a b (x , a⊩x , b⊩x) (x' , a⊩x' , b⊩x') =
    Σ≡Prop
      (λ x → isProp× (asmX .⊩isPropValued a x) (asmX .⊩isPropValued b x))
      (isModestAsmX x x' a a⊩x a⊩x')
  fst (PER.isPER canonicalPER) a b (x , a⊩x , b⊩x) = x , b⊩x , a⊩x
  snd (PER.isPER canonicalPER) a b c (x , a⊩x , b⊩x) (x' , b⊩x' , c⊩x') =
    x' , subst (a ⊩[ asmX ]_) (isModestAsmX x x' b b⊩x b⊩x') a⊩x , c⊩x'

CanonicalPERFunctor : Functor MOD PERCat
Functor.F-ob CanonicalPERFunctor (X , asmX , isModestAsmX) = canonicalPER asmX isModestAsmX
Functor.F-hom CanonicalPERFunctor {X , asmX , isModestAsmX} {Y , asmY , isModestAsmY} f = {!!}
Functor.F-id CanonicalPERFunctor = {!!}
Functor.F-seq CanonicalPERFunctor = {!!}

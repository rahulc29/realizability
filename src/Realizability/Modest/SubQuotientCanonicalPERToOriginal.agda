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
open import Categories.CartesianMorphism
open import Categories.GenericObject
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure
open import Realizability.PropResizing

module Realizability.Modest.SubQuotientCanonicalPERToOriginal {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Terminal ca
open import Realizability.Assembly.SetsReflectiveSubcategory ca
open import Realizability.Modest.Base ca
open import Realizability.Modest.UniformFamily ca
open import Realizability.Modest.CanonicalPER ca
open import Realizability.PERs.PER ca
open import Realizability.PERs.SubQuotient ca

open Assembly
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Contravariant UNIMOD
open UniformFamily
open DisplayedUFamMap

module
  _ {X : Type ℓ}
  (asmX : Assembly X)
  (isModestAsmX : isModest asmX) where

  theCanonicalPER : PER
  theCanonicalPER = canonicalPER asmX isModestAsmX

  theSubQuotient : Assembly (subQuotient theCanonicalPER)
  theSubQuotient = subQuotientAssembly theCanonicalPER

  invert : AssemblyMorphism theSubQuotient asmX
  AssemblyMorphism.map invert sq = SQ.rec (asmX .isSetX) mainMap mainMapCoh sq where

    mainMap : Σ[ a ∈ A ] (theCanonicalPER .PER.relation a a) → X
    mainMap (a , a~a) = PT.rec→Set (asmX .isSetX) action 2ConstantAction a~a where
      action : Σ[ x ∈ X ] ((a ⊩[ asmX ] x) × (a ⊩[ asmX ] x)) → X
      action (x , _ , _) = x

      2ConstantAction : 2-Constant action
      2ConstantAction (x , a⊩x , _) (x' , a⊩x' , _) = isModestAsmX x x' a a⊩x a⊩x'

    mainMapCoh : ∀ a b a~b → mainMap a ≡ mainMap b
    mainMapCoh (a , a~a) (b , b~b) a~b =
      PT.elim3
        {P = λ a~a b~b a~b → mainMap (a , a~a) ≡ mainMap (b , b~b)}
        (λ _ _ _ → asmX .isSetX _ _)
        (λ { (x , a⊩x , _) (x' , b⊩x' , _) (x'' , a⊩x'' , b⊩x'') →
          {!isModestAsmX x x' !} })
        a~a
        b~b
        a~b
  AssemblyMorphism.tracker invert = {!!}

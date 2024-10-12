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
  AssemblyMorphism.map invert sq = SQ.rec (asmX .isSetX) reprAction reprActionCoh sq module Invert where

    reprAction : Σ[ a ∈ A ] (a ~[ theCanonicalPER ] a) → X
    reprAction (a , x , a⊩x , _) = x

    reprActionCoh : ∀ a b a~b → reprAction a ≡ reprAction b
    reprActionCoh (a , x , a⊩x , _) (b , x' , b⊩x' , _) (x'' , a⊩x'' , b⊩x'') =
      x
        ≡⟨ isModestAsmX x x'' a a⊩x a⊩x'' ⟩
      x''
        ≡⟨ isModestAsmX x'' x' b b⊩x'' b⊩x' ⟩
      x'
        ∎
  AssemblyMorphism.tracker invert = return (Id , (λ sq a a⊩sq → goal sq a a⊩sq)) where
    realizability : (sq : subQuotient theCanonicalPER) → (a : A) → a ⊩[ theSubQuotient ] sq → a ⊩[ asmX ] (invert .map sq)
    realizability sq a a⊩sq =
      SQ.elimProp
        {P = motive}
        isPropMotive
        elemMotive
        sq a a⊩sq where

      motive : (sq : subQuotient theCanonicalPER) → Type _
      motive sq = ∀ (a : A) → a ⊩[ theSubQuotient ] sq → a ⊩[ asmX ] (invert .map sq)

      isPropMotive : ∀ sq → isProp (motive sq)
      isPropMotive sq = isPropΠ2 λ a a⊩sq → asmX .⊩isPropValued _ _

      elemMotive : (x : domain theCanonicalPER) → motive [ x ]
      elemMotive (r , x , r⊩x , _) a (x' , a⊩x' , r⊩x') = subst (a ⊩[ asmX ]_) (isModestAsmX x' x r r⊩x' r⊩x) a⊩x'

    goal : (sq : subQuotient theCanonicalPER) → (a : A) → a ⊩[ theSubQuotient ] sq → (Id ⨾ a) ⊩[ asmX ] (invert .map sq)
    goal sq a a⊩sq = subst (_⊩[ asmX ] _) (sym (Ida≡a a)) (realizability sq a a⊩sq)


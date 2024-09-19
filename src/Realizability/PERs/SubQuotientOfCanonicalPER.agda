open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Path
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv
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

module Realizability.PERs.SubQuotientOfCanonicalPER {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Terminal ca
open import Realizability.Assembly.SetsReflectiveSubcategory ca
open import Realizability.Modest.Base ca
open import Realizability.Modest.UniformFamily ca
open import Realizability.Modest.CanonicalPER ca
open import Realizability.PERs.PER ca
open import Realizability.PERs.SubQuotient ca

module _ (per : PER) where

  theCanonicalPER : PER
  theCanonicalPER = canonicalPER (subQuotientAssembly per) (isModestSubQuotientAssembly per)

  opaque
    canonicalPEROfSubQuotientIsId : theCanonicalPER ≡ per
    canonicalPEROfSubQuotientIsId =
      PER≡ _ _
        (funExt₂ pointwise) where
        opaque
          effectiveness : (x : subQuotient per) (a b : A) → a ⊩[ subQuotientAssembly per ] x → b ⊩[ subQuotientAssembly per ] x → per .PER.relation a b
          effectiveness x a b a⊩x b⊩x = {!!}
          
        opaque
          dir1 : ∀ a b → theCanonicalPER .PER.relation a b → per .PER.relation a b
          dir1 a b ∃x =
            equivFun
              (propTruncIdempotent≃ (per .PER.isPropValued a b))
              (do
                (x , a⊩x , b⊩x) ← ∃x
                return (effectiveness x a b a⊩x b⊩x))

        opaque
          pointwise : ∀ a b → theCanonicalPER .PER.relation a b ≡ per .PER.relation a b
          pointwise a b =
            hPropExt
              (theCanonicalPER .PER.isPropValued a b)
              (per .PER.isPropValued a b)
              (dir1 a b)
              {!!}
        

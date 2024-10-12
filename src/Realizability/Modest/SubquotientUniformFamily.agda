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

module Realizability.Modest.SubquotientUniformFamily {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) (resizing : hPropResizing ℓ) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Terminal ca
open import Realizability.Assembly.SetsReflectiveSubcategory ca
open import Realizability.Modest.Base ca
open import Realizability.Modest.UniformFamily ca
open import Realizability.Modest.CanonicalPER ca
open import Realizability.Modest.UnresizedGeneric ca
open import Realizability.PERs.PER ca
open import Realizability.PERs.ResizedPER ca resizing
open import Realizability.PERs.SubQuotient ca

open Assembly
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open Contravariant UNIMOD
open UniformFamily
open DisplayedUFamMap

private
  ∇PER = ∇ ⟅ ResizedPER , isSetResizedPER ⟆
  asm∇PER = ∇PER .snd

-- G over ∇PER
subQuotientUniformFamily : UniformFamily asm∇PER
UniformFamily.carriers subQuotientUniformFamily per = subQuotient (enlargePER per)
UniformFamily.assemblies subQuotientUniformFamily per = subQuotientAssembly (enlargePER per)
UniformFamily.isModestFamily subQuotientUniformFamily per = isModestSubQuotientAssembly (enlargePER per)

-- For any uniform family M over X
-- there is a map to the canonical uniform family G over ∇PER
module _
  {X : Type ℓ}
  {asmX : Assembly X}
  (M : UniformFamily asmX) where

  classifyingMap : AssemblyMorphism asmX asm∇PER
  AssemblyMorphism.map classifyingMap x = shrinkPER (canonicalPER (M .assemblies x) (M .isModestFamily x))
  AssemblyMorphism.tracker classifyingMap = return (k , (λ _ _ _ → tt*))

  opaque
      unfolding Unresized.mainMap
      classifyingMapᴰ : DisplayedUFamMap asmX asm∇PER classifyingMap M subQuotientUniformFamily
      DisplayedUFamMap.fibrewiseMap classifyingMapᴰ x Mx =
        subst
          subQuotient
          (sym
            (enlargePER⋆shrinkPER≡id
              (canonicalPER (M .assemblies x) (M .isModestFamily x))))
          (Unresized.mainMap resizing asmX M x Mx .fst)
      DisplayedUFamMap.isTracked classifyingMapᴰ =
        return
          ((λ*2 (# zero)) ,
          (λ x a a⊩x Mx b b⊩Mx →
            -- Is there a way to do this that avoids transp ?
            -- This really eats type-checking time
            transp
              (λ i →
                ⟨
                  subQuotientRealizability
                    (enlargePER⋆shrinkPER≡id
                      (canonicalPER (M .assemblies x) (M .isModestFamily x)) (~ i))
                    (λ*2 (# zero) ⨾ a ⨾ b)
                    (subst-filler
                      subQuotient
                      (sym
                        (enlargePER⋆shrinkPER≡id
                        (canonicalPER (M .assemblies x) (M .isModestFamily x))))
                        (Unresized.mainMap resizing asmX M x Mx .fst) i)
                ⟩) i0 (Unresized.mainMap resizing asmX M x Mx .snd a a⊩x b b⊩Mx)))


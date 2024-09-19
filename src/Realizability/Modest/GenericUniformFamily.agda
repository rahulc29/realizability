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

module Realizability.Modest.GenericUniformFamily {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) (resizing : hPropResizing ℓ) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Terminal ca
open import Realizability.Assembly.SetsReflectiveSubcategory ca
open import Realizability.Modest.Base ca
open import Realizability.Modest.UniformFamily ca
open import Realizability.Modest.CanonicalPER ca
open import Realizability.Modest.UnresizedGeneric ca
open import Realizability.Modest.SubquotientUniformFamily ca resizing
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

genericUniformFamily : GenericObject UNIMOD
GenericObject.base genericUniformFamily = ∇PER
GenericObject.displayed genericUniformFamily = subQuotientUniformFamily
GenericObject.isGeneric genericUniformFamily {X , asmX} M =
  f , fᴰ , isCartesian'→isCartesian f fᴰ cart' where

    f : AssemblyMorphism asmX asm∇PER
    f = classifyingMap M

    opaque
      unfolding Unresized.mainMap
      fᴰ : DisplayedUFamMap asmX asm∇PER f M (genericUniformFamily .GenericObject.displayed)
      fᴰ = classifyingMapᴰ M

    opaque
      unfolding isCartesian'
      cart' : isCartesian' f fᴰ
      cart' {Y , asmY} {N} g hᴰ =
        (! , {!!}) , {!!} where
        
          ! : DisplayedUFamMap asmY asmX g N M
          DisplayedUFamMap.fibrewiseMap ! y Ny = lhsIsoRhs .fst .map {!hᴰ .fibrewiseMap y Ny!} module !Definition where
            gy : X
            gy = g .map y

            canonicalPERMgy : PER
            canonicalPERMgy = canonicalPER (M .assemblies gy) (M .isModestFamily gy)

            lhsModestSet : MOD .Category.ob
            lhsModestSet = subQuotient canonicalPERMgy , subQuotientAssembly canonicalPERMgy , isModestSubQuotientAssembly canonicalPERMgy

            rhsModestSet : MOD .Category.ob
            rhsModestSet = M .carriers gy , M .assemblies gy , M .isModestFamily gy

            lhsIsoRhs : CatIso MOD lhsModestSet rhsModestSet
            lhsIsoRhs = {!!}
          DisplayedUFamMap.isTracked ! = {!!}
    

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Adjoint
open import Cubical.Categories.NaturalTransformation
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure

module Realizability.Assembly.SetsReflectiveSubcategory {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca

open Assembly
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

forgetfulFunctor : Functor ASM (SET ℓ)
Functor.F-ob forgetfulFunctor (X , asmX) = X , asmX .isSetX
Functor.F-hom forgetfulFunctor {X , asmX} {Y , asmY} f = f .map
Functor.F-id forgetfulFunctor = refl
Functor.F-seq forgetfulFunctor {X , asmX} {Y , asmY} {Z , asmZ} f g = refl

∇ : Functor (SET ℓ) ASM
Functor.F-ob ∇ (X , isSetX) = X , makeAssembly (λ a x → Unit*) isSetX (λ _ _ → isPropUnit*) λ x → ∣ k , tt* ∣₁
Functor.F-hom ∇ {X , isSetX} {Y , isSetY} f = makeAssemblyMorphism f (return (k , (λ _ _ _ → tt*)))
Functor.F-id ∇ {X , isSetX} = AssemblyMorphism≡ _ _ refl
Functor.F-seq ∇ {X , isSetX} {Y , isSetY} {Z , isSetZ} f g = AssemblyMorphism≡ _ _ refl

module _ where
  open UnitCounit

  adjointUnitCounit : forgetfulFunctor ⊣ ∇
  NatTrans.N-ob (_⊣_.η adjointUnitCounit) (X , asmX) = makeAssemblyMorphism (λ x → x) (return (k , (λ _ _ _ → tt*)))
  NatTrans.N-hom (_⊣_.η adjointUnitCounit) {X , asmX} {Y , asmY} f = AssemblyMorphism≡ _ _ refl
  NatTrans.N-ob (_⊣_.ε adjointUnitCounit) (X , isSetX) x = x
  NatTrans.N-hom (_⊣_.ε adjointUnitCounit) {X , isSetX} {Y , isSetY} f = refl
  TriangleIdentities.Δ₁ (_⊣_.triangleIdentities adjointUnitCounit) (X , asmX) = refl
  TriangleIdentities.Δ₂ (_⊣_.triangleIdentities adjointUnitCounit) (X , isSetX) = AssemblyMorphism≡ _ _ refl

module _ where
  open NaturalBijection

  adjointNaturalBijection : forgetfulFunctor ⊣ ∇
  Iso.fun (_⊣_.adjIso adjointNaturalBijection) f = makeAssemblyMorphism f (return (k , (λ x r r⊩x → tt*)))
  Iso.inv (_⊣_.adjIso adjointNaturalBijection) f = f .map
  Iso.rightInv (_⊣_.adjIso adjointNaturalBijection) b = AssemblyMorphism≡ _ _ refl
  Iso.leftInv (_⊣_.adjIso adjointNaturalBijection) a = refl
  _⊣_.adjNatInD adjointNaturalBijection {X , isSetX} {Y , isSetY} f g = AssemblyMorphism≡ _ _ refl
  _⊣_.adjNatInC adjointNaturalBijection {X , asmX} {Y , asmY} f g = refl


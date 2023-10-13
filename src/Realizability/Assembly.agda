{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Prod hiding (map)

open import Realizability.CombinatoryAlgebra

module Realizability.Assembly {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
  open CombinatoryAlgebra ca
  open Realizability.CombinatoryAlgebra.Combinators ca

  record Assembly (X : Type ℓ) : Type (ℓ-suc ℓ) where
    infix 25 _⊩_
    field
      isSetX : isSet X
      _⊩_ : A → X → Type ℓ
      ⊩isPropValued : ∀ a x → isProp (a ⊩ x)
      ⊩surjective : ∀ x → Σ[ a ∈ A ] a ⊩ x

  open Assembly
  unitAssembly : Assembly Unit*
  unitAssembly .isSetX = isSetUnit*
  unitAssembly ._⊩_ a x = Unit*
  unitAssembly .⊩isPropValued a x = isPropUnit*
  unitAssembly .⊩surjective x = s ⨾ k ⨾ k , tt*

  emptyAssembly : Assembly ⊥*
  emptyAssembly .isSetX = isProp→isSet isProp⊥*
  emptyAssembly ._⊩_ a x = Unit*
  emptyAssembly .⊩isPropValued a x = isPropUnit*
  emptyAssembly .⊩surjective x = s ⨾ k ⨾ k , tt*
  
  record AssemblyMorphism {X Y : Type ℓ} (as : Assembly X) (bs : Assembly Y) : Type ℓ where
    open Assembly as renaming (_⊩_ to _⊩X_)
    open Assembly bs renaming (_⊩_ to _⊩Y_)
    field
      map : X → Y
      tracker : A
      trackerTracks : ∀ (x : X) (aₓ : A) → (aₓ ⊩X x) → (tracker ⨾ aₓ) ⊩Y (map x)

  open AssemblyMorphism
  identityMorphism : {X : Type ℓ} (as : Assembly X) → AssemblyMorphism as as
  identityMorphism as .map x = x
  identityMorphism as .tracker = i
  identityMorphism as .trackerTracks x aₓ aₓ⊩x = subst (λ y → (as ⊩ y) x) (sym (ia≡a aₓ)) aₓ⊩x

  compositeMorphism : {X Y Z : Type ℓ} {xs : Assembly X} {ys : Assembly Y} {zs : Assembly Z} → (f : AssemblyMorphism xs ys) → (g : AssemblyMorphism ys zs) → AssemblyMorphism xs zs
  compositeMorphism f g .map x = g .map (f .map x)
  compositeMorphism f g .tracker = B (g .tracker) (f .tracker)
  compositeMorphism {xs = xs} {ys = ys} {zs = zs} f g .trackerTracks x aₓ aₓ⊩x = goal where
                      open Assembly xs renaming (_⊩_ to _⊩X_)
                      open Assembly ys renaming (_⊩_ to _⊩Y_)
                      open Assembly zs renaming (_⊩_ to _⊩Z_)

                      f~ = f .tracker
                      g~ = g .tracker
                      a = aₓ

                      easierVariant : (g~ ⨾ (f~ ⨾ aₓ)) ⊩Z g .map (f .map x)
                      easierVariant = g .trackerTracks (f .map x) (f~ ⨾ aₓ) (f .trackerTracks x aₓ aₓ⊩x)
                      
                      goal : ((compositeMorphism f g) .tracker ⨾ aₓ) ⊩Z (compositeMorphism f g) .map x
                      goal = subst (λ y → y ⊩Z g .map (f .map x)) (sym (Ba≡gfa g~ f~ a)) easierVariant

  -- Some constructions on assemblies
  infixl 23 _⊗_
  _⊗_ : {A B : Type ℓ} → Assembly A → Assembly B → Assembly (A × B)
  (as ⊗ bs) .isSetX = isOfHLevelProd 2 (as .isSetX) (bs .isSetX)
  (as ⊗ bs) ._⊩_ r (a , b) = {!!}
  (as ⊗ bs) .⊩isPropValued = {!!}
  (as ⊗ bs) .⊩surjective (a , b) = {!!} , {!!}
                      
      
  

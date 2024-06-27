{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Category
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure

module Realizability.Assembly.Morphism {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Base ca

open Assembly
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

module _ {X Y : Type ℓ} {xs : Assembly X} {ys : Assembly Y} (t : A) (f : X → Y)  where
  
  tracks : Type ℓ
  tracks = ∀ (x : X) (aₓ : A) → (aₓ ⊩X x) → (t ⨾ aₓ) ⊩Y (f x) where
    _⊩X_ = xs ._⊩_
    _⊩Y_ = ys ._⊩_
      
  isPropTracks : isProp tracks
  isPropTracks = isPropΠ λ x →
                         isPropΠ λ aₓ →
                           isPropΠ λ aₓ⊩x →
                             ys .⊩isPropValued (t ⨾ aₓ) (f x)
    
record AssemblyMorphism {X Y : Type ℓ} (as : Assembly X) (bs : Assembly Y) : Type ℓ where
  no-eta-equality
  constructor makeAssemblyMorphism
  open Assembly as renaming (_⊩_ to _⊩X_)
  open Assembly bs renaming (_⊩_ to _⊩Y_)
  field
    map : X → Y
    tracker : ∃[ t ∈ A ] ((x : X) (aₓ : A) → (aₓ ⊩X x) → (t ⨾ aₓ) ⊩Y (map x))
open AssemblyMorphism

unquoteDecl AssemblyMorphismIsoΣ = declareRecordIsoΣ AssemblyMorphismIsoΣ (quote AssemblyMorphism)

module _ {X Y : Type ℓ} (xs : Assembly X) (ys : Assembly Y) where
    
  AssemblyMorphismΣ : Type ℓ
  AssemblyMorphismΣ = Σ[ map ∈ (X → Y) ] ∃[ t ∈ A ] ((x : X) (aₓ : A) → (aₓ ⊩X x) → (t ⨾ aₓ) ⊩Y (map x)) where
    _⊩X_ = xs ._⊩_
    _⊩Y_ = ys ._⊩_

  isSetAssemblyMorphismΣ : isSet AssemblyMorphismΣ
  isSetAssemblyMorphismΣ = isSetΣ (isSet→ (ys .isSetX)) (λ map → isProp→isSet squash₁)
                                                                              
  AssemblyMorphism≡Σ = isoToPath (AssemblyMorphismIsoΣ {as = xs} {bs = ys})

  isSetAssemblyMorphism : isSet (AssemblyMorphism xs ys)
  isSetAssemblyMorphism = subst (λ t → isSet t) (sym AssemblyMorphism≡Σ) isSetAssemblyMorphismΣ

AssemblyMorphism≡Equiv : ∀ {X Y : Type ℓ} {xs : Assembly X} {ys : Assembly Y} (f g : AssemblyMorphismΣ xs ys) → (f .fst ≡ g .fst) ≃ (f ≡ g)
AssemblyMorphism≡Equiv {X} {Y} {xs} {ys} f g = Σ≡PropEquiv λ _ → isPropPropTrunc

AssemblyMorphismΣ≡ : {X Y : Type ℓ}
                     {xs : Assembly X}
                     {ys : Assembly Y}
                     (f g : AssemblyMorphismΣ xs ys)
                     → f .fst ≡ g .fst
                     ---------------------------------
                     → f ≡ g
AssemblyMorphismΣ≡ f g = Σ≡Prop λ _ → squash₁

module _ {X Y : Type ℓ}
         {xs : Assembly X}
         {ys : Assembly Y}
         (f g : AssemblyMorphism xs ys) where
       -- Necessary to please the constraint solver
       theIso = AssemblyMorphismIsoΣ {X} {Y} {as = xs} {bs = ys}
       thePath = AssemblyMorphismΣ≡ {X = X} {Y = Y} {xs = xs} {ys = ys}
       open Iso
       AssemblyMorphism≡ : (f .map ≡ g .map) → f ≡ g
       map (AssemblyMorphism≡ fmap≡gmap i) x = fmap≡gmap i x
       tracker (AssemblyMorphism≡ fmap≡gmap i) =
         isProp→PathP
           (λ i → isPropPropTrunc {A = Σ[ t ∈ A ] (∀ x aₓ → aₓ ⊩[ xs ] x → (t ⨾ aₓ) ⊩[ ys ] (fmap≡gmap i x))})
           (f .tracker) (g .tracker) i

identityMorphism : {X : Type ℓ} (as : Assembly X) → AssemblyMorphism as as
identityMorphism as .map x = x
identityMorphism as .tracker = ∣ Id , (λ x aₓ aₓ⊩x → subst (λ y → (as ⊩ y) x) (sym (Ida≡a aₓ)) aₓ⊩x) ∣₁

compositeMorphism : {X Y Z : Type ℓ} {xs : Assembly X} {ys : Assembly Y} {zs : Assembly Z}
                  → (f : AssemblyMorphism xs ys)
                  → (g : AssemblyMorphism ys zs)
                  → AssemblyMorphism xs zs
compositeMorphism f g .map x = g .map (f .map x)
compositeMorphism {X} {Y} {Z} {xs} {ys} {zs} f g .tracker =
  do
    (f~ , isTrackedF) ← f .tracker
    (g~ , isTrackedG) ← g .tracker
    let
      realizer : Term as 1
      realizer = ` g~ ̇ (` f~ ̇ # zero)
    return
      (λ* realizer ,
      (λ x aₓ aₓ⊩x → subst (λ r' → r' ⊩[ zs ] (g .map (f .map x))) (sym (λ*ComputationRule realizer aₓ)) (isTrackedG (f .map x) (f~ ⨾ aₓ) (isTrackedF x aₓ aₓ⊩x))))

infixl 23 _⊚_
_⊚_ : {X Y Z : Type ℓ} → {xs : Assembly X} {ys : Assembly Y} {zs : Assembly Z}
                       → AssemblyMorphism xs ys
                       → AssemblyMorphism ys zs
                       → AssemblyMorphism xs zs
f ⊚ g = compositeMorphism f g

module _ {X Y : Type ℓ} (xs : Assembly X) (ys : Assembly Y) where
  ⊚idL : ∀ (f : AssemblyMorphism xs ys) → identityMorphism xs ⊚ f ≡ f
  ⊚idL f = AssemblyMorphism≡ (identityMorphism xs ⊚ f) f (funExt λ x → refl)

  ⊚idR : ∀ (f : AssemblyMorphism ys xs) → f ⊚ identityMorphism xs ≡ f
  ⊚idR f = AssemblyMorphism≡ (f ⊚ identityMorphism xs) f (funExt λ x → refl)

module _ {X Y Z W : Type ℓ}
         (xs : Assembly X)
         (ys : Assembly Y)
         (zs : Assembly Z)
         (ws : Assembly W)
         (f : AssemblyMorphism xs ys)
         (g : AssemblyMorphism ys zs)
         (h : AssemblyMorphism zs ws) where

       ⊚assoc : (f ⊚ g) ⊚ h ≡ f ⊚ (g ⊚ h)
       ⊚assoc = AssemblyMorphism≡ ((f ⊚ g) ⊚ h) (f ⊚ (g ⊚ h)) (∘-assoc (h .map) (g .map) (f .map))

open Category
  
ASM : Category (ℓ-suc ℓ) ℓ
ASM .ob = Σ[ X ∈ Type ℓ ] Assembly X
ASM .Hom[_,_] x y = AssemblyMorphism (x .snd) (y .snd)
ASM .id {x} = identityMorphism (x .snd)
ASM ._⋆_ f g = f ⊚ g
ASM .⋆IdL {x} {y} f = ⊚idL (x .snd) (y .snd) f
ASM .⋆IdR {x} {y} f = ⊚idR (y .snd) (x .snd) f
ASM .⋆Assoc {x} {y} {z} {w} f g h = ⊚assoc (x .snd) (y .snd) (z .snd) (w .snd) f g h
ASM .isSetHom {x} {y} f g = isSetAssemblyMorphism (x .snd) (y .snd) f g

open AssemblyMorphism public

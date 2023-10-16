{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (map)
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.SetCoequalizer

open import Realizability.CombinatoryAlgebra

module Realizability.Assembly {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
  open CombinatoryAlgebra ca
  open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

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

  -- An unnecessarily goofy proof that the space of assembly morphisms is a set
  -- Need to transport over a path to the identical Σ type cause the
  -- standard library interface only accepts Σ and Π types
  module _ where
    assemblyMorphismΣ : {X Y : Type ℓ} (xs : Assembly X) (ys : Assembly Y) → Type ℓ
    assemblyMorphismΣ {X} {Y} xs ys = Σ[ map ∈ (X → Y) ] Σ[ tracker ∈ A ] (∀ (x : X) (aₓ : A) → (xs ._⊩_ aₓ x) → ys ._⊩_ (tracker ⨾ aₓ) (map x))

    isSetAssemblyMorphismΣ : {X Y : Type ℓ} (xs : Assembly X) (ys : Assembly Y) → isSet (assemblyMorphismΣ xs ys)
    isSetAssemblyMorphismΣ xs ys = isSetΣ (isSetΠ λ _ → ys .isSetX) (λ map → isSetΣ isSetA λ a → isSetΠ λ x → isSetΠ λ aₓ → isSetΠ λ aₓ⊩x → isProp→isSet (ys .⊩isPropValued (a ⨾ aₓ) (map x)))

    assemblyMorphismΣ≡AssemblyMorphism : {X Y : Type ℓ} (xs : Assembly X) (ys : Assembly Y) → assemblyMorphismΣ xs ys ≡ AssemblyMorphism xs ys
    assemblyMorphismΣ≡AssemblyMorphism xs ys = isoToPath (iso (λ (map , tracker , trackerTracks) → record { map = map; tracker = tracker; trackerTracks = trackerTracks }) (λ assembly → (assembly .map , assembly .tracker , assembly .trackerTracks)) (λ b → refl) λ a → refl)

    isSetAssemblyMorphism : {X Y : Type ℓ} (xs : Assembly X) (ys : Assembly Y) → isSet (AssemblyMorphism xs ys)
    isSetAssemblyMorphism xs ys = subst (λ x → isSet x) (assemblyMorphismΣ≡AssemblyMorphism xs ys) (isSetAssemblyMorphismΣ xs ys)

  identityMorphism : {X : Type ℓ} (as : Assembly X) → AssemblyMorphism as as
  identityMorphism as .map x = x
  identityMorphism as .tracker = Id
  identityMorphism as .trackerTracks x aₓ aₓ⊩x = subst (λ y → (as ⊩ y) x) (sym (Ida≡a aₓ)) aₓ⊩x

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
  (as ⊗ bs) .isSetX = isSetΣ (as .isSetX) (λ _ → bs .isSetX)
  (as ⊗ bs) ._⊩_ r (a , b) = (as ._⊩_ (pr₁ ⨾ r) a) × (bs ._⊩_ (pr₂ ⨾ r) b)
  (as ⊗ bs) .⊩isPropValued r (a , b) = isPropΣ (as .⊩isPropValued (pr₁ ⨾ r) a) (λ _ → bs .⊩isPropValued (pr₂ ⨾ r) b)
  (as ⊗ bs) .⊩surjective (a , b) = pair ⨾ (as .⊩surjective a) .fst ⨾ (bs .⊩surjective b) .fst , subst (λ x → as ._⊩_ x a) (sym (pr₁pxy≡x (as .⊩surjective a .fst) (bs .⊩surjective b .fst))) (as .⊩surjective a .snd) , subst (λ x → bs ._⊩_ x b) (sym (pr₂pxy≡y (as .⊩surjective a .fst) (bs .⊩surjective b .fst))) (bs .⊩surjective b .snd)

  π₁ : {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} → AssemblyMorphism (as ⊗ bs) as
  π₁ .map (a , b) = a
  π₁ .tracker = pr₁
  π₁ .trackerTracks (a , b) p (goal , _) = goal

  π₂ : {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} → AssemblyMorphism (as ⊗ bs) bs
  π₂ .map (a , b) = b
  π₂ .tracker = pr₂
  π₂ .trackerTracks (a , b) p (_ , goal) = goal

  -- Not sure if this is correct but okay let us see
  infixl 23 _⊕_
  _⊕_ : {A B : Type ℓ} → Assembly A → Assembly B → Assembly (A ⊎ B)
  (as ⊕ bs) .isSetX = isSet⊎ (as .isSetX) (bs .isSetX)
  (as ⊕ bs) ._⊩_ r (inl a) = ∃[ aᵣ ∈ A ] (as ._⊩_ aᵣ a) × (r ≡ pair ⨾ true ⨾ aᵣ)
  (as ⊕ bs) ._⊩_ r (inr b) = ∃[ bᵣ ∈ A ] (bs ._⊩_ bᵣ b) × (r ≡ pair ⨾ false ⨾ bᵣ)
  (as ⊕ bs) .⊩isPropValued r (inl a) = squash₁
  (as ⊕ bs) .⊩isPropValued r (inr b) = squash₁
  (as ⊕ bs) .⊩surjective (inl a) = pair ⨾ true ⨾ (as .⊩surjective a .fst) , ∣ (as .⊩surjective a .fst) , as .⊩surjective a .snd , refl ∣₁
  (as ⊕ bs) .⊩surjective (inr b) = pair ⨾ false ⨾ (bs .⊩surjective b .fst) , ∣ (bs .⊩surjective b .fst) , bs .⊩surjective b .snd , refl ∣₁

  κ₁ : {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} → AssemblyMorphism as (as ⊕ bs)
  κ₁ .map a = inl a
  κ₁ .tracker = pair ⨾ true
  κ₁ .trackerTracks x aₓ aₓ⊩x = ∣ aₓ , aₓ⊩x , refl ∣₁

  κ₂ : {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} → AssemblyMorphism bs (as ⊕ bs)
  κ₂ .map b = inr b
  κ₂ .tracker = pair ⨾ false
  κ₂ .trackerTracks x bₓ bₓ⊩x =  ∣ bₓ , bₓ⊩x , refl ∣₁

  -- (Co)equalisers lessgo!
  module _ {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} (f g : AssemblyMorphism as bs) where
    equalizer : Assembly (Σ[ a ∈ A ] f .map a ≡ g .map a)
    equalizer .isSetX = isSetΣ (as .isSetX) λ x → isProp→isSet (bs .isSetX (f .map x) (g .map x))
    equalizer ._⊩_ r (a , fa≡ga) = as ._⊩_ r a
    equalizer .⊩isPropValued r (a , fa≡ga) = as .⊩isPropValued r a
    equalizer .⊩surjective (a , fa≡ga) = as .⊩surjective a

    coequalizer : Assembly (SetCoequalizer (f .map) (g .map))
    coequalizer .isSetX = squash
    coequalizer ._⊩_ r b = ∃[ b' ∈ B ] (b ≡ inc b') × (bs ._⊩_ r b')
    coequalizer .⊩isPropValued r b = squash₁
    coequalizer .⊩surjective (inc b) = bs .⊩surjective b .fst , ∣ b , refl , bs .⊩surjective b .snd ∣₁
    coequalizer .⊩surjective (coeq a i) = {!!} , {!!}
    coequalizer .⊩surjective (squash x y p q i j) = {!!} , {!!}

  -- Exponential objects
  _⇒_ : {A B : Type ℓ} → (as : Assembly A) → (bs : Assembly B) → Assembly (AssemblyMorphism as bs)
  (as ⇒ bs) .isSetX = isSetAssemblyMorphism as bs
  (as ⇒ bs) ._⊩_ r f = r ≡ f .tracker
  (as ⇒ bs) .⊩isPropValued r f = isSetA r (f .tracker)
  (as ⇒ bs) .⊩surjective f = f .tracker , refl

  -- What a distinguished gentleman
  eval : {A B : Type ℓ} → (as : Assembly A) → (bs : Assembly B) → AssemblyMorphism ((as ⇒ bs) ⊗ as) bs
  eval as bs .map (f , x) = f .map x
  eval as bs .tracker = s ⨾ (s ⨾ (k ⨾ pr₁) ⨾ Id) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id)
  eval as bs .trackerTracks (f , x) r r⊩fx = subst (λ tracker → bs ._⊩_ tracker (f .map x)) (sym tracker⨾r≡pr₁r⨾pr₂r) pr₁r⨾pr₂rTracks where
    fTracker⨾pr₂r⊩fx : (rₐ : A) → (as ._⊩_ rₐ x) → bs ._⊩_ (f .tracker ⨾ rₐ) (f .map x)
    fTracker⨾pr₂r⊩fx rₐ rₐ⊩x = f .trackerTracks x rₐ rₐ⊩x

    pr₁r⨾pr₂rTracks : bs ._⊩_ (pr₁ ⨾ r ⨾ (pr₂ ⨾ r)) (f .map x)
    pr₁r⨾pr₂rTracks = subst (λ tracker → bs ._⊩_ (tracker ⨾ (pr₂ ⨾ r)) (f .map x)) (sym (r⊩fx .fst)) (fTracker⨾pr₂r⊩fx (pr₂ ⨾ r) (r⊩fx .snd))

    tracker⨾r≡pr₁r⨾pr₂r : s ⨾ (s ⨾ (k ⨾ pr₁) ⨾ Id) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id) ⨾ r ≡ (pr₁ ⨾ r) ⨾ (pr₂ ⨾ r)
    tracker⨾r≡pr₁r⨾pr₂r =
                        s ⨾ (s ⨾ (k ⨾ pr₁) ⨾ Id) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id) ⨾ r
                          ≡⟨ sabc≡ac_bc _ _ _  ⟩
                        (s ⨾ (k ⨾ pr₁) ⨾ Id ⨾ r) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id ⨾ r)
                          ≡⟨ cong (λ x → x ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id ⨾ r)) (sabc≡ac_bc _ _ _)  ⟩
                        (k ⨾ pr₁ ⨾ r ⨾ (Id ⨾ r)) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id ⨾ r)
                          ≡⟨ cong (λ x → (k ⨾ pr₁ ⨾ r ⨾ (Id ⨾ r)) ⨾ x) (sabc≡ac_bc _ _ _) ⟩
                        (k ⨾ pr₁ ⨾ r ⨾ (Id ⨾ r)) ⨾ (k ⨾ pr₂ ⨾ r ⨾ (Id ⨾ r))
                          ≡⟨ cong (λ x → (x ⨾ (Id ⨾ r)) ⨾ (k ⨾ pr₂ ⨾ r ⨾ (Id ⨾ r))) (kab≡a _ _) ⟩
                        (pr₁ ⨾ (Id ⨾ r)) ⨾ (k ⨾ pr₂ ⨾ r ⨾ (Id ⨾ r))
                          ≡⟨ cong (λ x → (pr₁ ⨾ x) ⨾ (k ⨾ pr₂ ⨾ r ⨾ (Id ⨾ r))) (Ida≡a r) ⟩
                        (pr₁ ⨾ r) ⨾ (k ⨾ pr₂ ⨾ r ⨾ (Id ⨾ r))
                          ≡⟨ cong (λ x → (pr₁ ⨾ r) ⨾ (x ⨾ (Id ⨾ r))) (kab≡a _ _)  ⟩
                        (pr₁ ⨾ r) ⨾ (pr₂ ⨾ (Id ⨾ r))
                          ≡⟨ cong (λ x → (pr₁ ⨾ r) ⨾ (pr₂ ⨾ x)) (Ida≡a r) ⟩
                        (pr₁ ⨾ r) ⨾ (pr₂ ⨾ r)
                          ∎

    

 
      
  

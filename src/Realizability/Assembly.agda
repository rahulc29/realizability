{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum hiding (map)
open import Cubical.HITs.PropositionalTruncation renaming (map to ∥∥map ; map2 to ∥∥map2)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Binary
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Initial
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Reflection.RecordEquiv

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
      ⊩surjective : ∀ x → ∃[ a ∈ A ] a ⊩ x

  open Assembly
  unitAssembly : Assembly Unit*
  unitAssembly .isSetX = isSetUnit*
  unitAssembly ._⊩_ a x = Unit*
  unitAssembly .⊩isPropValued a x = isPropUnit*
  unitAssembly .⊩surjective x = ∣ s ⨾ k ⨾ k , tt* ∣₁

  emptyAssembly : Assembly ⊥*
  emptyAssembly .isSetX = isProp→isSet isProp⊥*
  emptyAssembly ._⊩_ a x = ⊥*
  emptyAssembly .⊩isPropValued a x = isProp⊥*
  emptyAssembly .⊩surjective x = ∣ s ⨾ k ⨾ k , x ∣₁

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

  AssemblyMorphismΣ≡ : {X Y : Type ℓ}
                      {xs : Assembly X}
                      {ys : Assembly Y}
                      (f g : AssemblyMorphismΣ xs ys)
                      → f .fst ≡ g .fst
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
         AssemblyMorphism≡ fmap≡gmap i = theIso .inv (thePath (theIso .fun f) (theIso .fun g) (fmap≡gmap) i)

  identityMorphism : {X : Type ℓ} (as : Assembly X) → AssemblyMorphism as as
  identityMorphism as .map x = x
  identityMorphism as .tracker = ∣ Id , (λ x aₓ aₓ⊩x → subst (λ y → (as ⊩ y) x) (sym (Ida≡a aₓ)) aₓ⊩x) ∣₁

  compositeMorphism : {X Y Z : Type ℓ} {xs : Assembly X} {ys : Assembly Y} {zs : Assembly Z}
                    → (f : AssemblyMorphism xs ys)
                    → (g : AssemblyMorphism ys zs)
                    → AssemblyMorphism xs zs
  compositeMorphism f g .map x = g .map (f .map x)
  compositeMorphism {X} {Y} {Z} {xs} {ys} {zs} f g .tracker = ∥∥map2 untruncated (f .tracker) (g .tracker) where
                      open Assembly xs renaming (_⊩_ to _⊩X_)
                      open Assembly ys renaming (_⊩_ to _⊩Y_)
                      open Assembly zs renaming (_⊩_ to _⊩Z_)
                      module _ (fTracker : Σ[ f~ ∈ A ] tracks {xs = xs} {ys = ys} f~ (f .map))
                               (gTracker : Σ[ g~ ∈ A ] tracks {xs = ys} {ys = zs} g~ (g .map)) where
                               
                             f~ = fTracker .fst
                             f~tracks = fTracker .snd

                             g~ = gTracker .fst
                             g~tracks = gTracker .snd

                             easierVariant : ∀ x aₓ aₓ⊩x → (g~ ⨾ (f~ ⨾ aₓ)) ⊩Z g .map (f .map x)
                             easierVariant x aₓ aₓ⊩x = g~tracks (f .map x) (f~ ⨾ aₓ) (f~tracks x aₓ aₓ⊩x)
                             
                             goal : ∀ (x : X) (aₓ : A) (aₓ⊩x : aₓ ⊩X x)
                                    → (B g~ f~ ⨾ aₓ) ⊩Z (compositeMorphism f g .map x)
                             goal x aₓ aₓ⊩x = subst (λ y → y ⊩Z g .map (f .map x))
                                                    (sym (Ba≡gfa g~ f~ aₓ))
                                                    (easierVariant x aₓ aₓ⊩x)

                             untruncated : Σ[ t ∈ A ]
                                           ((x : X) (aₓ : A)
                                           → aₓ ⊩X x
                                           → (t ⨾ aₓ) ⊩Z (compositeMorphism f g) .map x)
                             untruncated = B g~ f~ , goal
                             
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
  
  -- Some constructions on assemblies
  infixl 23 _⊗_
  _⊗_ : {A B : Type ℓ} → Assembly A → Assembly B → Assembly (A × B)
  (as ⊗ bs) .isSetX = isSetΣ (as .isSetX) (λ _ → bs .isSetX)
  (as ⊗ bs) ._⊩_ r (a , b) = (as ._⊩_ (pr₁ ⨾ r) a) × (bs ._⊩_ (pr₂ ⨾ r) b)
  (as ⊗ bs) .⊩isPropValued r (a , b) = isPropΣ (as .⊩isPropValued (pr₁ ⨾ r) a)
                                                (λ _ → bs .⊩isPropValued (pr₂ ⨾ r) b)
  (as ⊗ bs) .⊩surjective (a , b) = do
                                   (b~ , b~realizes) ← bs .⊩surjective b
                                   (a~ , a~realizes) ← as .⊩surjective a
                                   return
                                     ( pair ⨾ a~ ⨾ b~
                                     , subst (λ x → as ._⊩_ x a) (sym (pr₁pxy≡x a~ b~)) a~realizes
                                     , subst (λ x → bs ._⊩_ x b) (sym (pr₂pxy≡y a~ b~)) b~realizes
                                     )

  π₁ : {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} → AssemblyMorphism (as ⊗ bs) as
  π₁ .map (a , b) = a
  π₁ .tracker = ∣ pr₁ , (λ (a , b) p (goal , _) → goal) ∣₁

  π₂ : {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} → AssemblyMorphism (as ⊗ bs) bs
  π₂ .map (a , b) = b
  π₂ .tracker = ∣ pr₂ , (λ (a , b) p (_ , goal) → goal) ∣₁

  ⟨_,_⟩ : {X Y Z : Type ℓ}
        → {xs : Assembly X} {ys : Assembly Y} {zs : Assembly Z}
        → AssemblyMorphism zs xs
        → AssemblyMorphism zs ys
        → AssemblyMorphism zs (xs ⊗ ys)
  ⟨ f , g ⟩ .map z = f .map z , g .map z
  ⟨_,_⟩ {X} {Y} {Z} {xs} {ys} {zs} f g .tracker = ∥∥map2 untruncated (f .tracker) (g .tracker) where
    module _ 
             ((f~ , f~tracks) : Σ[ f~ ∈ A ] tracks {xs = zs} {ys = xs}  f~ (f .map))
             ((g~ , g~tracks) : Σ[ g~ ∈ A ] tracks {xs = zs} {ys = ys} g~ (g .map)) where
             
             _⊩X_ = xs ._⊩_
             _⊩Y_ = ys ._⊩_
             _⊩Z_ = zs ._⊩_
             
             t = s ⨾ (s ⨾ (k ⨾ pair) ⨾ (s ⨾ (k ⨾ f~) ⨾ Id)) ⨾ (s ⨾ (k ⨾ g~) ⨾ Id)
             untruncated : Σ[ t ∈ A ] (∀ z zᵣ zᵣ⊩z → ((pr₁ ⨾ (t ⨾ zᵣ)) ⊩X (f .map z)) × ((pr₂ ⨾ (t ⨾ zᵣ)) ⊩Y (g .map z)))
             untruncated = t , λ z zᵣ zᵣ⊩z → goal₁ z zᵣ zᵣ⊩z , goal₂ z zᵣ zᵣ⊩z where
               module _ (z : Z) (zᵣ : A) (zᵣ⊩z : zᵣ ⊩Z z) where

                 pr₁⨾tracker⨾zᵣ≡f~⨾zᵣ : pr₁ ⨾ (t ⨾ zᵣ) ≡ f~ ⨾ zᵣ
                 pr₁⨾tracker⨾zᵣ≡f~⨾zᵣ =
                         pr₁ ⨾ (s ⨾ (s ⨾ (k ⨾ pair) ⨾ (s ⨾ (k ⨾ f~) ⨾ Id)) ⨾ (s ⨾ (k ⨾ g~) ⨾ Id) ⨾ zᵣ)
                           ≡⟨ cong (λ x → pr₁ ⨾ x) (sabc≡ac_bc _ _ _) ⟩
                         pr₁ ⨾ (s ⨾ (k ⨾ pair) ⨾ (s ⨾ (k ⨾ f~) ⨾ Id) ⨾ zᵣ ⨾ (s ⨾ (k ⨾ g~) ⨾ Id ⨾ zᵣ))
                           ≡⟨ cong (λ x → pr₁ ⨾ (x ⨾ (s ⨾ (k ⨾ g~) ⨾ Id ⨾ zᵣ))) (sabc≡ac_bc _ _ _) ⟩
                         pr₁ ⨾ (k ⨾ pair ⨾ zᵣ ⨾ (s ⨾ (k ⨾ f~) ⨾ Id ⨾ zᵣ) ⨾ (s ⨾ (k ⨾ g~) ⨾ Id ⨾ zᵣ))
                           ≡⟨ cong (λ x → pr₁ ⨾ (x ⨾ (s ⨾ (k ⨾ f~) ⨾ Id ⨾ zᵣ) ⨾ (s ⨾ (k ⨾ g~) ⨾ Id ⨾ zᵣ))) (kab≡a _ _) ⟩
                         pr₁ ⨾ (pair ⨾ (s ⨾ (k ⨾ f~) ⨾ Id ⨾ zᵣ) ⨾ (s ⨾ (k ⨾ g~) ⨾ Id ⨾ zᵣ))
                           ≡⟨ pr₁pxy≡x _ _ ⟩
                         s ⨾ (k ⨾ f~) ⨾ Id ⨾ zᵣ
                           ≡⟨ sabc≡ac_bc _ _ _ ⟩
                         k ⨾ f~ ⨾ zᵣ ⨾ (Id ⨾ zᵣ)
                           ≡⟨ cong (λ x → x ⨾ (Id ⨾ zᵣ)) (kab≡a _ _) ⟩
                         f~ ⨾ (Id ⨾ zᵣ)
                           ≡⟨ cong (λ x → f~ ⨾ x) (Ida≡a _) ⟩
                         f~ ⨾ zᵣ
                           ∎

                 pr₂⨾tracker⨾zᵣ≡g~⨾zᵣ : pr₂ ⨾ (t ⨾ zᵣ) ≡ g~ ⨾ zᵣ
                 pr₂⨾tracker⨾zᵣ≡g~⨾zᵣ =
                         pr₂ ⨾ (s ⨾ (s ⨾ (k ⨾ pair) ⨾ (s ⨾ (k ⨾ f~) ⨾ Id)) ⨾ (s ⨾ (k ⨾ g~) ⨾ Id) ⨾ zᵣ)
                           ≡⟨ cong (λ x → pr₂ ⨾ x) (sabc≡ac_bc _ _ _) ⟩
                         pr₂ ⨾ (s ⨾ (k ⨾ pair) ⨾ (s ⨾ (k ⨾ f~) ⨾ Id) ⨾ zᵣ ⨾ (s ⨾ (k ⨾ g~) ⨾ Id ⨾ zᵣ))
                           ≡⟨ cong (λ x → pr₂ ⨾ (x ⨾ (s ⨾ (k ⨾ g~) ⨾ Id ⨾ zᵣ))) (sabc≡ac_bc _ _ _) ⟩
                         pr₂ ⨾ (k ⨾ pair ⨾ zᵣ ⨾ (s ⨾ (k ⨾ f~) ⨾ Id ⨾ zᵣ) ⨾ (s ⨾ (k ⨾ g~) ⨾ Id ⨾ zᵣ))
                           ≡⟨ cong (λ x → pr₂ ⨾ (x ⨾ (s ⨾ (k ⨾ f~) ⨾ Id ⨾ zᵣ) ⨾ (s ⨾ (k ⨾ g~) ⨾ Id ⨾ zᵣ))) (kab≡a _ _) ⟩
                         pr₂ ⨾ (pair ⨾ (s ⨾ (k ⨾ f~) ⨾ Id ⨾ zᵣ) ⨾ (s ⨾ (k ⨾ g~) ⨾ Id ⨾ zᵣ))
                           ≡⟨ pr₂pxy≡y _ _ ⟩
                         s ⨾ (k ⨾ g~) ⨾ Id ⨾ zᵣ
                           ≡⟨ sabc≡ac_bc _ _ _ ⟩
                         k ⨾ g~ ⨾ zᵣ ⨾ (Id ⨾ zᵣ)
                           ≡⟨ cong (λ x → x ⨾ (Id ⨾ zᵣ)) (kab≡a _ _) ⟩
                         g~ ⨾ (Id ⨾ zᵣ)
                           ≡⟨ cong (λ x → g~ ⨾ x) (Ida≡a _) ⟩
                         g~ ⨾ zᵣ
                           ∎ 
                 goal₁ : (pr₁ ⨾ (t ⨾ zᵣ)) ⊩X (f .map z)
                 goal₁ = subst (λ y → y ⊩X (f .map z)) (sym pr₁⨾tracker⨾zᵣ≡f~⨾zᵣ) (f~tracks z zᵣ zᵣ⊩z)
  
                 goal₂ : (pr₂ ⨾ (t ⨾ zᵣ)) ⊩Y (g .map z)
                 goal₂ = subst (λ y → y ⊩Y (g .map z)) (sym pr₂⨾tracker⨾zᵣ≡g~⨾zᵣ) (g~tracks z zᵣ zᵣ⊩z)
  -- Not sure if this is correct but okay let us see
  infixl 23 _⊕_
  _⊕_ : {A B : Type ℓ} → Assembly A → Assembly B → Assembly (A ⊎ B)
  (as ⊕ bs) .isSetX = isSet⊎ (as .isSetX) (bs .isSetX)
  (as ⊕ bs) ._⊩_ r (inl a) = ∃[ aᵣ ∈ A ] (as ._⊩_ aᵣ a) × (r ≡ pair ⨾ true ⨾ aᵣ)
  (as ⊕ bs) ._⊩_ r (inr b) = ∃[ bᵣ ∈ A ] (bs ._⊩_ bᵣ b) × (r ≡ pair ⨾ false ⨾ bᵣ)
  (as ⊕ bs) .⊩isPropValued r (inl a) = squash₁
  (as ⊕ bs) .⊩isPropValued r (inr b) = squash₁
  (as ⊕ bs) .⊩surjective (inl a) =
                                 do
                                 (a~ , a~realizes) ← as .⊩surjective a
                                 return ( pair ⨾ true ⨾ a~
                                        , ∣ a~
                                        , a~realizes
                                        , refl ∣₁
                                        )
  (as ⊕ bs) .⊩surjective (inr b) =
                                 do
                                 (b~ , b~realizes) ← bs .⊩surjective b
                                 return ( pair ⨾ false ⨾ b~
                                        , ∣ b~
                                        , b~realizes
                                        , refl ∣₁
                                        )
                                        
  κ₁ : {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} → AssemblyMorphism as (as ⊕ bs)
  κ₁ .map = inl
  κ₁ .tracker = ∣ pair ⨾ true , (λ x aₓ aₓ⊩x → ∣ aₓ , aₓ⊩x , refl ∣₁) ∣₁

  κ₂ : {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} → AssemblyMorphism bs (as ⊕ bs)
  κ₂ .map b = inr b
  κ₂ .tracker = ∣ pair ⨾ false , (λ x bₓ bₓ⊩x → ∣ bₓ , bₓ⊩x , refl ∣₁) ∣₁
  module _ {A B : Type ℓ} {as : Assembly A} {bs : Assembly B} (f g : AssemblyMorphism as bs) where
    _⊩A_ = as ._⊩_
    equalizer : Assembly (Σ[ a ∈ A ] f .map a ≡ g .map a)
    equalizer .isSetX = isSetΣ (as .isSetX) λ x → isProp→isSet (bs .isSetX (f .map x) (g .map x))
    equalizer ._⊩_ r (a , fa≡ga) = as ._⊩_ r a
    equalizer .⊩isPropValued r (a , fa≡ga) = as .⊩isPropValued r a
    equalizer .⊩surjective (a , fa≡ga) = as .⊩surjective a

    ιequalizer : AssemblyMorphism equalizer as
    ιequalizer .map (a , fa≡ga) = a
    ιequalizer .tracker = ∣ Id , (λ x aₓ aₓ⊩x → subst (λ y → y ⊩A (x .fst)) (sym (Ida≡a aₓ)) aₓ⊩x) ∣₁

    equalizerFactors : ((Z , zs) : Σ[ Z ∈ Type ℓ ] (Assembly Z))
                     → (ι' : AssemblyMorphism zs as)
                     → (ι' ⊚ f ≡ ι' ⊚ g)
                     → ∃![ univ ∈ AssemblyMorphism zs equalizer ] (univ ⊚ ιequalizer ≡ ι')
    equalizerFactors (Z , zs) ι' ι'f≡ι'g =
                     uniqueExists (λ where
                                     .map z → ι' .map z , λ i → ι'f≡ι'g i .map z
                                     .tracker → {!!})
                                     {!!} {!!} {!!}

  -- Exponential objects
  _⇒_ : {A B : Type ℓ} → (as : Assembly A) → (bs : Assembly B) → Assembly (AssemblyMorphism as bs)
  (as ⇒ bs) .isSetX = isSetAssemblyMorphism as bs
  (as ⇒ bs) ._⊩_ r f = tracks {xs = as} {ys = bs} r (f .map)
  _⇒_ {A} {B} as bs .⊩isPropValued r f = isPropTracks {X = A} {Y = B} {xs = as} {ys = bs}  r (f .map)
  (as ⇒ bs) .⊩surjective f = f .tracker

  -- What a distinguished gentleman
  eval : {X Y : Type ℓ} → (xs : Assembly X) → (ys : Assembly Y) → AssemblyMorphism ((xs ⇒ ys) ⊗ xs) ys
  eval xs ys .map (f , x) = f .map x
  eval {X} {Y} xs ys .tracker =
       ∣(s ⨾ (s ⨾ (k ⨾ pr₁) ⨾ Id) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id))
       , (λ (f , x) r r⊩fx → subst
               (λ y → y ⊩Y (f .map x))
               (sym (tracker⨾r≡pr₁r⨾pr₂r (f , x) r r⊩fx))
               (pr₁r⨾pr₂rTracks (f , x) r r⊩fx))
       ∣₁ where
          _⊩Y_ = ys ._⊩_
          module _ (fx : (AssemblyMorphism xs ys) × X)
                   (r : A)
                   (r⊩fx : ((xs ⇒ ys) ⊗ xs) ._⊩_ r (fx .fst , fx .snd)) where
            f = fx .fst
            x = fx .snd
                          
            pr₁r⨾pr₂rTracks : (pr₁ ⨾ r ⨾ (pr₂ ⨾ r)) ⊩Y (f .map x)
            pr₁r⨾pr₂rTracks = r⊩fx .fst x (pr₂ ⨾ r) (r⊩fx .snd)
                          
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
  -- With major constructions done we start the universal properties
  module _ {X Y : Type ℓ} (xs : Assembly X) (ys : Assembly Y) where
    theπ₁ = π₁ {A = X} {B = Y} {as = xs} {bs = ys}
    theπ₂ = π₂ {A = X} {B = Y} {as = xs} {bs = ys}
    isBinProduct⊗ : ((Z , zs) : Σ[ Z ∈ Type ℓ ] Assembly Z)
                   → (f : AssemblyMorphism zs xs)
                   → (g : AssemblyMorphism zs ys)
                   → ∃![ fg ∈ AssemblyMorphism zs (xs ⊗ ys) ] (fg ⊚ theπ₁ ≡ f) × (fg ⊚ theπ₂ ≡ g)
    isBinProduct⊗ (Z , zs) f g =
                  uniqueExists
                    {B = λ fg → (fg ⊚ theπ₁ ≡ f) × (fg ⊚ theπ₂ ≡ g)}
                    ⟨ f , g ⟩
                    ( AssemblyMorphism≡ (⟨ f , g ⟩ ⊚ theπ₁) f (funExt (λ x → refl))
                    , AssemblyMorphism≡ (⟨ f , g ⟩ ⊚ theπ₂) g (funExt (λ x → refl)))
                    (λ fg → isProp×
                            (isSetAssemblyMorphism zs xs (fg ⊚ theπ₁) f)
                            (isSetAssemblyMorphism zs ys (fg ⊚ theπ₂) g))
                    -- TODO : Come up with a prettier proof
                    λ fg (fgπ₁≡f , fgπ₂≡g) → sym ((lemma₂ fg fgπ₁≡f fgπ₂≡g) ∙ (lemma₁ fg fgπ₁≡f fgπ₂≡g)) where
                      module _ (fg : AssemblyMorphism zs (xs ⊗ ys))
                               (fgπ₁≡f : fg ⊚ theπ₁ ≡ f)
                               (fgπ₂≡g : fg ⊚ theπ₂ ≡ g) where
                             lemma₁ : ⟨ fg ⊚ theπ₁ , fg ⊚ theπ₂ ⟩ ≡ ⟨ f , g ⟩
                             lemma₁ = AssemblyMorphism≡
                                      ⟨ fg ⊚ theπ₁ , fg ⊚ theπ₂ ⟩
                                      ⟨ f , g ⟩
                                      (λ i z → (fgπ₁≡f i .map z) , (fgπ₂≡g i .map z))

                             lemma₂ : fg ≡ ⟨ fg ⊚ theπ₁ , fg ⊚ theπ₂ ⟩
                             lemma₂ = AssemblyMorphism≡
                                      fg
                                      ⟨ fg ⊚ theπ₁ , fg ⊚ theπ₂ ⟩
                                      (funExt λ x → ΣPathP (refl , refl))

  module _ where
    open BinProduct
    ASMBinProducts : BinProducts ASM
    ASMBinProducts (X , xs) (Y , ys) .binProdOb = (X × Y) , (xs ⊗ ys)
    ASMBinProducts (X , xs) (Y , ys) .binProdPr₁ = π₁ {as = xs} {bs = ys}
    ASMBinProducts (X , xs) (Y , ys) .binProdPr₂ = π₂ {as = xs} {bs = ys}
    ASMBinProducts (X , xs) (Y , ys) .univProp {z} f g = isBinProduct⊗ xs ys z f g

  isTerminalUnitAssembly : ((Z , zs) : Σ[ Z ∈ Type ℓ ] (Assembly Z)) →  isContr (AssemblyMorphism zs unitAssembly)
  isTerminalUnitAssembly (Z , zs) =
                         inhProp→isContr (λ where
                                            .map → (λ _ → tt*)
                                            .tracker → ∣ k ⨾ Id , (λ _ _ _ → tt*) ∣₁)
                                          λ f g → AssemblyMorphism≡ f g refl

  ASMTerminal : Terminal ASM
  ASMTerminal = (Unit* , unitAssembly) , isTerminalUnitAssembly

  isInitialUnitAssembly : ((Z , zs) : Σ[ Z ∈ Type ℓ ] (Assembly Z)) → isContr (AssemblyMorphism emptyAssembly zs)
  isInitialUnitAssembly (Z , zs) =
                        inhProp→isContr (λ where
                                           .map → λ () 
                                           .tracker →  ∣ Id , (λ x aₓ aₓ⊩x → rec* x) ∣₁)
                                         λ f g → AssemblyMorphism≡ _ _ (funExt λ x → rec* x)

  ASMInitial : Initial ASM
  ASMInitial = (⊥* , emptyAssembly) , isInitialUnitAssembly

  module _ {X Y Z : Type ℓ}
           {xs : Assembly X}
           {ys : Assembly Y}
           {zs : Assembly Z}
           (f : AssemblyMorphism (zs ⊗ xs) ys) where
         theEval = eval {X} {Y} xs ys
         ⇒isExponential : ∃![ g ∈ AssemblyMorphism (zs ⊗ xs) ((xs ⇒ ys) ⊗ xs) ]
                          (g ⊚ theEval ≡ f)
         ⇒isExponential =
           uniqueExists (λ where
                        .map (z , x) → (((λ where
                                            .map x' → f .map (z , x')
                                            .tracker → {!!})) , x)
                        .tracker → {!!})
                        (AssemblyMorphism≡ _ _ {!!})
                        (λ g' → isSetAssemblyMorphism _ _ (g' ⊚ theEval) f)
                        λ g' g'⊚eval≡f → AssemblyMorphism≡ _ _ (funExt {!!})

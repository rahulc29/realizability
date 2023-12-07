{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Realizability.CombinatoryAlgebra

module Realizability.Assembly.Exponentials {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.BinProducts ca

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
       ∣ (s ⨾ (s ⨾ (k ⨾ pr₁) ⨾ Id) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id))
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

module _ {X Y Z : Type ℓ}
         {xs : Assembly X}
         {ys : Assembly Y}
         {zs : Assembly Z}
         (f : AssemblyMorphism (zs ⊗ xs) ys) where
         theEval = eval {X} {Y} xs ys
         ⇒isExponential : ∃![ g ∈ AssemblyMorphism zs (xs ⇒ ys) ]
                          ⟪ g , identityMorphism xs ⟫ ⊚ theEval ≡ f
         ⇒isExponential = uniqueExists (λ where
                                           .map z → λ where
                                                        .map x → f .map (z , x)
                                                        .tracker → do
                                                                    (f~ , f~tracks) ← f .tracker
                                                                    (z~ , z~realizes) ← zs .⊩surjective z
                                                                    return ( (s ⨾ (k ⨾ f~) ⨾ (s ⨾ (k ⨾ (pair ⨾ z~)) ⨾ Id)
                                                                           , λ x aₓ aₓ⊩x
                                                                           → subst (λ k → k ⊩Y (f .map (z , x)))
                                                                             (sym (eq f~ f~tracks z (z~ , z~realizes) x aₓ aₓ⊩x))
                                                                             (pair⨾z~⨾aₓtracks f~ f~tracks z (z~ , z~realizes) x aₓ aₓ⊩x)))
                                           .tracker → do
                                                       (f~ , f~tracker) ← f .tracker
                                                       -- λ* x. λ* y. f~ ⨾ (pair ⨾ x ⨾ y)
                                                       return ({!!} , (λ z zᵣ zᵣ⊩z x xᵣ xᵣ⊩x → {!!})))
                                        (AssemblyMorphism≡ _ _ (funExt (λ (z , x) → refl)))
                                        (λ g → isSetAssemblyMorphism _ _ (⟪ g , identityMorphism xs ⟫ ⊚ theEval) f)
                                        λ g g×id⊚eval≡f → AssemblyMorphism≡ _ _
                                                          (funExt (λ z → AssemblyMorphism≡ _ _
                                                                         (funExt (λ x → λ i → g×id⊚eval≡f (~ i) .map (z , x))))) where
                         _⊩X_ = xs ._⊩_
                         _⊩Y_ = ys ._⊩_
                         _⊩Z_ = zs ._⊩_
                         _⊩Z×X_ = (zs ⊗ xs) ._⊩_
                         Z×X = Z × X
                         module _ (f~ : A)
                                   (f~tracks : (∀ (zx : Z×X) (r : A) (rRealizes : (r ⊩Z×X zx)) → ((f~ ⨾ r) ⊩Y (f .map zx))))
                                   (z : Z)
                                   (zRealizer : Σ[ z~ ∈ A ] (z~ ⊩Z z))
                                   (x : X)
                                   (aₓ : A)
                                   (aₓ⊩x : aₓ ⊩X x) where
                            z~ : A
                            z~ = zRealizer .fst
                            z~realizes = zRealizer .snd

                            eq : s ⨾ (k ⨾ f~) ⨾ (s ⨾ (k ⨾ (pair ⨾ z~)) ⨾ Id) ⨾ aₓ ≡ f~ ⨾ (pair ⨾ z~ ⨾ aₓ)
                            eq =
                              s ⨾ (k ⨾ f~) ⨾ (s ⨾ (k ⨾ (pair ⨾ z~)) ⨾ Id) ⨾ aₓ
                                ≡⟨ sabc≡ac_bc _ _ _ ⟩
                              (k ⨾ f~ ⨾ aₓ) ⨾ (s ⨾ (k ⨾ (pair ⨾ z~)) ⨾ Id ⨾ aₓ)
                                ≡⟨ cong (λ x → x ⨾ (s ⨾ (k ⨾ (pair ⨾ z~)) ⨾ Id ⨾ aₓ)) (kab≡a f~ aₓ) ⟩
                              f~ ⨾ (s ⨾ (k ⨾ (pair ⨾ z~)) ⨾ Id ⨾ aₓ)
                                ≡⟨ cong (λ x → f~ ⨾ x) (sabc≡ac_bc _ _ _) ⟩
                              f~ ⨾ ((k ⨾ (pair ⨾ z~) ⨾ aₓ) ⨾ (Id ⨾ aₓ))
                                ≡⟨ cong (λ x → f~ ⨾ (x ⨾ (Id ⨾ aₓ))) (kab≡a (pair ⨾ z~) aₓ) ⟩
                              f~ ⨾ (pair ⨾ z~ ⨾ (Id ⨾ aₓ))
                                ≡⟨ cong (λ x → f~ ⨾ (pair ⨾ z~ ⨾ x)) (Ida≡a aₓ) ⟩
                              f~ ⨾ (pair ⨾ z~ ⨾ aₓ)
                                ∎

                            pair⨾z~⨾aₓtracks : (f~ ⨾ (pair ⨾ z~ ⨾ aₓ)) ⊩Y (f .map (z , x))
                            pair⨾z~⨾aₓtracks =
                              f~tracks
                                (z , x)
                                (pair ⨾ z~ ⨾ aₓ)
                                ( (subst (λ y → y ⊩Z z) (sym (pr₁pxy≡x z~ aₓ)) z~realizes)
                                , (subst (λ y → y ⊩X x) (sym (pr₂pxy≡y z~ aₓ)) aₓ⊩x))

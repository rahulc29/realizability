{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sum hiding (map)
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Vec hiding (map)
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinCoproduct
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure

module Realizability.Assembly.BinCoproducts {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open import Realizability.Assembly.Base ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open import Realizability.Assembly.Morphism ca

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

{-# TERMINATING #-}
[_,_] : ∀ {X Y Z : Type ℓ} {asmX : Assembly X} {asmY : Assembly Y} {asmZ : Assembly Z} → (f : AssemblyMorphism asmX asmZ) (g : AssemblyMorphism asmY asmZ) → AssemblyMorphism (asmX ⊕ asmY) asmZ
[ f , g ] .map (inl x) = f .map x
[ f , g ] .map (inr y) = g .map y
[_,_] {asmZ = asmZ} f g .tracker =
  do
    -- these are not considered structurally smaller since these are in the propositional truncation
    (f~ , f~tracks) ← f .tracker
    (g~ , g~tracks) ← g .tracker
    -- if (pr₁ r) then f (pr₂ r) else g (pr₂ r)
    let
      tracker : Term as (suc zero)
      tracker = ` Id ̇ (` pr₁ ̇ (# zero)) ̇ (` f~ ̇ (` pr₂ ̇ (# zero))) ̇ (` g~ ̇ (` pr₂ ̇ (# zero)))
    return
      (λ* tracker ,
        λ { (inl x) r r⊩inl →
                 transport
                   (propTruncIdempotent (asmZ .⊩isPropValued _ _))
                   (do
                     (rₓ , rₓ⊩x , r≡pair⨾true⨾rₓ) ← r⊩inl
                     return
                       (subst
                         (λ r → asmZ ._⊩_ r ([ f , g ] .map (inl x)))
                         (sym
                           (λ* tracker ⨾ r
                             ≡⟨ λ*ComputationRule tracker r ⟩
                            Id ⨾ (pr₁ ⨾ r) ⨾ (f~ ⨾ (pr₂ ⨾ r)) ⨾ (g~ ⨾ (pr₂ ⨾ r))
                             ≡⟨ cong (λ r → Id ⨾ (pr₁ ⨾ r) ⨾ (f~ ⨾ (pr₂ ⨾ r)) ⨾ (g~ ⨾ (pr₂ ⨾ r))) r≡pair⨾true⨾rₓ ⟩
                            Id ⨾ (pr₁ ⨾ (pair ⨾ true ⨾ rₓ)) ⨾ (f~ ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ))) ⨾ (g~ ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ)))
                             ≡⟨ cong (λ x → Id ⨾ x ⨾ (f~ ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ))) ⨾ (g~ ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ)))) (pr₁pxy≡x _ _) ⟩
                            Id ⨾ true ⨾ (f~ ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ))) ⨾ (g~ ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ)))
                             ≡⟨ ifTrueThen _ _ ⟩
                            f~ ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ))
                             ≡⟨ cong (λ x → f~ ⨾ x) (pr₂pxy≡y _ _) ⟩
                            f~ ⨾ rₓ
                               ∎))
                         (f~tracks x rₓ rₓ⊩x)))
          ; (inr y) r r⊩inr →
                 transport
                   (propTruncIdempotent (asmZ .⊩isPropValued _ _))
                   (do
                     (yᵣ , yᵣ⊩y , r≡pair⨾false⨾yᵣ) ← r⊩inr
                     return
                       (subst
                         (λ r → asmZ ._⊩_ r ([ f , g ] .map (inr y)))
                         (sym
                           ((λ* tracker ⨾ r
                             ≡⟨ λ*ComputationRule tracker r ⟩
                            Id ⨾ (pr₁ ⨾ r) ⨾ (f~ ⨾ (pr₂ ⨾ r)) ⨾ (g~ ⨾ (pr₂ ⨾ r))
                             ≡⟨ cong (λ r → Id ⨾ (pr₁ ⨾ r) ⨾ (f~ ⨾ (pr₂ ⨾ r)) ⨾ (g~ ⨾ (pr₂ ⨾ r))) r≡pair⨾false⨾yᵣ ⟩
                            Id ⨾ (pr₁ ⨾ (pair ⨾ false ⨾ yᵣ)) ⨾ (f~ ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ))) ⨾ (g~ ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ)))
                             ≡⟨ cong (λ x → Id ⨾ x ⨾ (f~ ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ))) ⨾ (g~ ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ)))) (pr₁pxy≡x _ _) ⟩
                            Id ⨾ false ⨾ (f~ ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ))) ⨾ (g~ ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ)))
                             ≡⟨ ifFalseElse _ _ ⟩
                            g~ ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ))
                             ≡⟨ cong (λ x → g~ ⨾ x) (pr₂pxy≡y _ _) ⟩
                            g~ ⨾ yᵣ
                               ∎)))
                         (g~tracks y yᵣ yᵣ⊩y))) })

open BinCoproduct
BinCoproductsASM : BinCoproducts ASM
BinCoproductsASM (X , asmX) (Y , asmY) .binCoprodOb = X ⊎ Y , asmX ⊕ asmY
BinCoproductsASM (X , asmX) (Y , asmY) .binCoprodInj₁ = κ₁
BinCoproductsASM (X , asmX) (Y , asmY) .binCoprodInj₂ = κ₂
BinCoproductsASM (X , asmX) (Y , asmY) .univProp {Z , asmZ} f g =
  uniqueExists
    [ f , g ]
    ((AssemblyMorphism≡ _ _ (funExt (λ x → refl))) , (AssemblyMorphism≡ _ _ (funExt (λ y → refl))))
    (λ ! → isProp× (isSetAssemblyMorphism _ _ _ _) (isSetAssemblyMorphism _ _ _ _))
    λ ! (κ₁⊚!≡f , κ₂⊚!≡g) → AssemblyMorphism≡ _ _ (funExt λ { (inl x) i → κ₁⊚!≡f (~ i) .map x ; (inr y) i → κ₂⊚!≡g (~ i) .map y })

-- I have no idea why I did these since this can be derived from the universal property of the coproduct anyway?
module _
  {X Y : Type ℓ}
  (asmX : Assembly X)
  (asmY : Assembly Y)
  where

  asmX+Y = asmX ⊕ asmY
  asmY+X = asmY ⊕ asmX

  X+Y→Y+X : AssemblyMorphism asmX+Y asmY+X
  X+Y→Y+X .map (inl x) = inr x
  X+Y→Y+X .map (inr y) = inl y
  X+Y→Y+X .tracker =
    do
      let
        tracker : Term as 1
        tracker = ` Id ̇ (` pr₁ ̇ # zero) ̇ (` pair ̇ ` false ̇ (` pr₂ ̇ # zero)) ̇ (` pair ̇ ` true ̇ (` pr₂ ̇ # zero))
      return
        ((λ* tracker) ,
         (λ { (inl x) r r⊩inl →
                   transport
                     (propTruncIdempotent (asmY+X .⊩isPropValued (λ* tracker ⨾ r) (inr x)))
                     (do
                       (rₓ , rₓ⊩x , r≡pair⨾true⨾rₓ) ← r⊩inl
                       let
                         λ*trackerEq : λ* tracker ⨾ r ≡ pair ⨾ false ⨾ rₓ
                         λ*trackerEq =
                           λ* tracker ⨾ r
                             ≡⟨ λ*ComputationRule tracker r ⟩
                           Id ⨾ (pr₁ ⨾ r) ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ r))
                             ≡⟨ cong (λ r → Id ⨾ (pr₁ ⨾ r) ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ r))) r≡pair⨾true⨾rₓ ⟩
                           Id ⨾ (pr₁ ⨾ (pair ⨾ true ⨾ rₓ)) ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ))) ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ)))
                             ≡⟨ cong (λ r → Id ⨾ r ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ))) ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ)))) (pr₁pxy≡x _ _) ⟩
                           Id ⨾ true ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ))) ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ)))
                             ≡⟨ ifTrueThen _ _ ⟩
                           pair ⨾ false ⨾ (pr₂ ⨾ (pair ⨾ true ⨾ rₓ))
                             ≡⟨ cong (λ r → pair ⨾ false ⨾ r) (pr₂pxy≡y _ _) ⟩
                           pair ⨾ false ⨾ rₓ
                              ∎
                       return (return (rₓ , subst _ (sym λ*trackerEq) rₓ⊩x , λ*trackerEq)))
            ; (inr y) r r⊩inr →
                    transport
                     (propTruncIdempotent (asmY+X .⊩isPropValued (λ* tracker ⨾ r) (inl y)))
                     (do
                       (yᵣ , yᵣ⊩y , r≡pair⨾false⨾yᵣ) ← r⊩inr
                       let
                         λ*trackerEq : λ* tracker ⨾ r ≡ pair ⨾ true ⨾ yᵣ
                         λ*trackerEq =
                           λ* tracker ⨾ r
                             ≡⟨ λ*ComputationRule tracker r ⟩
                           Id ⨾ (pr₁ ⨾ r) ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ r))
                             ≡⟨ cong (λ r → Id ⨾ (pr₁ ⨾ r) ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ r)) ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ r))) r≡pair⨾false⨾yᵣ ⟩
                           Id ⨾ (pr₁ ⨾ (pair ⨾ false ⨾ yᵣ)) ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ))) ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ)))
                             ≡⟨ cong (λ r → Id ⨾ r ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ))) ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ)))) (pr₁pxy≡x _ _) ⟩
                           Id ⨾ false ⨾ (pair ⨾ false ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ))) ⨾ (pair ⨾ true ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ)))
                             ≡⟨ ifFalseElse _ _ ⟩
                           pair ⨾ true ⨾ (pr₂ ⨾ (pair ⨾ false ⨾ yᵣ))
                             ≡⟨ cong (λ r → pair ⨾ true ⨾ r) (pr₂pxy≡y _ _) ⟩
                           pair ⨾ true ⨾ yᵣ
                              ∎
                       return (return (yᵣ , subst _ (sym λ*trackerEq) yᵣ⊩y , λ*trackerEq))) }))

CatIsoX+Y-Y+X : ∀ {X Y : Type ℓ} → (asmX : Assembly X) (asmY : Assembly Y) →  CatIso ASM (X ⊎ Y , asmX ⊕ asmY) (Y ⊎ X , asmY ⊕ asmX)
CatIsoX+Y-Y+X asmX asmY =
  (X+Y→Y+X asmX asmY) ,
  (isiso
    (X+Y→Y+X asmY asmX)
    (AssemblyMorphism≡ _ _ (funExt (λ { (inl y) → refl ; (inr x) → refl })))
    (AssemblyMorphism≡ _ _ (funExt (λ { (inl x) → refl ; (inr y) → refl }))))
  

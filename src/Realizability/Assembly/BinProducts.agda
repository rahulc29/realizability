{-# OPTIONS --cubical #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Categories.Limits.BinProduct
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure

module Realizability.Assembly.BinProducts {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open CombinatoryAlgebra ca
open Assembly
open AssemblyMorphism

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

⟪_,_⟫ : {X Y Z W : Type ℓ}
        {xs : Assembly X}
        {ys : Assembly Y}
        {zs : Assembly Z}
        {ws : Assembly W}
        (f : AssemblyMorphism xs ys)
        (g : AssemblyMorphism zs ws)
        → AssemblyMorphism (xs ⊗ zs) (ys ⊗ ws)
⟪ f , g ⟫ .map (x , z) = f .map x , g .map z
⟪_,_⟫ {ys = ys} {ws = ws} f g .tracker =
  do
    (f~ , f~⊩isTrackedF) ← f .tracker
    (g~ , g~⊩isTrackedG) ← g .tracker
    let
      realizer : Term as 1
      realizer = ` pair ̇ (` f~ ̇ (` pr₁ ̇ # zero)) ̇ (` g~ ̇ (` pr₂ ̇ # zero))
    return
      (λ* realizer ,
      (λ { (x , z) r (pr₁r⊩x , pr₂r⊩z) →
        subst (λ r' → r' ⊩[ ys ] (f .map x)) (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _)) (f~⊩isTrackedF x (pr₁ ⨾ r) pr₁r⊩x) ,
        subst (λ r' → r' ⊩[ ws ] (g .map z)) (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _)) (g~⊩isTrackedG z (pr₂ ⨾ r) pr₂r⊩z) }))
        
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
⟨_,_⟩ {X} {Y} {Z} {xs} {ys} {zs} f g .tracker =
  do
    (f~ , f~⊩isTrackedF) ← f .tracker
    (g~ , g~⊩isTrackedG) ← g .tracker
    let
      realizer : Term as 1
      realizer = ` pair ̇ (` f~ ̇ # zero) ̇ (` g~ ̇ # zero)
    return
      (λ* realizer ,
      (λ z r r⊩z →
        subst (λ r' → r' ⊩[ xs ] (f .map z)) (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _)) (f~⊩isTrackedF z r r⊩z) ,
        subst (λ r' → r' ⊩[ ys ] (g .map z)) (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _)) (g~⊩isTrackedG z r r⊩z)))
  
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

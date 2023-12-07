{-# OPTIONS --cubical --allow-unsolved-metas #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Categories.Limits.BinProduct
open import Realizability.CombinatoryAlgebra

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
⟪_,_⟫ {ys = ys} {ws = ws} f g .tracker = (do
                      (f~ , f~tracks) ← f .tracker
                      (g~ , g~tracks) ← g .tracker
                      return (s ⨾ (s ⨾ (k ⨾ pair) ⨾ (s ⨾ (k ⨾ f~) ⨾ (s ⨾ (k ⨾ pr₁) ⨾ Id))) ⨾ (s ⨾ (k ⨾ g~) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id))
                             , λ xz r r⊩xz →
                               ( subst (λ y → ys ._⊩_ y (f .map (xz .fst)))
                                 (sym (subst _
                                             (sym (t⨾r≡pair_fg f~ g~ r))
                                             (pr₁pxy≡x (f~ ⨾ (pr₁ ⨾ r)) (g~ ⨾ (pr₂ ⨾ r)))))
                                 (f~tracks (xz .fst) (pr₁ ⨾ r) (r⊩xz .fst)))
                               , subst (λ y → ws ._⊩_ y (g .map (xz .snd)))
                                 (sym (subst _
                                             (sym (t⨾r≡pair_fg f~ g~ r))
                                             (pr₂pxy≡y (f~ ⨾ (pr₁ ⨾ r)) (g~ ⨾ (pr₂ ⨾ r)))))
                                 (g~tracks (xz .snd) (pr₂ ⨾ r) (r⊩xz .snd))))
                               where
                      module _ (f~ g~ r : A) where
                        subf≡fprr : ∀ f pr → (s ⨾ (k ⨾ f) ⨾ (s ⨾ (k ⨾ pr) ⨾ Id) ⨾ r) ≡ (f ⨾ (pr ⨾ r))
                        subf≡fprr f pr =
                                    s ⨾ (k ⨾ f) ⨾ (s ⨾ (k ⨾ pr) ⨾ Id) ⨾ r
                                      ≡⟨ sabc≡ac_bc _ _ _ ⟩
                                    (k ⨾ f ⨾ r) ⨾ (s ⨾ (k ⨾ pr) ⨾ Id ⨾ r)
                                      ≡⟨ cong (λ x → x ⨾ _) (kab≡a f r) ⟩
                                    f ⨾ (s ⨾ (k ⨾ pr) ⨾ Id ⨾ r)
                                      ≡⟨ cong (λ x → f ⨾ x) (sabc≡ac_bc _ _ _) ⟩
                                    f ⨾ (k ⨾ pr ⨾ r ⨾ (Id ⨾ r))
                                      ≡⟨ cong (λ x → f ⨾ (x ⨾ (Id ⨾ r))) (kab≡a _ _ ) ⟩
                                    f ⨾ (pr ⨾ (Id ⨾ r))
                                      ≡⟨ cong (λ x → f ⨾ (pr ⨾ x)) (Ida≡a r) ⟩
                                    f ⨾ (pr ⨾ r)
                                      ∎
                        t⨾r≡pair_fg :
                          s ⨾ (s ⨾ (k ⨾ pair) ⨾ (s ⨾ (k ⨾ f~) ⨾ (s ⨾ (k ⨾ pr₁) ⨾ Id))) ⨾ (s ⨾ (k ⨾ g~) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id)) ⨾ r
                          ≡ pair ⨾ (f~ ⨾ (pr₁ ⨾ r)) ⨾ (g~ ⨾ (pr₂ ⨾ r))
                        t⨾r≡pair_fg =
                          s ⨾ (s ⨾ (k ⨾ pair) ⨾ (s ⨾ (k ⨾ f~) ⨾ (s ⨾ (k ⨾ pr₁) ⨾ Id))) ⨾ (s ⨾ (k ⨾ g~) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id)) ⨾ r
                            ≡⟨ sabc≡ac_bc _ _ _ ⟩
                          s ⨾ (k ⨾ pair) ⨾ (s ⨾ (k ⨾ f~) ⨾ (s ⨾ (k ⨾ pr₁) ⨾ Id)) ⨾ r ⨾ (s ⨾ (k ⨾ g~) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id) ⨾ r)
                            ≡⟨ cong (λ x → x ⨾ (s ⨾ (k ⨾ g~) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id) ⨾ r)) (sabc≡ac_bc _ _ _) ⟩
                          k ⨾ pair ⨾ r ⨾ (s ⨾ (k ⨾ f~) ⨾ (s ⨾ (k ⨾ pr₁) ⨾ Id) ⨾ r) ⨾ (s ⨾ (k ⨾ g~) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id) ⨾ r)
                            ≡⟨ cong (λ x → x ⨾ (s ⨾ (k ⨾ f~) ⨾ (s ⨾ (k ⨾ pr₁) ⨾ Id) ⨾ r) ⨾ (s ⨾ (k ⨾ g~) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id) ⨾ r))
                              (kab≡a pair r) ⟩
                          pair ⨾ (s ⨾ (k ⨾ f~) ⨾ (s ⨾ (k ⨾ pr₁) ⨾ Id) ⨾ r) ⨾ (s ⨾ (k ⨾ g~) ⨾ (s ⨾ (k ⨾ pr₂) ⨾ Id) ⨾ r)
                            ≡⟨ cong₂ (λ x y → pair ⨾ x ⨾ y) (subf≡fprr f~ pr₁) (subf≡fprr g~ pr₂) ⟩
                          pair ⨾ (f~ ⨾ (pr₁ ⨾ r)) ⨾ (g~ ⨾ (pr₂ ⨾ r))
                            ∎
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
⟨_,_⟩ {X} {Y} {Z} {xs} {ys} {zs} f g .tracker = map2 untruncated (f .tracker) (g .tracker) where
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

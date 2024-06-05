open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Category
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Slice
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure
open import Realizability.PropResizing

module Realizability.Modest.UniformFamily {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where


open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Terminal ca
open import Realizability.Assembly.LocallyCartesianClosed ca
open import Realizability.Modest.Base ca

open Assembly
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

UNIMOD : Categoryᴰ ASM (ℓ-suc ℓ) ℓ
Categoryᴰ.ob[ UNIMOD ] (X , asmX) = Σ[ Y ∈ Type ℓ ] Σ[ asmY ∈ Assembly Y ] isModest asmY × AssemblyMorphism asmY asmX
Categoryᴰ.Hom[_][_,_] UNIMOD {X , asmX} {Y , asmY} reindex (V , asmV , isModestAsmV , m) (W , asmW , isModestAsmW , n) = Σ[ reindexᵈ ∈ (AssemblyMorphism asmV asmW) ] m ⊚ reindex ≡ reindexᵈ ⊚ n
Categoryᴰ.idᴰ UNIMOD {X , asmX} {V , asmV , isModestAsmV , m} = (identityMorphism asmV) , (Category.⋆IdR ASM m ∙ sym (Category.⋆IdL ASM m))
Categoryᴰ._⋆ᴰ_ UNIMOD
  {X , asmX} {Y , asmY} {Z , asmZ} {f} {g}
  {U , asmU , isModestU , m} {V , asmV , isModestV , n} {W , asmW , isModestW , o}
  (fᵈ , fᵈcomm) (gᵈ , gᵈcomm) =
    (fᵈ ⊚ gᵈ) ,
    (m ⊚ (f ⊚ g)
      ≡⟨ sym (Category.⋆Assoc ASM m f g) ⟩
    (m ⊚ f) ⊚ g
      ≡⟨ cong (λ x → x ⊚ g) fᵈcomm ⟩
    fᵈ ⊚ n ⊚ g
      ≡⟨ Category.⋆Assoc ASM fᵈ n g ⟩
    fᵈ ⊚ (n ⊚ g)
      ≡⟨ cong (fᵈ ⊚_) gᵈcomm ⟩
    fᵈ ⊚ (gᵈ ⊚ o)
      ≡⟨ sym (Category.⋆Assoc ASM fᵈ gᵈ o) ⟩
    fᵈ ⊚ gᵈ ⊚ o
      ∎)
Categoryᴰ.⋆IdLᴰ UNIMOD {X , asmX} {Y , asmY} {f} {V , asmV , isModestAsmV , m} {W , asmW , isModestAsmW , n} (fᵈ , fᵈcomm) =
  ΣPathPProp (λ fᵈ → isSetAssemblyMorphism asmV asmY _ _) (Category.⋆IdL ASM fᵈ)
Categoryᴰ.⋆IdRᴰ UNIMOD {X , asmX} {Y , asmY} {f} {V , asmV , isModestAsmV , m} {W , asmW , isModestAsmW , n} (fᵈ , fᵈcomm) =
  ΣPathPProp (λ fᵈ → isSetAssemblyMorphism asmV asmY _ _) (Category.⋆IdR ASM fᵈ)
Categoryᴰ.⋆Assocᴰ UNIMOD
  {X , asmX} {Y , asmY} {Z , asmZ} {W , asmW} {f} {g} {h}
  {Xᴰ , asmXᴰ , isModestAsmXᴰ , pX} {Yᴰ , asmYᴰ , isModestAsmYᴰ , pY} {Zᴰ , asmZᴰ , isModestAsmZᴰ , pZ} {Wᴰ , asmWᴰ , isModestAsmWᴰ , pW}
  (fᵈ , fᵈcomm) (gᵈ , gᵈcomm) (hᵈ , hᵈcomm) =
  ΣPathPProp (λ comp → isSetAssemblyMorphism asmXᴰ asmW _ _) (Category.⋆Assoc ASM fᵈ gᵈ hᵈ )
Categoryᴰ.isSetHomᴰ UNIMOD = isSetΣ (isSetAssemblyMorphism _ _) (λ f → isProp→isSet (isSetAssemblyMorphism _ _ _ _))

UniformFamily : {X : Type ℓ} → (asmX : Assembly X) → Type (ℓ-suc ℓ)
UniformFamily {X} asmX = UNIMOD .Categoryᴰ.ob[_] (X , asmX)

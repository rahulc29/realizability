open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Category
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure
open import Realizability.PropResizing

module Realizability.Modest.Base {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A)  where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca

open Assembly
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

module _ {X : Type ℓ} (asmX : Assembly X) where

  isModest : Type _
  isModest = ∀ (x y : X) (a : A) → a ⊩[ asmX ] x → a ⊩[ asmX ] y → x ≡ y

  isPropIsModest : isProp isModest
  isPropIsModest = isPropΠ3 λ x y a → isProp→ (isProp→ (asmX .isSetX x y))

  isUniqueRealized : isModest → ∀ (a : A) → isProp (Σ[ x ∈ X ] (a ⊩[ asmX ] x))
  isUniqueRealized isMod a (x , a⊩x) (y , a⊩y) = Σ≡Prop (λ x' → asmX .⊩isPropValued a x') (isMod x y a a⊩x a⊩y)

ModestSet : Type ℓ → Type (ℓ-suc ℓ)
ModestSet X = Σ[ xs ∈ Assembly X ] isModest xs

MOD : Category (ℓ-suc ℓ) ℓ
MOD = ΣPropCat ASM λ { (X , asmX) → (Lift (isModest asmX)) , (isOfHLevelRespectEquiv 1 (LiftEquiv {A = isModest asmX}) (isPropIsModest asmX)) }

-- Every modest set is isomorphic to a canonically modest set
module Canonical (X : Type ℓ) (asmX : Assembly X) (isModestAsmX : isModest asmX) (resizing : hPropResizing ℓ) where
  open ResizedPowerset resizing
  -- Replace every term of X by it's set of realisers
  realisersOf : X → ℙ A
  realisersOf x a = (a ⊩[ asmX ] x) , (asmX .⊩isPropValued a x)

  resizedRealisersOf : X → 𝓟 A
  resizedRealisersOf x = ℙ→𝓟 A (realisersOf x)

  realiserSet : Type ℓ
  realiserSet = Σ[ P ∈ 𝓟 A ] ∃[ x ∈ X ] P ≡ resizedRealisersOf x

  canonicalModestSet : Assembly realiserSet
  Assembly._⊩_ canonicalModestSet r (P , ∃x) = r ϵ P
  Assembly.isSetX canonicalModestSet = isSetΣ (isSet𝓟 A) (λ P → isProp→isSet isPropPropTrunc)
  Assembly.⊩isPropValued canonicalModestSet r (P , ∃x) = isPropϵ r P
  Assembly.⊩surjective canonicalModestSet (P , ∃x) =
    do
      (x , P≡⊩x) ← ∃x
      (a , a⊩x) ← asmX .⊩surjective x
      return
        (a ,
        (subst
          (λ P → a ϵ P)
          (sym P≡⊩x)
          (subst (λ P → a ∈ P) (sym (compIsIdFunc (realisersOf x))) a⊩x)))
  {-
  isModestCanonicalModestSet : isModest canonicalModestSet
  isModestCanonicalModestSet x y a a⊩x a⊩y =
    Σ≡Prop
      (λ _ → isPropPropTrunc)
      (𝓟≡ (x .fst) (y .fst) (⊆-extensionality (𝓟→ℙ A (x .fst)) (𝓟→ℙ A (y .fst)) ((λ b b⊩x → {!!}) , {!!}))) -}
   
  
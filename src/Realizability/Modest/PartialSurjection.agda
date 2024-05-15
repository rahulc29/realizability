open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Foundations.Univalence
open import Cubical.Functions.Surjection
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Reflection.RecordEquiv
open import Cubical.Categories.Category
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure
open import Realizability.PropResizing

module Realizability.Modest.PartialSurjection {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) (resizing : hPropResizing ℓ) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Modest.Base ca resizing

open Assembly
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open ResizedPowerset resizing

record PartialSurjection (X : Type ℓ) : Type (ℓ-suc ℓ) where
  no-eta-equality
  constructor makePartialSurjection
  field
    support : A → Type ℓ
    enumeration : Σ[ a ∈ A ] (support a) → X
    isPropSupport : ∀ a → isProp (support a)
    isSurjectionEnumeration : isSurjection enumeration
    isSetX : isSet X -- potentially redundant?
open PartialSurjection

-- let us derive a structure of identity principle for partial surjections
module _ (X : Type ℓ) where

  PartialSurjection≡Iso :
    ∀ (p q : PartialSurjection X)
    → Iso
      (Σ[ suppPath ∈ p .support ≡ q .support ]
      PathP (λ i → Σ[ a ∈ A ] (suppPath i a) → X) (p .enumeration) (q .enumeration))
      (p ≡ q)
  support (Iso.fun (PartialSurjection≡Iso p q) (suppPath , enumPath) i) z = suppPath i z
  enumeration (Iso.fun (PartialSurjection≡Iso p q) (suppPath , enumPath) i) (a , enum) = enumPath i (a , enum)
  isPropSupport (Iso.fun (PartialSurjection≡Iso p q) (suppPath , enumPath) i) z =
    isProp→PathP {B = λ j → isProp (suppPath j z)} (λ j → isPropIsProp) (p .isPropSupport z) (q .isPropSupport z) i
  isSurjectionEnumeration (Iso.fun (PartialSurjection≡Iso p q) (suppPath , enumPath) i) b =
    isProp→PathP
      {B = λ j → ∥ fiber (enumeration (Iso.fun (PartialSurjection≡Iso p q) (suppPath , enumPath) j)) b ∥₁}
      (λ j → isPropPropTrunc)
      (p .isSurjectionEnumeration b) (q .isSurjectionEnumeration b) i
  isSetX (Iso.fun (PartialSurjection≡Iso p q) (suppPath , enumPath) i) = isPropIsSet (p .isSetX) (q .isSetX) i
  Iso.inv (PartialSurjection≡Iso p q) p≡q = (λ i → p≡q i .support) , (λ i → p≡q i .enumeration)
  Iso.rightInv (PartialSurjection≡Iso p q) p≡q = {!!}
  Iso.leftInv (PartialSurjection≡Iso p q) (suppPath , enumPath) = ΣPathP (refl , refl)

  PartialSurjection≡ : ∀ (p q : PartialSurjection X) → Σ[ suppPath ∈ p .support ≡ q .support ] PathP (λ i → Σ[ a ∈ A ] (suppPath i a) → X) (p .enumeration) (q .enumeration) → p ≡ q
  PartialSurjection≡ p q (suppPath , enumPath) = Iso.fun (PartialSurjection≡Iso p q) (suppPath , enumPath)

-- the type of partial surjections is equivalent to the type of modest assemblies on X
module _ (X : Type ℓ) where

  {-# TERMINATING #-}
  ModestSet→PartialSurjection : ModestSet X → PartialSurjection X
  support (ModestSet→PartialSurjection (xs , isModestXs)) r = ∃[ x ∈ X ] (r ⊩[ xs ] x)
  enumeration (ModestSet→PartialSurjection (xs , isModestXs)) (r , ∃x) =
    let
      answer : Σ[ x ∈ X ] (r ⊩[ xs ] x)
      answer = PT.rec (isUniqueRealised xs isModestXs r) (λ t → t) ∃x
    in fst answer
  isPropSupport (ModestSet→PartialSurjection (xs , isModestXs)) r = isPropPropTrunc
  isSurjectionEnumeration (ModestSet→PartialSurjection (xs , isModestXs)) x =
    do
      (a , a⊩x) ← xs .⊩surjective x
      return ((a , ∣ x , a⊩x ∣₁) , refl)
  isSetX (ModestSet→PartialSurjection (xs , isModestXs)) = xs .isSetX

  PartialSurjection→ModestSet : PartialSurjection X → ModestSet X
  Assembly._⊩_ (fst (PartialSurjection→ModestSet surj)) r x =
    Σ[ s ∈ surj .support r ] surj .enumeration (r , s) ≡ x
  Assembly.isSetX (fst (PartialSurjection→ModestSet surj)) = surj .isSetX
  Assembly.⊩isPropValued (fst (PartialSurjection→ModestSet surj)) a x (s , ≡x) (t , ≡x') =
    Σ≡Prop (λ u → surj .isSetX (surj .enumeration (a , u)) x) (surj .isPropSupport a s t)
  Assembly.⊩surjective (fst (PartialSurjection→ModestSet surj)) x =
    do
      ((a , s) , ≡x) ← surj .isSurjectionEnumeration x
      return (a , (s , ≡x))
  snd (PartialSurjection→ModestSet surj) x y r (s , ≡x) (t , ≡x') =
    x
      ≡⟨ sym ≡x ⟩
    surj .enumeration (r , s)
      ≡⟨ cong (λ s → surj .enumeration (r , s)) (surj .isPropSupport r s t) ⟩
    surj .enumeration (r , t)
      ≡⟨ ≡x' ⟩
    y
      ∎

  opaque
    rightInv : ∀ surj → ModestSet→PartialSurjection (PartialSurjection→ModestSet surj) ≡ surj
    rightInv surj =
      PartialSurjection≡
        X (ModestSet→PartialSurjection (PartialSurjection→ModestSet surj)) surj
        (funExt supportEq ,
        funExtDep
          {A = λ i → Σ-syntax A (funExt supportEq i)}
          {B = λ _ _ → X}
          {f = ModestSet→PartialSurjection (PartialSurjection→ModestSet surj) .enumeration}
          {g = surj .enumeration}
          λ { {r , ∃x} {s , supp} p →
            PT.elim
              {P = λ ∃x → fst
                             (PT.rec
                              (isUniqueRealised (fst (PartialSurjection→ModestSet surj))
                               (snd (PartialSurjection→ModestSet surj)) r)
                              (λ t → t) ∃x)
                          ≡ surj .enumeration (s , supp)}
             (λ ∃x → surj .isSetX _ _)
             (λ { (x , r⊩x) →
               let
                 ∃x' = transport (sym (supportEq s)) supp
               in
               equivFun
                 (propTruncIdempotent≃ {!!})
                 (do
                   (x' , suppS , ≡x') ← ∃x'
                   return {!!}) })
             ∃x }) where
          supportEq : ∀ r → (∃[ x ∈ X ] (Σ[ supp ∈ surj .support r ] (surj .enumeration (r , supp) ≡ x))) ≡ support surj r
          supportEq =
              (λ r →
                hPropExt
                isPropPropTrunc
                (surj .isPropSupport r)
                (λ ∃x → PT.rec (surj .isPropSupport r) (λ { (x , supp , ≡x) → supp }) ∃x)
                (λ supp → return (surj .enumeration (r , supp) , supp , refl)))

  IsoModestSetPartialSurjection : Iso (ModestSet X) (PartialSurjection X)
  Iso.fun IsoModestSetPartialSurjection = ModestSet→PartialSurjection
  Iso.inv IsoModestSetPartialSurjection = PartialSurjection→ModestSet
  Iso.rightInv IsoModestSetPartialSurjection = rightInv 
  Iso.leftInv IsoModestSetPartialSurjection mod = {!!}

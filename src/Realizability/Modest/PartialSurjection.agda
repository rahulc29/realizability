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
open import Realizability.Assembly.SIP ca
open import Realizability.Modest.Base ca

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

module _ (X : Type ℓ) (isCorrectHLevel : isSet X) where
  -- first we need a Σ type equivalent to partial surjections
  -- we could use RecordEquiv but this does not give hProps and hSets and
  -- that causes problems when trying to compute the hlevel

  PartialSurjectionΣ : Type (ℓ-suc ℓ)
  PartialSurjectionΣ = Σ[ support ∈ (A → hProp ℓ) ] Σ[ enumeration ∈ ((Σ[ a ∈ A ] ⟨ support a ⟩) → X) ] isSurjection enumeration × isSet X

  isSetPartialSurjectionΣ : isSet PartialSurjectionΣ
  isSetPartialSurjectionΣ = isSetΣ (isSet→ isSetHProp) (λ support → isSetΣ (isSet→ isCorrectHLevel) (λ enum → isSet× (isProp→isSet isPropIsSurjection) (isProp→isSet isPropIsSet)))

  PartialSurjectionIsoΣ : Iso (PartialSurjection X) PartialSurjectionΣ
  Iso.fun PartialSurjectionIsoΣ surj =
    (λ a → (surj .support a) , (surj .isPropSupport a)) ,
    (λ { (a , suppA) → surj .enumeration (a , suppA) }) ,
    surj .isSurjectionEnumeration ,
    PartialSurjection.isSetX surj
  Iso.inv PartialSurjectionIsoΣ (support , enumeration , isSurjectionEnumeration , isSetX) =
    makePartialSurjection (λ a → ⟨ support a ⟩) enumeration (λ a → str (support a)) isSurjectionEnumeration isSetX
  Iso.rightInv PartialSurjectionIsoΣ (support , enumeration , isSurjectionEnumeration , isSetX) = refl
  support (Iso.leftInv PartialSurjectionIsoΣ surj i) a = surj .support a
  enumeration (Iso.leftInv PartialSurjectionIsoΣ surj i) (a , suppA) = surj .enumeration (a , suppA)
  isPropSupport (Iso.leftInv PartialSurjectionIsoΣ surj i) a = surj .isPropSupport a
  isSurjectionEnumeration (Iso.leftInv PartialSurjectionIsoΣ surj i) = surj .isSurjectionEnumeration
  isSetX (Iso.leftInv PartialSurjectionIsoΣ surj i) = surj .isSetX

  PartialSurjection≡Σ : PartialSurjection X ≡ PartialSurjectionΣ
  PartialSurjection≡Σ = isoToPath PartialSurjectionIsoΣ

  isSetPartialSurjection : isSet (PartialSurjection X)
  isSetPartialSurjection = subst isSet (sym PartialSurjection≡Σ) isSetPartialSurjectionΣ

-- let us derive a structure of identity principle for partial surjections
module SIP (X : Type ℓ) (isCorrectHLevel : isSet X) where

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
  Iso.rightInv (PartialSurjection≡Iso p q) p≡q = isSetPartialSurjection X isCorrectHLevel _ _ _ _ 
  Iso.leftInv (PartialSurjection≡Iso p q) (suppPath , enumPath) = ΣPathP (refl , refl)

  PartialSurjection≡ : ∀ (p q : PartialSurjection X) → Σ[ suppPath ∈ p .support ≡ q .support ] PathP (λ i → Σ[ a ∈ A ] (suppPath i a) → X) (p .enumeration) (q .enumeration) → p ≡ q
  PartialSurjection≡ p q (suppPath , enumPath) = Iso.fun (PartialSurjection≡Iso p q) (suppPath , enumPath)

-- the type of partial surjections is equivalent to the type of modest assemblies on X
module ModestSetIso (X : Type ℓ) (isCorrectHLevel : isSet X) where

  open SIP X isCorrectHLevel

  {-# TERMINATING #-}
  ModestSet→PartialSurjection : ModestSet X → PartialSurjection X
  support (ModestSet→PartialSurjection (xs , isModestXs)) r = ∃[ x ∈ X ] (r ⊩[ xs ] x)
  enumeration (ModestSet→PartialSurjection (xs , isModestXs)) (r , ∃x) =
    let
      answer : Σ[ x ∈ X ] (r ⊩[ xs ] x)
      answer = PT.rec (isUniqueRealized xs isModestXs r) (λ t → t) ∃x
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
        (ModestSet→PartialSurjection (PartialSurjection→ModestSet surj)) surj
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
                              (isUniqueRealized (fst (PartialSurjection→ModestSet surj))
                               (snd (PartialSurjection→ModestSet surj)) r)
                              (λ t → t) ∃x)
                          ≡ surj .enumeration (s , supp)}
             (λ ∃x → surj .isSetX _ _)
             (λ { (x , suppR , ≡x) →
               let
                 ∃x' = transport (sym (supportEq s)) supp
                 r≡s : r ≡ s
                 r≡s = PathPΣ p .fst
               in
               equivFun
                 (propTruncIdempotent≃ (surj .isSetX x (surj .enumeration (s , supp))))
                 (do
                   (x' , suppS , ≡x') ← ∃x'
                   return
                     (x
                       ≡⟨ sym ≡x ⟩
                     surj .enumeration (r , suppR)
                       ≡⟨ cong (surj .enumeration) (ΣPathP (r≡s , (isProp→PathP (λ i → surj .isPropSupport (PathPΣ p .fst i)) suppR supp))) ⟩
                     surj .enumeration (s , supp)
                       ∎)) })
             ∃x }) where
          supportEq : ∀ r → (∃[ x ∈ X ] (Σ[ supp ∈ surj .support r ] (surj .enumeration (r , supp) ≡ x))) ≡ support surj r
          supportEq =
              (λ r →
                hPropExt
                isPropPropTrunc
                (surj .isPropSupport r)
                (λ ∃x → PT.rec (surj .isPropSupport r) (λ { (x , supp , ≡x) → supp }) ∃x)
                (λ supp → return (surj .enumeration (r , supp) , supp , refl)))

  leftInv : ∀ mod → PartialSurjection→ModestSet (ModestSet→PartialSurjection mod) ≡ mod
  leftInv (asmX , isModestAsmX) =
    Σ≡Prop
      isPropIsModest
      (Assembly≡ _ _
        λ r x →
          hPropExt
            (isPropΣ isPropPropTrunc (λ ∃x → asmX .isSetX _ _))
            (asmX .⊩isPropValued r x)
            (λ { (∃x , ≡x) →
              let
                (x' , r⊩x') = PT.rec (isUniqueRealized asmX isModestAsmX r) (λ t → t) ∃x
              in subst (λ x' → r ⊩[ asmX ] x') ≡x r⊩x'})
            λ r⊩x → ∣ x , r⊩x ∣₁ , refl)

  IsoModestSetPartialSurjection : Iso (ModestSet X) (PartialSurjection X)
  Iso.fun IsoModestSetPartialSurjection = ModestSet→PartialSurjection
  Iso.inv IsoModestSetPartialSurjection = PartialSurjection→ModestSet
  Iso.rightInv IsoModestSetPartialSurjection = rightInv 
  Iso.leftInv IsoModestSetPartialSurjection = leftInv

record PartialSurjectionMorphism {X Y : Type ℓ} (psX : PartialSurjection X) (psY : PartialSurjection Y) : Type ℓ where
  no-eta-equality
  constructor makePartialSurjectionMorphism
  field
    map : X → Y
    {-
      The following "diagram" commutes
                              
      Xˢ -----------> X
      |              |
      |              |
      |              |
      |              |
      |              |
      ↓              ↓
      Yˢ -----------> Y
    -}
    isTracked : ∃[ t ∈ A ] (∀ (a : A) (sᵃ : psX .support a) → Σ[ sᵇ ∈ (psY .support (t ⨾ a)) ] map (psX .enumeration (a , sᵃ)) ≡ psY .enumeration ((t ⨾ a) , sᵇ))
open PartialSurjectionMorphism

unquoteDecl PartialSurjectionMorphismIsoΣ = declareRecordIsoΣ PartialSurjectionMorphismIsoΣ (quote PartialSurjectionMorphism)

PartialSurjectionMorphismΣ : {X Y : Type ℓ} (psX : PartialSurjection X) (psY : PartialSurjection Y) → Type ℓ
PartialSurjectionMorphismΣ {X} {Y} psX psY =
  Σ[ f ∈ (X → Y) ] ∃[ t ∈ A ] ((∀ (a : A) (sᵃ : psX .support a) → Σ[ sᵇ ∈ (psY .support (t ⨾ a)) ] f (psX .enumeration (a , sᵃ)) ≡ psY .enumeration ((t ⨾ a) , sᵇ)))

isSetPartialSurjectionMorphismΣ : {X Y : Type ℓ} (psX : PartialSurjection X) (psY : PartialSurjection Y) → isSet (PartialSurjectionMorphismΣ psX psY)
isSetPartialSurjectionMorphismΣ {X} {Y} psX psY = isSetΣ (isSet→ (psY .isSetX)) (λ f → isProp→isSet isPropPropTrunc)

PartialSurjectionMorphismΣ≡ : {X Y : Type ℓ} (psX : PartialSurjection X) (psY : PartialSurjection Y) → PartialSurjectionMorphism psX psY ≡ PartialSurjectionMorphismΣ psX psY
PartialSurjectionMorphismΣ≡ {X} {Y} psX psY = isoToPath PartialSurjectionMorphismIsoΣ

isSetPartialSurjectionMorphism : {X Y : Type ℓ} (psX : PartialSurjection X) (psY : PartialSurjection Y) → isSet (PartialSurjectionMorphism psX psY)
isSetPartialSurjectionMorphism {X} {Y} psX psY = subst isSet (sym (PartialSurjectionMorphismΣ≡ psX psY)) (isSetPartialSurjectionMorphismΣ psX psY)

-- SIP
module MorphismSIP {X Y : Type ℓ} (psX : PartialSurjection X) (psY : PartialSurjection Y) where
  open PartialSurjectionMorphism
  PartialSurjectionMorphism≡Iso : ∀ (f g : PartialSurjectionMorphism psX psY) → Iso (f ≡ g) (f .map ≡ g .map)
  Iso.fun (PartialSurjectionMorphism≡Iso f g) f≡g i = f≡g i .map
  map (Iso.inv (PartialSurjectionMorphism≡Iso f g) fMap≡gMap i) = fMap≡gMap i
  isTracked (Iso.inv (PartialSurjectionMorphism≡Iso f g) fMap≡gMap i) =
    isProp→PathP
      -- Agda can't infer the type B
      {B = λ j → ∃-syntax A
      (λ t →
         (a : A) (sᵃ : psX .support a) →
         Σ-syntax (psY .support (t ⨾ a))
         (λ sᵇ →
            fMap≡gMap j (psX .enumeration (a , sᵃ)) ≡
            psY .enumeration (t ⨾ a , sᵇ)))}
      (λ j → isPropPropTrunc)
      (f .isTracked) (g .isTracked) i
  Iso.rightInv (PartialSurjectionMorphism≡Iso f g) fMap≡gMap = refl
  Iso.leftInv (PartialSurjectionMorphism≡Iso f g) f≡g = isSetPartialSurjectionMorphism psX psY f g _ _

  PartialSurjectionMorphism≡ : ∀ {f g : PartialSurjectionMorphism psX psY} → (f .map ≡ g .map) → f ≡ g
  PartialSurjectionMorphism≡ {f} {g} fMap≡gMap = Iso.inv (PartialSurjectionMorphism≡Iso f g) fMap≡gMap

-- morphisms between partial surjections are equivalent to assembly morphisms between corresponding modest assemblies
module
  _
  {X Y : Type ℓ}
  (psX : PartialSurjection X)
  (psY : PartialSurjection Y) where
  open ModestSetIso 
  open MorphismSIP psX psY

  asmX = PartialSurjection→ModestSet X (psX .isSetX) psX .fst
  isModestAsmX = PartialSurjection→ModestSet X (psX .isSetX) psX .snd

  asmY = PartialSurjection→ModestSet Y (psY .isSetX) psY .fst
  isModestAsmY = PartialSurjection→ModestSet Y (psY .isSetX) psY .snd

  partialSurjectionHomModestSetHomIso : Iso (AssemblyMorphism asmX asmY) (PartialSurjectionMorphism psX psY)
  map (Iso.fun partialSurjectionHomModestSetHomIso asmHom) = asmHom .map
  isTracked (Iso.fun partialSurjectionHomModestSetHomIso asmHom) =
    do
      (map~ , isTrackedMap) ← asmHom .tracker
      return
        (map~ ,
         λ a aSuppX →
           let
             worker : (map~ ⨾ a) ⊩[ asmY ] (asmHom .map (psX .enumeration (a , aSuppX)))
             worker = isTrackedMap (psX .enumeration (a , aSuppX)) a (aSuppX , refl)
           in
           (worker .fst) ,
           (sym (worker .snd)))
  AssemblyMorphism.map (Iso.inv partialSurjectionHomModestSetHomIso surjHom) = surjHom .map
  AssemblyMorphism.tracker (Iso.inv partialSurjectionHomModestSetHomIso surjHom) =
    do
      (t , isTrackedMap) ← surjHom .isTracked
      return
        (t ,
        (λ { x a (aSuppX , ≡x) →
          (isTrackedMap a aSuppX .fst) ,
          (sym (cong (surjHom .map) (sym ≡x) ∙ isTrackedMap a aSuppX .snd)) }))
  Iso.rightInv partialSurjectionHomModestSetHomIso surjHom = PartialSurjectionMorphism≡ refl
  Iso.leftInv partialSurjectionHomModestSetHomIso asmHom = AssemblyMorphism≡ _ _ refl

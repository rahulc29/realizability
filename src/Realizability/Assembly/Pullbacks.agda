open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.HITs.PropositionalTruncation hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Slice
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure

module Realizability.Assembly.Pullbacks {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a) hiding (Z)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca

module _ (cspn : Cospan ASM) where
  open Cospan cspn

  X  = l .fst
  xs = l .snd

  Y  = m .fst
  ys = m .snd

  Z  = r .fst
  zs = r .snd

  f = s₁
  g = s₂

  opaque
    pullbackType : Type ℓ
    pullbackType = (Σ[ x ∈ X ] Σ[ z ∈ Z ] (f .map x ≡ g .map z))

  opaque
    unfolding pullbackType
    pullbackAsm : Assembly pullbackType
    Assembly._⊩_ pullbackAsm = λ { r (x , z , fx≡gz) → (pr₁ ⨾ r) ⊩[ xs ] x × ((pr₂ ⨾ r) ⊩[ zs ] z) }
    Assembly.isSetX pullbackAsm = isSetΣ (xs .isSetX) (λ _ → isSetΣ (zs .isSetX) (λ _ → isProp→isSet (ys .isSetX _ _)))
    Assembly.⊩isPropValued pullbackAsm = λ { r (x , z , fx≡gz) → isProp× (xs .⊩isPropValued _ _) (zs .⊩isPropValued _ _) }
    Assembly.⊩surjective pullbackAsm =
      (λ { (x , z , fx≡gz) →
        do
          (a , a⊩x) ← xs .⊩surjective x
          (b , b⊩z) ← zs .⊩surjective z
          return
            (pair ⨾ a ⨾ b ,
             subst (λ r' → r' ⊩[ xs ] x) (sym (pr₁pxy≡x _ _)) a⊩x ,
             subst (λ r' → r' ⊩[ zs ] z) (sym (pr₂pxy≡y _ _)) b⊩z) })

  opaque
    unfolding pullbackType
    unfolding pullbackAsm
    pullbackPr₁ : AssemblyMorphism pullbackAsm xs
    AssemblyMorphism.map pullbackPr₁ (x , z , fx≡gz) = x
    AssemblyMorphism.tracker pullbackPr₁ =
      return (pr₁ , (λ { (x , z , fx≡gz) r (pr₁r⊩x , pr₂r⊩z) → pr₁r⊩x }))

  opaque
    unfolding pullbackType
    unfolding pullbackAsm
    pullbackPr₂ : AssemblyMorphism pullbackAsm zs
    AssemblyMorphism.map pullbackPr₂ (x , z , fx≡gz) = z
    AssemblyMorphism.tracker pullbackPr₂ =
      return (pr₂ , (λ { (x , z , fx≡gz) r (pr₁r⊩x , pr₂r⊩z) → pr₂r⊩z }))

  opaque
    unfolding pullbackAsm
    unfolding pullbackPr₁
    unfolding pullbackPr₂
    pullback : Pullback ASM cspn
    Pullback.pbOb pullback = pullbackType , pullbackAsm
    Pullback.pbPr₁ pullback = pullbackPr₁
    Pullback.pbPr₂ pullback = pullbackPr₂
    Pullback.pbCommutes pullback = AssemblyMorphism≡ _ _ (funExt λ { (x , z , fx≡gz) → fx≡gz })
    Pullback.univProp pullback {D , ds} p q pf≡qg =
      uniqueExists
        uniqueMorphism
        ((AssemblyMorphism≡ _ _ (funExt (λ d → refl))) , (AssemblyMorphism≡ _ _ (funExt (λ d → refl))))
        (λ !' → isProp× (isSetAssemblyMorphism _ _ p (!' ⊚ pullbackPr₁)) (isSetAssemblyMorphism _ _ q (!' ⊚ pullbackPr₂)))
        λ { !' (p≡!'*pr₁ , q≡!'*pr₂) →
          AssemblyMorphism≡
            _ _
            (funExt
              λ d →
                ΣPathP
                  ((λ i → p≡!'*pr₁ i .map d) ,
                    ΣPathPProp
                      {u = q .map d , λ i → pf≡qg i .map d}
                      {v = !' .map d .snd}
                      (λ z → ys .isSetX _ _)
                      λ i → q≡!'*pr₂ i .map d)) }
        where
        uniqueMap : D → pullbackType
        uniqueMap d = p .map d , q .map d , λ i → pf≡qg i .map d

        uniqueMorphism : AssemblyMorphism ds pullbackAsm
        uniqueMorphism =
          (makeAssemblyMorphism
            uniqueMap
            (do
              (p~ , isTrackedP) ← p .tracker
              (q~ , isTrackedQ) ← q .tracker
              let
                realizer : Term as 1
                realizer = ` pair ̇ (` p~ ̇ # zero) ̇ (` q~ ̇ # zero)
              return
                (λ* realizer ,
                 λ d r r⊩d →
                   subst (λ r' → r' ⊩[ xs ] (p .map d)) (sym (cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₁pxy≡x _ _)) (isTrackedP d r r⊩d) ,
                   subst (λ r' → r' ⊩[ zs ] (q .map d)) (sym (cong (λ x → pr₂ ⨾ x) (λ*ComputationRule realizer r) ∙ pr₂pxy≡y _ _)) (isTrackedQ d r r⊩d))))

PullbacksASM : Pullbacks ASM
PullbacksASM cspn = pullback cspn

-- Using pullbacks we get a functor that sends any f : X → Y to f* : Asm / Y → Asm / X
module _ {X Y : Type ℓ} (asmX : Assembly X) (asmY : Assembly Y) (f : AssemblyMorphism asmX asmY) where
  open Pullback
  opaque
    unfolding pullbackAsm
    unfolding pullbackPr₁
    unfolding pullback
    pullbackFunctor : Functor (SliceCat ASM (Y , asmY)) (SliceCat ASM (X , asmX))
    Functor.F-ob pullbackFunctor sliceY = sliceob (pullback (cospan (X , asmX) (Y , asmY) (sliceY .S-ob) f (sliceY .S-arr)) .pbPr₁)
    Functor.F-hom pullbackFunctor {ySliceA} {ySliceB} sliceHomAB =
      {-let
        sliceACospan : Cospan ASM
        sliceACospan = cospan (X , asmX) (Y , asmY) (ySliceA .S-ob) f (ySliceA .S-arr)
        p = pullbackPr₂ sliceACospan
        m = ySliceA .S-arr
        n = ySliceB .S-arr
        f*m = pullbackPr₁ sliceACospan
        h = sliceHomAB .S-hom
        m≡h⊚n = sliceHomAB .S-comm
        f*m⊚f≡p⊚m = pbCommutes (pullback sliceACospan)
        arrow =
          pullbackArrow
            ASM
            (pullback (cospan (X , asmX) (Y , asmY) (ySliceB .S-ob) f (ySliceB .S-arr))) (pullbackPr₁ sliceACospan) (p ⊚ h)
            (AssemblyMorphism≡ _ _
              (funExt
                λ { (x , a , fx≡ma) →
                  f .map x
                    ≡⟨ fx≡ma ⟩
                  m .map a
                    ≡[ i ]⟨ m≡h⊚n (~ i) .map a ⟩
                  n .map (h .map a)
                    ∎ }))
      in
      slicehom
        arrow-}
        {!!}
    Functor.F-id pullbackFunctor = {!!}
    Functor.F-seq pullbackFunctor = {!!}

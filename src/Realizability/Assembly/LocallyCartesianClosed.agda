open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Vec hiding (map)
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Slice
open import Cubical.Categories.Adjoint
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure
open import Categories.PullbackFunctor

module Realizability.Assembly.LocallyCartesianClosed {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a) hiding (Z)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.Assembly.Pullbacks ca
open import Realizability.Assembly.Reindexing ca
open NaturalBijection
open SliceOb

module _ {X Y : Type ℓ} {asmX : Assembly X} {asmY : Assembly Y} (f : AssemblyMorphism asmX asmY) where
  module SliceDomain {V : Type ℓ} {asmV : Assembly V} (h : AssemblyMorphism asmV asmX) where
    
    D : Type ℓ
    D = Σ[ y ∈ Y ] Σ[ s ∈ (fiber (f .map) y → V)] (∀ (yFiberF : fiber (f .map) y) → h .map (s yFiberF) ≡ yFiberF .fst)

    isSetD : isSet D
    isSetD =
      isSetΣ
        (asmY .isSetX)
        (λ y →
          isSetΣ
            (isSet→ (asmV .isSetX))
            (λ s →
              isSetΠ λ yFiberF → isProp→isSet (asmX .isSetX _ _)))

    _⊩D_ : A → D → Type ℓ
    r ⊩D (y , s , coh) = ((pr₁ ⨾ r) ⊩[ asmY ] y) × (∀ (yFiberF : fiber (f .map) y) (a : A) → a ⊩[ asmX ] (yFiberF .fst) → (pr₂ ⨾ r ⨾ a) ⊩[ asmV ] (s yFiberF))

    isProp⊩D : ∀ r d → isProp (r ⊩D d)
    isProp⊩D r d =
      isProp×
        (asmY .⊩isPropValued _ _)
        (isPropΠ
          λ yFiberF →
            isPropΠ
              λ a →
                isProp→ (asmV .⊩isPropValued _ _))

    asmD : Assembly (Σ[ d ∈ D ] ∃[ r ∈ A ] (r ⊩D d))
    Assembly._⊩_ asmD r (d@(y , s , coh) , ∃r) = r ⊩D d
    Assembly.isSetX asmD = isSetΣ isSetD (λ d → isProp→isSet isPropPropTrunc)
    Assembly.⊩isPropValued asmD r (d@(y , s , coh) , ∃a) = isProp⊩D r d
    Assembly.⊩surjective asmD (d , ∃a) = ∃a

    projection : AssemblyMorphism asmD asmY
    AssemblyMorphism.map projection (d@(y , s , coh) , ∃r) = y
    AssemblyMorphism.tracker projection =
        return
          (pr₁ ,
          (λ { (d@(y , s , coh) , ∃a) r r⊩d → r⊩d .fst }))

  private module SliceDomainHom {V W : Type ℓ} {asmV : Assembly V} {asmW : Assembly W} (g : AssemblyMorphism asmV asmX) (h : AssemblyMorphism asmW asmX) (j : AssemblyMorphism asmV asmW) (comm : j ⊚ h ≡ g) where
    
    rawMap : SliceDomain.D g → SliceDomain.D h
    rawMap (y , s , coh) =
      y ,
      (λ fib → j .map (s fib)) ,
      λ { fib@(x , fx≡y) →
        h .map (j .map (s fib))
          ≡[ i ]⟨ comm i .map (s fib) ⟩
        g .map (s fib)
          ≡⟨ coh fib ⟩
        x
          ∎ }

    transformRealizers : ∀ (d : SliceDomain.D g) → Σ[ b ∈ A ] (SliceDomain._⊩D_ g b d) → Σ[ j~ ∈ A ] (tracks {xs = asmV} {ys = asmW} j~ (j .map)) → Σ[ r ∈ A ] (SliceDomain._⊩D_ h r (rawMap d))
    transformRealizers d@(y , s , coh) (e , pr₁e⊩y , pr₂e⊩) (j~ , isTrackedJ) =
        let
          realizer : A
          realizer = pair ⨾ (pr₁ ⨾ e) ⨾ λ* (` j~ ̇ (` pr₂ ̇ ` e ̇ # zero))

          pr₁realizer≡pr₁e : pr₁ ⨾ realizer ≡ pr₁ ⨾ e
          pr₁realizer≡pr₁e =
            pr₁ ⨾ realizer
              ≡⟨ refl ⟩ -- unfolding
            pr₁ ⨾ (pair ⨾ (pr₁ ⨾ e) ⨾ λ* (` j~ ̇ (` pr₂ ̇ ` e ̇ # zero)))
              ≡⟨ pr₁pxy≡x _ _ ⟩
            pr₁ ⨾ e
              ∎

          pr₂realizerEq : (a : A) → pr₂ ⨾ realizer ⨾ a ≡ j~ ⨾ (pr₂ ⨾ e ⨾ a)
          pr₂realizerEq a =
            pr₂ ⨾ realizer ⨾ a
              ≡⟨ refl ⟩
            pr₂ ⨾ (pair ⨾ (pr₁ ⨾ e) ⨾ λ* (` j~ ̇ (` pr₂ ̇ ` e ̇ # zero))) ⨾ a
              ≡⟨ cong (λ x → x ⨾ a) (pr₂pxy≡y _ _) ⟩
            λ* (` j~ ̇ (` pr₂ ̇ ` e ̇ # zero)) ⨾ a
              ≡⟨ λ*ComputationRule (` j~ ̇ (` pr₂ ̇ ` e ̇ # zero)) a ⟩
            j~ ⨾ (pr₂ ⨾ e ⨾ a)
              ∎
        in
          (realizer ,
          (subst (λ r' → r' ⊩[ asmY ] y) (sym pr₁realizer≡pr₁e) pr₁e⊩y ,
          (λ { fib@(x , fx≡y) a a⊩x →
            subst (λ r' → r' ⊩[ asmW ] (j .map (s fib))) (sym (pr₂realizerEq a)) (isTrackedJ (s fib) (pr₂ ⨾ e ⨾ a) (pr₂e⊩ fib a a⊩x)) })))

    morphism : AssemblyMorphism (SliceDomain.asmD g) (SliceDomain.asmD h)
    AssemblyMorphism.map morphism (d@(y , s , coh) , ∃r) = rawMap d , PT.rec2 isPropPropTrunc (λ r⊩d j~ → ∣ transformRealizers d r⊩d j~ ∣₁) ∃r (j .tracker)
    AssemblyMorphism.tracker morphism =
      do
        (j~ , isTrackedJ) ← j .tracker
        let
          closure : Term as 2
          closure = (` j~  ̇ (` pr₂ ̇ # one ̇ # zero))
  
          realizer : Term as 1
          realizer = ` pair ̇ (` pr₁ ̇ # zero) ̇ (λ*abst closure)
        return
          (λ* realizer ,
          (λ { (d@(y , s , coh) , ∃r) a (pr₁a⊩y , pr₂a⊩) →
            let
              pr₁Eq : pr₁ ⨾ (λ* realizer ⨾ a) ≡ pr₁ ⨾ a
              pr₁Eq =
                pr₁ ⨾ (λ* realizer ⨾ a)
                  ≡⟨ cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer a) ⟩
                pr₁ ⨾ (pair ⨾ (pr₁ ⨾ a) ⨾ _)
                  ≡⟨ pr₁pxy≡x _ _ ⟩
                pr₁ ⨾ a
                  ∎

              pr₂Eq : ∀ b → pr₂ ⨾ (λ* realizer ⨾ a) ⨾ b ≡ j~ ⨾ (pr₂ ⨾ a ⨾ b)
              pr₂Eq b =
                pr₂ ⨾ (λ* realizer ⨾ a) ⨾ b
                  ≡⟨ cong (λ x → pr₂ ⨾ x ⨾ b) (λ*ComputationRule realizer a) ⟩
                pr₂ ⨾ (pair ⨾ (pr₁ ⨾ a) ⨾ _) ⨾ b
                  ≡⟨ cong (λ x → x ⨾ b) (pr₂pxy≡y _ _) ⟩
                βreduction closure b (a ∷ [])
            in
            subst (λ r' → r' ⊩[ asmY ] y) (sym pr₁Eq) pr₁a⊩y ,
            (λ { fib@(x , fx≡y) b b⊩x → subst (λ r' → r' ⊩[ asmW ] j .map (s fib)) (sym (pr₂Eq b)) (isTrackedJ (s fib) (pr₂ ⨾ a ⨾ b) (pr₂a⊩ fib b b⊩x)) }) }))
            -- 
  {-# TERMINATING #-}
  Π[_] : Functor (SliceCat ASM (X , asmX)) (SliceCat ASM (Y , asmY))
  Functor.F-ob Π[_] (sliceob {V , asmV} h) = sliceob (SliceDomain.projection h)
  Functor.F-hom Π[_] {sliceob {V , asmV} g} {sliceob {W , asmW} h} (slicehom j comm) = slicehom (SliceDomainHom.morphism g h j comm) (AssemblyMorphism≡ _ _ (funExt λ { (d@(y , s , coh) , ∃r) → refl } ))
  Functor.F-id Π[_] {sliceob {V , asmV} h} = SliceHom-≡-intro' ASM (Y , asmY) (AssemblyMorphism≡ _ _ (funExt λ { (d@(y , s , coh) , ∃r) → Σ≡Prop (λ d → isPropPropTrunc) (ΣPathP (refl , (ΣPathP (refl , (funExt (λ { (x , fx≡y) → asmX .isSetX _ _ _ _ })))))) }))
  -- this call is marked as problematic
  -- it is not even recursive :(
  Functor.F-seq Π[_] {sliceob {U , asmU} g} {sliceob {V , asmV} h} {sliceob {W , asmW} i} (slicehom j jComm) (slicehom k kComm) = SliceHom-≡-intro' ASM ((Y , asmY)) (AssemblyMorphism≡ _ _ (funExt (λ { (d@(y , s , coh) , ∃r) → Σ≡Prop (λ d → isPropPropTrunc) (ΣPathP (refl , (ΣPathP (refl , (funExt (λ { (x , fx≡y) → asmX .isSetX _ _ _ _ })))))) })))

  module ForwardIso {V P : Type ℓ} {asmV : Assembly V} {asmP : Assembly P} (g : AssemblyMorphism asmV asmY) (m : AssemblyMorphism asmP asmX) (h : AssemblyMorphism ((reindexFunctor ASM PullbacksASM f ⟅ sliceob g ⟆) .S-ob .snd) asmP) (hComm : h ⊚ m ≡ (reindexFunctor ASM PullbacksASM f ⟅ sliceob g ⟆) .S-arr) where
    opaque
       unfolding pullback
       answerMap : V → (SliceDomain.D m)
       answerMap v =
         g .map v ,
         (λ { fib@(x , fx≡gv) → h .map (x , v , fx≡gv) }) ,
         (λ { (x , fx≡gv) →
           m .map (h .map (x , v , fx≡gv)) ≡[ i ]⟨ hComm i .map (x , v , fx≡gv) ⟩ x ∎ })

       answerTracker : ∃[ t ∈ A ] (∀ (v : V) (b : A) → b ⊩[ asmV ] v → SliceDomain._⊩D_ m (t ⨾ b) (answerMap v))
       answerTracker =
         do
           (g~ , isTrackedG) ← g .tracker
           (h~ , isTrackedH) ← h .tracker
           let
             closure : Term as 2
             closure = ` h~ ̇ (` pair ̇ # zero ̇ # one)

             realizer : Term as 1
             realizer = ` pair ̇ (` g~ ̇ # zero) ̇ λ*abst closure
           return
             (λ* realizer ,
             (λ v a a⊩v →
               let
                 pr₁eq : pr₁ ⨾ (λ* realizer ⨾ a) ≡ g~ ⨾ a
                 pr₁eq =
                   pr₁ ⨾ (λ* realizer ⨾ a)
                     ≡⟨ cong (λ x → pr₁ ⨾ x) (λ*ComputationRule realizer a) ⟩
                   pr₁ ⨾ (pair ⨾ (g~ ⨾ a) ⨾ _)
                     ≡⟨ pr₁pxy≡x _ _ ⟩
                   g~ ⨾ a
                     ∎

                 pr₂eq : ∀ b → pr₂ ⨾ (λ* realizer ⨾ a) ⨾ b ≡ h~ ⨾ (pair ⨾ b ⨾ a)
                 pr₂eq b =
                   pr₂ ⨾ (λ* realizer ⨾ a) ⨾ b
                     ≡⟨ cong (λ x → pr₂ ⨾ x ⨾ b) (λ*ComputationRule realizer a) ⟩
                   pr₂ ⨾ (pair ⨾ (g~ ⨾ a) ⨾ _) ⨾ b
                     ≡⟨ cong (λ x → x ⨾ b) (pr₂pxy≡y _ _) ⟩
                   βreduction closure b (a ∷ [])
               in
               subst (λ r' → r' ⊩[ asmY ] (g .map v)) (sym pr₁eq) (isTrackedG v a a⊩v) ,
               λ { (x , fx≡gv) b b⊩x →
                 subst
                   (λ r' → r' ⊩[ asmP ] h .map (x , v , fx≡gv))
                   (sym (pr₂eq b))
                   (isTrackedH
                     (x , v , fx≡gv)
                     (pair ⨾ b ⨾ a)
                     (subst (λ r' → r' ⊩[ asmX ] x) (sym (pr₁pxy≡x _ _)) b⊩x ,
                      subst (λ r' → r' ⊩[ asmV ] v) (sym (pr₂pxy≡y _ _)) a⊩v)) }))
       
       answer : AssemblyMorphism asmV (SliceDomain.asmD m)
       AssemblyMorphism.map answer v =
         answerMap v ,
         do
           (tr , isTrackedAnswer) ← answerTracker
           (b , b⊩v) ← asmV .⊩surjective v
           return (tr ⨾ b , isTrackedAnswer v b b⊩v)
       AssemblyMorphism.tracker answer = answerTracker

       answerEq : answer ⊚ ((Π[_] ⟅ sliceob m ⟆) .S-arr) ≡ g
       answerEq = AssemblyMorphism≡ _ _ (funExt λ v → refl)

  
  module BackwardIso {V P : Type ℓ} {asmV : Assembly V} {asmP : Assembly P} (g : AssemblyMorphism asmV asmY) (m : AssemblyMorphism asmP asmX) (h : AssemblyMorphism asmV ((Π[_] ⟅ sliceob m ⟆) .S-ob .snd)) (hComm : h ⊚ ((Π[_] ⟅ sliceob m ⟆) .S-arr) ≡ g) where
       Q : ASM .Category.ob
       Q = (reindexFunctor ASM PullbacksASM f ⟅ sliceob g ⟆) .S-ob

       typeQ : Type ℓ
       typeQ = Q .fst

       asmQ : Assembly typeQ
       asmQ = Q .snd

       isFiberOfY : (x : X) → (v : V) → f .map x ≡ g .map v → h .map v .fst .fst ≡ f .map x
       isFiberOfY x v fx≡gv =
            h .map v .fst .fst
              ≡[ i ]⟨ hComm i .map v ⟩
            g .map v
              ≡⟨ sym fx≡gv ⟩
            f .map x
              ∎
              
       opaque
         unfolding pullback
         answerMap : Q .fst → P
         answerMap (x , v , fx≡gv) =
           h .map v .fst .snd .fst 
           (x ,
           sym (isFiberOfY x v fx≡gv))

       opaque
         unfolding pullback
         unfolding answerMap
         answer : AssemblyMorphism asmQ asmP
         AssemblyMorphism.map answer = answerMap
         AssemblyMorphism.tracker answer =
           do
           (h~ , isTrackedH) ← h .tracker
           let
             realizer : Term as 1
             realizer = ` pr₂ ̇ (` h~ ̇ (` pr₂ ̇ # zero)) ̇ (` pr₁ ̇ # zero)
           return
             (λ* realizer ,
             (λ { q@(x , v , fx≡gv) a (pr₁a⊩x , pr₂a⊩v) →
               subst
                 (λ r' → r' ⊩[ asmP ] (answerMap (x , v , fx≡gv)))
                 (sym (λ*ComputationRule realizer a))
                 (isTrackedH v (pr₂ ⨾ a) pr₂a⊩v .snd (x , sym (isFiberOfY x v fx≡gv)) (pr₁ ⨾ a) pr₁a⊩x) }))

  opaque
    unfolding pullback
    reindex⊣Π[_] : reindexFunctor ASM PullbacksASM f ⊣ Π[_]
    Iso.fun (_⊣_.adjIso reindex⊣Π[_] {sliceob {V , asmV} g} {sliceob {P , asmP} m}) (slicehom h hComm) = slicehom (ForwardIso.answer g m h hComm) (ForwardIso.answerEq g m h hComm) 
    Iso.inv (_⊣_.adjIso reindex⊣Π[_] {sliceob {V , asmV} g} {sliceob {P , asmP} m}) (slicehom h hComm) =
      slicehom answer (AssemblyMorphism≡ _ _ (funExt λ { (x , v , fx≡gv) → answerEq x v fx≡gv })) where
      Π[f]m : AssemblyMorphism (S-ob (Π[_] ⟅ sliceob m ⟆) .snd) asmY
      Π[f]m = (Π[_] ⟅ sliceob m ⟆) .S-arr

      Q : ASM .Category.ob
      Q = (reindexFunctor ASM PullbacksASM f ⟅ sliceob g ⟆) .S-ob

      typeQ : Type ℓ
      typeQ = Q .fst

      asmQ : Assembly typeQ
      asmQ = Q .snd

      isFiberOfY : (x : X) → (v : V) → f .map x ≡ g .map v → h .map v .fst .fst ≡ f .map x
      isFiberOfY x v fx≡gv =
            h .map v .fst .fst
              ≡[ i ]⟨ hComm i .map v ⟩
            g .map v
              ≡⟨ sym fx≡gv ⟩
            f .map x
              ∎

      answerMap : typeQ → P
      answerMap (x , v , fx≡gv) =
        h .map v .fst .snd .fst 
          (x ,
          sym (isFiberOfY x v fx≡gv))

      answerEq : (x : X) (v : V) (fx≡gv : f .map x ≡ g .map v) → m .map (answerMap (x , v , fx≡gv)) ≡ x
      answerEq x v fx≡gv =
        m .map (answerMap (x , v , fx≡gv))
          ≡⟨ refl ⟩
        m .map (h .map v .fst .snd .fst (x , sym (isFiberOfY x v fx≡gv)))
          ≡⟨ h .map v .fst .snd .snd (x , sym (isFiberOfY x v fx≡gv)) ⟩
        x
          ∎

      answer : AssemblyMorphism asmQ asmP
      AssemblyMorphism.map answer = answerMap
      AssemblyMorphism.tracker answer =
        do
          (h~ , isTrackedH) ← h .tracker
          let
            realizer : Term as 1
            realizer = ` pr₂ ̇ (` h~ ̇ (` pr₂ ̇ # zero)) ̇ (` pr₁ ̇ # zero)
          return
            (λ* realizer ,
            (λ { q@(x , v , fx≡gv) a (pr₁a⊩x , pr₂a⊩v) →
              subst
                (λ r' → r' ⊩[ asmP ] (answerMap (x , v , fx≡gv)))
                (sym (λ*ComputationRule realizer a))
                (isTrackedH v (pr₂ ⨾ a) pr₂a⊩v .snd (x , sym (isFiberOfY x v fx≡gv)) (pr₁ ⨾ a) pr₁a⊩x) }))
    Iso.rightInv (_⊣_.adjIso reindex⊣Π[_] {sliceob {V , asmV} g} {sliceob {P , asmP} m}) (slicehom h hComm) =
      SliceHom-≡-intro'
        ASM
        (Y , asmY)
        (AssemblyMorphism≡ _ _
          (funExt
            λ v →
              Σ≡Prop
                (λ d → isPropPropTrunc)
                (ΣPathP
                  ({!h!} , {!!}))))
    Iso.leftInv (_⊣_.adjIso reindex⊣Π[_] {sliceob {V , asmV} g} {sliceob {P , asmP} m}) (slicehom h hComm) =
      SliceHom-≡-intro'
        ASM
        (X , asmX)
        (AssemblyMorphism≡ _ _
          (funExt
            λ { (x , v , fx≡gv) →
              {!!} }))
    _⊣_.adjNatInD reindex⊣Π[_] = {!!}
    _⊣_.adjNatInC reindex⊣Π[_] = {!!}

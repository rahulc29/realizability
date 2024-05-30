open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
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
            in
            subst (λ r' → r' ⊩[ asmY ] y) (sym pr₁Eq) pr₁a⊩y ,
            (λ { fib@(x , fx≡y) b b⊩x → {!isTrackedJ !} }) }))

  Π[_] : Functor (SliceCat ASM (X , asmX)) (SliceCat ASM (Y , asmY))
  Functor.F-ob Π[_] (sliceob {V , asmV} h) = sliceob (SliceDomain.projection h)
  Functor.F-hom Π[_] {sliceob {V , asmV} g} {sliceob {W , asmW} h} (slicehom j comm) = {!!}
  Functor.F-id Π[_] = {!!}
  Functor.F-seq Π[_] = {!!}

  reindex⊣Π[_] : reindexFunctor ASM PullbacksASM f ⊣ Π[_]
  Iso.fun (_⊣_.adjIso reindex⊣Π[_]) = λ fo → slicehom {!!} {!!}
  Iso.inv (_⊣_.adjIso reindex⊣Π[_]) = {!!}
  Iso.rightInv (_⊣_.adjIso reindex⊣Π[_]) = {!!}
  Iso.leftInv (_⊣_.adjIso reindex⊣Π[_]) = {!!}
  _⊣_.adjNatInD reindex⊣Π[_] = {!!}
  _⊣_.adjNatInC reindex⊣Π[_] = {!!}

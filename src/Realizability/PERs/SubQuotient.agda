open import Realizability.ApplicativeStructure
open import Realizability.CombinatoryAlgebra
open import Realizability.PropResizing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩; str)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Functions.FunExtEquiv
open import Cubical.Relation.Binary
open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Vec
open import Cubical.Reflection.RecordEquiv
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Categories.Category
open import Cubical.Categories.Functor hiding (Id)

module Realizability.PERs.SubQuotient
  {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where

open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca
open import Realizability.PERs.PER ca
open import Realizability.Modest.Base ca

open CombinatoryAlgebra ca
open Combinators ca renaming (i to Id; ia≡a to Ida≡a)

module _
  (per : PER) where

  domain : Type ℓ
  domain = Σ[ a ∈ A ] (per .PER.relation a a)

  subQuotient : Type ℓ
  subQuotient = domain / λ { (a , _) (b , _) → per .PER.relation a b }

  subQuotientRealizability : A → subQuotient → hProp ℓ
  subQuotientRealizability r [a] =
    SQ.rec
      isSetHProp
      (λ { (a , a~a) → r ~[ per ] a , isProp~ r per a })
      (λ { (a , a~a) (b , b~b) a~b →
        Σ≡Prop
          (λ x → isPropIsProp)
          (hPropExt
            (isProp~ r per a)
            (isProp~ r per b)
            (λ r~a → PER.isTransitive per r a b r~a a~b)
            (λ r~b → PER.isTransitive per r b a r~b (PER.isSymmetric per a b a~b))) })
      [a]
      
  
  subQuotientAssembly : Assembly subQuotient
  Assembly._⊩_ subQuotientAssembly r [a] = ⟨ subQuotientRealizability r [a] ⟩
  Assembly.isSetX subQuotientAssembly = squash/
  Assembly.⊩isPropValued subQuotientAssembly r [a] = str (subQuotientRealizability r [a])
  Assembly.⊩surjective subQuotientAssembly [a] =
    SQ.elimProp
      {P = λ [a] → ∃[ r ∈ A ] ⟨ subQuotientRealizability r [a] ⟩}
      (λ [a] → isPropPropTrunc)
      (λ { (a , a~a) → return (a , a~a) })
      [a]
      
  isModestSubQuotientAssembly : isModest subQuotientAssembly
  isModestSubQuotientAssembly x y a a⊩x a⊩y =
    SQ.elimProp2
      {P = λ x y → motive x y}
      isPropMotive
      (λ { (x , x~x) (y , y~y) a a~x a~y →
        eq/ (x , x~x) (y , y~y) (PER.isTransitive per x a y (PER.isSymmetric per a x a~x) a~y) })
      x y
      a a⊩x a⊩y where
        motive : ∀ (x y : subQuotient) → Type ℓ
        motive x y = ∀ (a : A) (a⊩x : a ⊩[ subQuotientAssembly ] x) (a⊩y : a ⊩[ subQuotientAssembly ] y) → x ≡ y

        isPropMotive : ∀ x y → isProp (motive x y)
        isPropMotive x y = isPropΠ3 λ _ _ _ → squash/ x y

module _ (R S : PER) (f : perMorphism R S) where

  subQuotientAssemblyMorphism : AssemblyMorphism (subQuotientAssembly R) (subQuotientAssembly S)
  subQuotientAssemblyMorphism =
    SQ.rec
      (isSetAssemblyMorphism (subQuotientAssembly R) (subQuotientAssembly S))
      mainMap
      mainMapCoherence
      f where

      mainMap : perTracker R S → AssemblyMorphism (subQuotientAssembly R) (subQuotientAssembly S)
      AssemblyMorphism.map (mainMap (f , fIsTracker)) sqR =
        SQ.rec
          squash/
          mainMapRepr
          mainMapReprCoherence
          sqR module MainMapDefn where
            mainMapRepr : domain R → subQuotient S
            mainMapRepr (r , r~r) = [ f ⨾ r , fIsTracker r r r~r ]

            mainMapReprCoherence : (a b : domain R) → R .PER.relation (a .fst) (b .fst) → mainMapRepr a ≡ mainMapRepr b
            mainMapReprCoherence (a , a~a) (b , b~b) a~b = eq/ _ _ (fIsTracker a b a~b)
 
      AssemblyMorphism.tracker (mainMap (f , fIsTracker)) =
        do
          return
            (f ,
            (λ sqR s s⊩sqR →
              SQ.elimProp
                {P =
                  λ sqR
                  → ∀ (s : A)
                  → s ⊩[ subQuotientAssembly R ] sqR
                  → ⟨ subQuotientRealizability S (f ⨾ s) (SQ.rec squash/ (MainMapDefn.mainMapRepr f fIsTracker sqR) (MainMapDefn.mainMapReprCoherence f fIsTracker sqR) sqR) ⟩}
                (λ sqR → isPropΠ2 λ s s⊩sqR → str (subQuotientRealizability S (f ⨾ s) (SQ.rec squash/ (MainMapDefn.mainMapRepr f fIsTracker sqR) (MainMapDefn.mainMapReprCoherence f fIsTracker sqR) sqR)))
                (λ { (a , a~a) s s~a → fIsTracker s a s~a })
                sqR s s⊩sqR))

      mainMapCoherence : (a b : perTracker R S) → isEquivTracker R S a b → mainMap a ≡ mainMap b
      mainMapCoherence (a , a~a) (b , b~b) a~b =
        AssemblyMorphism≡ _ _
          (funExt
            λ sq →
              SQ.elimProp
                {P =
                  λ sq →
                    SQ.rec
                      squash/
                      (MainMapDefn.mainMapRepr a a~a sq)
                      (MainMapDefn.mainMapReprCoherence a a~a sq) sq
                    ≡
                    SQ.rec
                      squash/
                      (MainMapDefn.mainMapRepr b b~b sq)
                      (MainMapDefn.mainMapReprCoherence b b~b sq) sq}
                (λ sq → squash/ _ _)
                (λ { (r , r~r) → eq/ _ _ (a~b r r~r) })
                sq)
    

subQuotientModestSet : PER → MOD .Category.ob
subQuotientModestSet R = subQuotient R , subQuotientAssembly R , isModestSubQuotientAssembly R

subQuotientFunctor : Functor PERCat MOD
Functor.F-ob subQuotientFunctor R = subQuotientModestSet R
Functor.F-hom subQuotientFunctor {R} {S} f = subQuotientAssemblyMorphism R S f
Functor.F-id subQuotientFunctor {R} =
  AssemblyMorphism≡ _ _
    (funExt
      λ sqR →
        SQ.elimProp
          {P = λ sqR → subQuotientAssemblyMorphism R R (PERCat .Category.id {R}) .AssemblyMorphism.map sqR ≡ identityMorphism (subQuotientAssembly R) .AssemblyMorphism.map sqR}
          (λ sqR → squash/ _ _)
          (λ { (a , a~a) →
            eq/ _ _
              (subst (_~[ R ] a) (sym (Ida≡a a)) a~a) })
          sqR)
Functor.F-seq subQuotientFunctor {R} {S} {T} f g =
  AssemblyMorphism≡ _ _
    (funExt
      λ sq →
        SQ.elimProp3
          {P = λ sqR f g →
            subQuotientAssemblyMorphism R T (seq' PERCat {R} {S} {T} f g) .AssemblyMorphism.map sqR ≡
            seq' MOD
              {x = subQuotientModestSet R}
              {y = subQuotientModestSet S}
              {z = subQuotientModestSet T}
              (subQuotientAssemblyMorphism R S f) (subQuotientAssemblyMorphism S T g) .AssemblyMorphism.map sqR}
          (λ sq f g → squash/ _ _)
          (λ { (a , a~a) (b , bIsTracker) (c , cIsTracker) →
            eq/ _ _ (subst (_~[ T ] (c ⨾ (b ⨾ a))) (sym (λ*ComputationRule (` c ̇ (` b ̇ # zero)) a)) (cIsTracker (b ⨾ a) (b ⨾ a) (bIsTracker a a a~a))) })
          sq f g)

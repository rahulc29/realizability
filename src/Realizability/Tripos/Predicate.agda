open import Realizability.CombinatoryAlgebra
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Cubical.Relation.Binary.Order

module Realizability.Tripos.Predicate {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)

record Predicate {ℓ' ℓ''} (X : Type ℓ') : Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ'')) where
  field
    isSetX : isSet X
    ∣_∣ : X → A → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    isPropValued : ∀ x a → isProp (∣_∣ x a)

open Predicate
_⊩_ : ∀ {ℓ'} → A → (A → Type ℓ') → Type ℓ'
a ⊩ ϕ = ϕ a

PredicateΣ : ∀ {ℓ' ℓ''} → (X : Type ℓ') → Type (ℓ-max (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) (ℓ-suc ℓ''))
PredicateΣ {ℓ'} {ℓ''} X = Σ[ rel ∈ (X → A → hProp (ℓ-max (ℓ-max ℓ ℓ') ℓ'')) ] (isSet X)

isSetPredicateΣ : ∀ {ℓ' ℓ''} (X : Type ℓ') → isSet (PredicateΣ {ℓ'' = ℓ''} X)
isSetPredicateΣ X = isSetΣ (isSetΠ (λ x → isSetΠ λ a → isSetHProp)) λ _ → isProp→isSet isPropIsSet

PredicateIsoΣ : ∀ {ℓ' ℓ''} (X : Type ℓ') → Iso (Predicate {ℓ'' = ℓ''} X) (PredicateΣ {ℓ'' = ℓ''} X)
PredicateIsoΣ {ℓ'} {ℓ''} X =
  iso
    (λ p → (λ x a → (a ⊩ ∣ p ∣ x) , p .isPropValued x a) , p .isSetX)
    (λ p → record { isSetX = p .snd ; ∣_∣ = λ x a → p .fst x a .fst ; isPropValued = λ x a → p .fst x a .snd })
    (λ b → refl)
    λ a → refl

Predicate≡PredicateΣ : ∀ {ℓ' ℓ''} (X : Type ℓ') → Predicate {ℓ'' = ℓ''} X ≡ PredicateΣ {ℓ'' = ℓ''} X
Predicate≡PredicateΣ {ℓ'} {ℓ''} X = isoToPath (PredicateIsoΣ X)

isSetPredicate : ∀ {ℓ' ℓ''} (X : Type ℓ') → isSet (Predicate {ℓ'' = ℓ''} X)
isSetPredicate {ℓ'} {ℓ''} X = subst (λ predicateType → isSet predicateType) (sym (Predicate≡PredicateΣ X)) (isSetPredicateΣ {ℓ'' = ℓ''} X)

PredicateΣ≡ : ∀ {ℓ' ℓ''} (X : Type ℓ') → (P Q : PredicateΣ {ℓ'' = ℓ''} X) → (P .fst ≡ Q .fst) → P ≡ Q
PredicateΣ≡ X P Q ∣P∣≡∣Q∣ = Σ≡Prop (λ _ → isPropIsSet) ∣P∣≡∣Q∣


module PredicateProperties {ℓ' ℓ''} (X : Type ℓ') where
  PredicateX = Predicate {ℓ'' = ℓ''} X
  open Predicate
  _≤_ : Predicate {ℓ'' = ℓ''} X → Predicate {ℓ'' = ℓ''} X → Type (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
  ϕ ≤ ψ = ∃[ b ∈ A ] (∀ (x : X) (a : A) → a ⊩ (∣ ϕ ∣ x) → (b ⨾ a) ⊩ ∣ ψ ∣ x)

  isProp≤ : ∀ ϕ ψ → isProp (ϕ ≤ ψ)
  isProp≤ ϕ ψ = isPropPropTrunc

  isRefl≤ : ∀ ϕ → ϕ ≤ ϕ
  isRefl≤ ϕ = ∣ Id , (λ x a a⊩ϕx → subst (λ r → r ⊩ ∣ ϕ ∣ x) (sym (Ida≡a a)) a⊩ϕx) ∣₁

  isTrans≤ : ∀ ϕ ψ ξ → ϕ ≤ ψ → ψ ≤ ξ → ϕ ≤ ξ
  isTrans≤ ϕ ψ ξ ϕ≤ψ ψ≤ξ = do
                           (a , ϕ≤[a]ψ) ← ϕ≤ψ
                           (b , ψ≤[b]ξ) ← ψ≤ξ
                           return
                             ((B b a) ,
                             (λ x a' a'⊩ϕx →
                               subst
                                 (λ r → r ⊩ ∣ ξ ∣ x)
                                 (sym (Ba≡gfa b a a'))
                                 (ψ≤[b]ξ x (a ⨾ a')
                                 (ϕ≤[a]ψ x a' a'⊩ϕx))))
    

  open IsPreorder renaming
    (is-set to isSet
    ;is-prop-valued to isPropValued
    ;is-refl to isRefl
    ;is-trans to isTrans)

  preorder≤ : _
  preorder≤ = preorder (Predicate X) _≤_ (ispreorder (isSetPredicate X) isProp≤ isRefl≤ isTrans≤)

  infix 25 _⊔_
  _⊔_ : PredicateX → PredicateX → PredicateX
  (ϕ ⊔ ψ) .isSetX = ϕ .isSetX
  ∣ ϕ ⊔ ψ ∣ x a = ∥ ((pair ⨾ k ⨾ a) ⊩ ∣ ϕ ∣ x) ⊎ ((pair ⨾ k' ⨾ a) ⊩ ∣ ψ ∣ x) ∥₁
  (ϕ ⊔ ψ) .isPropValued x a = isPropPropTrunc

  infix 25 _⊓_
  _⊓_ : PredicateX → PredicateX → PredicateX
  (ϕ ⊓ ψ) .isSetX = ϕ .isSetX
  ∣ ϕ ⊓ ψ ∣ x a = ((pr₁ ⨾ a) ⊩ ∣ ϕ ∣ x) × ((pr₂ ⨾ a) ⊩ ∣ ψ ∣ x)
  (ϕ ⊓ ψ) .isPropValued x a = isProp× (ϕ .isPropValued x (pr₁ ⨾ a)) (ψ .isPropValued x (pr₂ ⨾ a))

  infix 25 _⇒_
  _⇒_ : PredicateX → PredicateX → PredicateX
  (ϕ ⇒ ψ) .isSetX = ϕ .isSetX
  ∣ ϕ ⇒ ψ ∣ x a = ∀ b → (b ⊩ ∣ ϕ ∣ x) → (a ⨾ b) ⊩ ∣ ψ ∣ x
  (ϕ ⇒ ψ) .isPropValued x a = isPropΠ λ a → isPropΠ λ a⊩ϕx → ψ .isPropValued _ _

module Morphism {ℓ' ℓ''} {X Y : Type ℓ'} (isSetX : isSet X) (isSetY : isSet Y)  where
  PredicateX = Predicate {ℓ'' = ℓ''} X
  PredicateY = Predicate {ℓ'' = ℓ''} Y
  module PredicatePropertiesX = PredicateProperties {ℓ'' = ℓ''} X
  module PredicatePropertiesY = PredicateProperties {ℓ'' = ℓ''} Y
  open PredicatePropertiesX hiding (PredicateX) renaming (_≤_ to _≤X_ ; isProp≤ to isProp≤X)
  open PredicatePropertiesY hiding (PredicateX) renaming (_≤_ to _≤Y_ ; isProp≤ to isProp≤Y)

  ⋆_ : (X → Y) → (PredicateY → PredicateX)
  ⋆ f =
    λ ϕ →
      record
        { isSetX = isSetX
        ; ∣_∣ = λ x a → a ⊩ ∣ ϕ ∣ (f x)
        ; isPropValued = λ x a → ϕ .isPropValued (f x) a }

  `∀[_] : (X → Y) → (PredicateX → PredicateY)
  `∀[ f ] =
    λ ϕ →
      record
        { isSetX = isSetY
        ; ∣_∣ = λ y a → (∀ b x → f x ≡ y → (a ⨾ b) ⊩ ∣ ϕ ∣ x)
        ; isPropValued = λ y a → isPropΠ λ a' → isPropΠ λ x → isPropΠ λ fx≡y → ϕ .isPropValued x (a ⨾ a') }

  `∃[_] : (X → Y) → (PredicateX → PredicateY)
  `∃[ f ] =
    λ ϕ →
      record
        { isSetX = isSetY
        ; ∣_∣ = λ y a → ∃[ x ∈ X ] (f x ≡ y) × (a ⊩ ∣ ϕ ∣ x)
        ; isPropValued = λ y a → isPropPropTrunc }

  -- Adjunction proofs

  `∃isLeftAdjoint→ : ∀ ϕ ψ f → `∃[ f ] ϕ ≤Y ψ → ϕ ≤X (⋆ f) ψ
  `∃isLeftAdjoint→ ϕ ψ f p =
    do
      (a~ , a~proves) ← p
      return (a~ , (λ x a a⊩ϕx → a~proves (f x) a ∣ x , refl , a⊩ϕx ∣₁))


  `∃isLeftAdjoint← : ∀ ϕ ψ f → ϕ ≤X (⋆ f) ψ → `∃[ f ] ϕ ≤Y ψ
  `∃isLeftAdjoint← ϕ ψ f p =
    do
      (a~ , a~proves) ← p
      return
        (a~ ,
        (λ y b b⊩∃fϕ →
          equivFun
            (propTruncIdempotent≃
              (ψ .isPropValued y (a~ ⨾ b)))
              (do
                (x , fx≡y , b⊩ϕx) ← b⊩∃fϕ
                return (subst (λ y' → (a~ ⨾ b) ⊩ ∣ ψ ∣ y') fx≡y (a~proves x b b⊩ϕx)))))

  `∃isLeftAdjoint : ∀ ϕ ψ f → `∃[ f ] ϕ ≤Y ψ ≡ ϕ ≤X (⋆ f) ψ
  `∃isLeftAdjoint ϕ ψ f =
    hPropExt
      (isProp≤Y (`∃[ f ] ϕ) ψ)
      (isProp≤X ϕ ((⋆ f) ψ))
      (`∃isLeftAdjoint→ ϕ ψ f)
      (`∃isLeftAdjoint← ϕ ψ f)

  `∀isRightAdjoint→ : ∀ ϕ ψ f → ψ ≤Y `∀[ f ] ϕ → (⋆ f) ψ ≤X ϕ
  `∀isRightAdjoint→ ϕ ψ f p =
    do
      (a~ , a~proves) ← p
      let realizer = (s ⨾ (s ⨾ (k ⨾ a~) ⨾ Id) ⨾ (k ⨾ k))
      return
        (realizer ,
        (λ x a a⊩ψfx →
          equivFun
            (propTruncIdempotent≃
              (ϕ .isPropValued x (realizer ⨾ a) ))
              (do
                let ∀prover = a~proves (f x) a a⊩ψfx
                return
                  (subst
                    (λ ϕ~ → ϕ~ ⊩ ∣ ϕ ∣ x)
                    (sym
                      (realizer ⨾ a
                        ≡⟨ refl ⟩
                       s ⨾ (s ⨾ (k ⨾ a~) ⨾ Id) ⨾ (k ⨾ k) ⨾ a
                        ≡⟨ sabc≡ac_bc _ _ _ ⟩
                       s ⨾ (k ⨾ a~) ⨾ Id ⨾ a ⨾ (k ⨾ k ⨾ a)
                        ≡⟨ cong (λ x → x ⨾ (k ⨾ k ⨾ a)) (sabc≡ac_bc _ _ _) ⟩
                       k ⨾ a~ ⨾ a ⨾ (Id ⨾ a) ⨾ (k ⨾ k ⨾ a)
                        ≡⟨ cong (λ x → k ⨾ a~ ⨾ a ⨾ x ⨾ (k ⨾ k ⨾ a)) (Ida≡a a) ⟩
                       k ⨾ a~ ⨾ a ⨾ a ⨾ (k ⨾ k ⨾ a)
                        ≡⟨ cong (λ x → k ⨾ a~ ⨾ a ⨾ a ⨾ x) (kab≡a _ _) ⟩
                       (k ⨾ a~ ⨾ a) ⨾ a ⨾ k
                        ≡⟨ cong (λ x → x ⨾ a ⨾ k) (kab≡a _ _) ⟩
                       a~ ⨾ a ⨾ k
                         ∎))
                    (∀prover k x refl)))))

  `∀isRightAdjoint← : ∀ ϕ ψ f → (⋆ f) ψ ≤X ϕ → ψ ≤Y `∀[ f ] ϕ
  `∀isRightAdjoint← ϕ ψ f p =
    do
      (a~ , a~proves) ← p
      let realizer = (s ⨾ (s ⨾ (k ⨾ s) ⨾ (s ⨾ (k ⨾ k) ⨾ (k ⨾ a~))) ⨾ (s ⨾ (k ⨾ k) ⨾ Id))
      return
        (realizer ,
        (λ y b b⊩ψy a x fx≡y →
          subst
            (λ r → r ⊩ ∣ ϕ ∣ x)
            (sym
              (realizer ⨾ b ⨾ a
                 ≡⟨ refl ⟩
               s ⨾ (s ⨾ (k ⨾ s) ⨾ (s ⨾ (k ⨾ k) ⨾ (k ⨾ a~))) ⨾ (s ⨾ (k ⨾ k) ⨾ Id) ⨾ b ⨾ a
                 ≡⟨ cong (λ x → x ⨾ a) (sabc≡ac_bc _ _ _) ⟩
               s ⨾ (k ⨾ s) ⨾ (s ⨾ (k ⨾ k) ⨾ (k ⨾ a~)) ⨾ b ⨾ (s ⨾ (k ⨾ k) ⨾ Id ⨾ b) ⨾ a
                 ≡⟨ cong (λ x → s ⨾ (k ⨾ s) ⨾ (s ⨾ (k ⨾ k) ⨾ (k ⨾ a~)) ⨾ b ⨾ x ⨾ a) (sabc≡ac_bc (k ⨾ k) Id b) ⟩
               s ⨾ (k ⨾ s) ⨾ (s ⨾ (k ⨾ k) ⨾ (k ⨾ a~)) ⨾ b ⨾ ((k ⨾ k ⨾ b) ⨾ (Id ⨾ b)) ⨾ a
                 ≡⟨ cong (λ x → s ⨾ (k ⨾ s) ⨾ (s ⨾ (k ⨾ k) ⨾ (k ⨾ a~)) ⨾ b ⨾ (x ⨾ (Id ⨾ b)) ⨾ a) (kab≡a _ _) ⟩
               s ⨾ (k ⨾ s) ⨾ (s ⨾ (k ⨾ k) ⨾ (k ⨾ a~)) ⨾ b ⨾ (k ⨾ (Id ⨾ b)) ⨾ a
                 ≡⟨ cong (λ x → s ⨾ (k ⨾ s) ⨾ (s ⨾ (k ⨾ k) ⨾ (k ⨾ a~)) ⨾ b ⨾ (k ⨾ x) ⨾ a) (Ida≡a b) ⟩
               s ⨾ (k ⨾ s) ⨾ (s ⨾ (k ⨾ k) ⨾ (k ⨾ a~)) ⨾ b ⨾ (k ⨾ b) ⨾ a
                 ≡⟨ cong (λ x → x ⨾ (k ⨾ b) ⨾ a) (sabc≡ac_bc _ _ _) ⟩
               k ⨾ s ⨾ b ⨾ (s ⨾ (k ⨾ k) ⨾ (k ⨾ a~) ⨾ b) ⨾ (k ⨾ b) ⨾ a
                 ≡⟨ cong (λ x → x ⨾ (s ⨾ (k ⨾ k) ⨾ (k ⨾ a~) ⨾ b) ⨾ (k ⨾ b) ⨾ a) (kab≡a _ _) ⟩
               s ⨾ (s ⨾ (k ⨾ k) ⨾ (k ⨾ a~) ⨾ b) ⨾ (k ⨾ b) ⨾ a
                 ≡⟨ sabc≡ac_bc _ _ _ ⟩
               s ⨾ (k ⨾ k) ⨾ (k ⨾ a~) ⨾ b ⨾ a ⨾ (k ⨾ b ⨾ a)
                 ≡⟨ cong (λ x → s ⨾ (k ⨾ k) ⨾ (k ⨾ a~) ⨾ b ⨾ a ⨾ x) (kab≡a b a) ⟩
               s ⨾ (k ⨾ k) ⨾ (k ⨾ a~) ⨾ b ⨾ a ⨾ b
                 ≡⟨ cong (λ x → x ⨾ a ⨾ b) (sabc≡ac_bc (k ⨾ k) (k ⨾ a~) b) ⟩
               k ⨾ k ⨾ b ⨾ (k ⨾ a~ ⨾ b) ⨾ a ⨾ b
                 ≡⟨ cong (λ x → x ⨾ (k ⨾ a~ ⨾ b) ⨾ a ⨾ b) (kab≡a _ _) ⟩
               k ⨾ (k ⨾ a~ ⨾ b) ⨾ a ⨾ b
                 ≡⟨ cong (λ x → k ⨾ x ⨾ a ⨾ b) (kab≡a _ _) ⟩
               k ⨾ a~ ⨾ a ⨾ b
                 ≡⟨ cong (λ x → x ⨾ b) (kab≡a _ _) ⟩
               a~ ⨾ b
                   ∎))
            (a~proves x b (subst (λ x' → b ⊩ ∣ ψ ∣ x') (sym fx≡y) b⊩ψy))))

  `∀isRightAdjoint : ∀ ϕ ψ f → (⋆ f) ψ ≤X ϕ ≡ ψ ≤Y `∀[ f ] ϕ
  `∀isRightAdjoint ϕ ψ f =
    hPropExt
      (isProp≤X ((⋆ f) ψ) ϕ)
      (isProp≤Y ψ (`∀[ f ] ϕ))
      (`∀isRightAdjoint← ϕ ψ f)
      (`∀isRightAdjoint→ ϕ ψ f)

-- The proof is trivial but I am the reader it was left to as an exercise
module BeckChevalley
    {ℓ' ℓ'' : Level}
    (I J K : Type ℓ')
    (isSetI : isSet I)
    (isSetJ : isSet J)
    (isSetK : isSet K)
    (f : J → I)
    (g : K → I) where

    module Morphism' = Morphism {ℓ' = ℓ'} {ℓ'' = ℓ''}
    open Morphism'
    
    L = Σ[ k ∈ K ] Σ[ j ∈ J ] (g k ≡ f j)

    isSetL : isSet L
    isSetL = isSetΣ isSetK λ k → isSetΣ isSetJ λ j → isProp→isSet (isSetI _ _)

    p : L → K
    p (k , _ , _) = k

    q : L → J
    q (_ , l , _) = l

    q* = ⋆_ isSetL isSetJ q
    g* = ⋆_ isSetK isSetI g

    module `f = Morphism' isSetJ isSetI
    open `f renaming (`∃[_] to `∃[J→I][_]; `∀[_] to `∀[J→I][_])

    module `q = Morphism' isSetL isSetK
    open `q renaming (`∃[_] to `∃[L→K][_]; `∀[_] to `∀[L→K][_])

    `∃BeckChevalley→ : ∀ ϕ k a → a ⊩ ∣ g* (`∃[J→I][ f ] ϕ) ∣ k → a ⊩ ∣ `∃[L→K][ p ] (q* ϕ) ∣ k
    `∃BeckChevalley→ ϕ k a p =
      do
        (j , fj≡gk , a⊩ϕj) ← p
        return ((k , (j , (sym fj≡gk))) , (refl , a⊩ϕj))

    `∃BeckChevalley← : ∀ ϕ k a → a ⊩ ∣ `∃[L→K][ p ] (q* ϕ) ∣ k → a ⊩ ∣ g* (`∃[J→I][ f ] ϕ) ∣ k
    `∃BeckChevalley← ϕ k a p =
      do
        (x@(k' , j , gk'≡fj) , k'≡k , a⊩ϕqj) ← p
        return (j , (subst (λ k → f j ≡ g k) k'≡k (sym gk'≡fj)) , a⊩ϕqj)

    open Iso
    `∃BeckChevalley : g* ∘ `∃[J→I][ f ] ≡ `∃[L→K][ p ] ∘ q*
    `∃BeckChevalley =
      funExt λ ϕ i →
        PredicateIsoΣ K .inv
          (PredicateΣ≡ {ℓ'' = ℓ''} K
            ((λ k a → (∣ (g* ∘ `∃[J→I][ f ]) ϕ ∣ k a) , ((g* ∘ `∃[J→I][ f ]) ϕ .isPropValued k a)) , isSetK)
            ((λ k a → (∣ (`∃[L→K][ p ] ∘ q*) ϕ ∣ k a) , ((`∃[L→K][ p ] ∘ q*) ϕ .isPropValued k a)) , isSetK)
            (funExt₂
              (λ k a →
                Σ≡Prop
                  (λ x → isPropIsProp {A = x})
                  (hPropExt
                    (g* (`∃[J→I][ f ] ϕ) .isPropValued k a)
                    (`∃[L→K][ p ] (q* ϕ) .isPropValued k a)
                    (`∃BeckChevalley→ ϕ k a)
                    (`∃BeckChevalley← ϕ k a))))
           i)

    

  

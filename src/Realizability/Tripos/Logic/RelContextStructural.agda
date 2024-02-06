{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Vec
open import Cubical.Data.Nat
open import Cubical.Data.FinData
open import Cubical.Data.Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.PropositionalTruncation.Monad
open import Realizability.CombinatoryAlgebra
open import Realizability.ApplicativeStructure
open import Realizability.Tripos.Logic.Syntax
import Realizability.Tripos.Logic.Semantics as Semantics

module Realizability.Tripos.Logic.RelContextStructural where

module WeakenSyntax
  {n}
  {ℓ}
  (Ξ : Vec (Sort {ℓ = ℓ}) n)
  (R : Sort) where

  private module SyntaxΞ = Relational Ξ
  open SyntaxΞ renaming (Formula to ΞFormula)

  private module SyntaxΞR = Relational (R ∷ Ξ)
  open SyntaxΞR renaming (Formula to ΞRFormula)

  transportAlongWeakening : ∀ {Γ} → ΞFormula Γ → ΞRFormula Γ
  transportAlongWeakening {Γ} Relational.⊤ᵗ = SyntaxΞR.⊤ᵗ
  transportAlongWeakening {Γ} Relational.⊥ᵗ = SyntaxΞR.⊥ᵗ
  transportAlongWeakening {Γ} (form Relational.`∨ form₁) = transportAlongWeakening form SyntaxΞR.`∨ transportAlongWeakening form₁
  transportAlongWeakening {Γ} (form Relational.`∧ form₁) = transportAlongWeakening form SyntaxΞR.`∧ transportAlongWeakening form₁
  transportAlongWeakening {Γ} (form Relational.`→ form₁) = transportAlongWeakening form SyntaxΞR.`→ transportAlongWeakening form₁
  transportAlongWeakening {Γ} (Relational.`¬ form) = SyntaxΞR.`¬ transportAlongWeakening form
  transportAlongWeakening {Γ} (Relational.`∃ form) = SyntaxΞR.`∃ (transportAlongWeakening form)
  transportAlongWeakening {Γ} (Relational.`∀ form) = SyntaxΞR.`∀ (transportAlongWeakening form)
  transportAlongWeakening {Γ} (Relational.rel k x) = SyntaxΞR.rel (suc k) x

module WeakenSemantics
  {n}
  {ℓ ℓ' ℓ''}
  {A : Type ℓ}
  (ca : CombinatoryAlgebra A)
  (isNonTrivial : CombinatoryAlgebra.s ca ≡ CombinatoryAlgebra.k ca → ⊥)
  (Ξ : Vec (Sort {ℓ = ℓ'}) n)
  (R : Sort {ℓ = ℓ'})
  (Ξsem : Semantics.RelationInterpretation {ℓ'' = ℓ''} ca Ξ) where
  open import Realizability.Tripos.Prealgebra.Predicate.Base ca renaming (Predicate to Predicate')
  open import Realizability.Tripos.Prealgebra.Predicate.Properties ca
  open CombinatoryAlgebra ca
  open Combinators ca
  open WeakenSyntax Ξ R
  open Predicate'
  open Semantics {ℓ = ℓ} {ℓ' = ℓ'} {ℓ'' = ℓ''} ca
  Predicate = Predicate' {ℓ' = ℓ'} {ℓ'' = ℓ''}

  module SyntaxΞ = Relational Ξ
  open SyntaxΞ renaming (Formula to ΞFormula)

  module SyntaxΞR = Relational (R ∷ Ξ)
  open SyntaxΞR renaming (Formula to ΞRFormula)

  module _ (Rsem : Predicate ⟨ ⟦ R ⟧ˢ ⟩) where

    RΞsem : Semantics.RelationInterpretation {ℓ'' = ℓ''} ca (R ∷ Ξ)
    RΞsem zero = Rsem
    RΞsem (suc f) = Ξsem f

    module InterpretationΞ = Interpretation Ξ Ξsem isNonTrivial
    module InterpretationΞR = Interpretation (R ∷ Ξ) RΞsem isNonTrivial
    module SoundnessΞ = Soundness {relSym = Ξ} isNonTrivial Ξsem
    module SoundnessΞR = Soundness {relSym = R ∷ Ξ} isNonTrivial RΞsem

    syntacticTransportPreservesRealizers⁺ : ∀ {Γ} → (γ : ⟨ ⟦ Γ ⟧ᶜ ⟩) → (r : A) → (f : ΞFormula Γ) → ∣ InterpretationΞ.⟦ f ⟧ᶠ ∣ γ r → r ⊩ ∣ InterpretationΞR.⟦ transportAlongWeakening f ⟧ᶠ ∣ γ
    syntacticTransportPreservesRealizers⁻ : ∀ {Γ} → (γ : ⟨ ⟦ Γ ⟧ᶜ ⟩) → (r : A) → (f : ΞFormula Γ) → r ⊩ ∣ InterpretationΞR.⟦ transportAlongWeakening f ⟧ᶠ ∣ γ → r ⊩ ∣ InterpretationΞ.⟦ f ⟧ᶠ ∣ γ
    
    syntacticTransportPreservesRealizers⁺ {Γ} γ r Relational.⊤ᵗ r⊩⟦f⟧Ξ = r⊩⟦f⟧Ξ
    syntacticTransportPreservesRealizers⁺ {Γ} γ r (f Relational.`∨ f₁) r⊩⟦f⟧Ξ =
      r⊩⟦f⟧Ξ >>=
        λ { (inl (pr₁r≡k , pr₂r⊩⟦f⟧)) → ∣ inl (pr₁r≡k , syntacticTransportPreservesRealizers⁺ γ (pr₂ ⨾ r) f pr₂r⊩⟦f⟧) ∣₁
          ; (inr (pr₁r≡k' , pr₂r⊩⟦f₁⟧)) → ∣ inr (pr₁r≡k' , (syntacticTransportPreservesRealizers⁺ γ (pr₂ ⨾ r) f₁ pr₂r⊩⟦f₁⟧)) ∣₁ }
    syntacticTransportPreservesRealizers⁺ {Γ} γ r (f Relational.`∧ f₁) (pr₁r⊩⟦f⟧ , pr₂r⊩⟦f₁⟧) =
      syntacticTransportPreservesRealizers⁺ γ (pr₁ ⨾ r) f pr₁r⊩⟦f⟧ ,
      syntacticTransportPreservesRealizers⁺ γ (pr₂ ⨾ r) f₁ pr₂r⊩⟦f₁⟧
    syntacticTransportPreservesRealizers⁺ {Γ} γ r (f Relational.`→ f₁) r⊩⟦f⟧Ξ =
      λ b b⊩⟦f⟧ΞR → syntacticTransportPreservesRealizers⁺ γ (r ⨾ b) f₁ (r⊩⟦f⟧Ξ b (syntacticTransportPreservesRealizers⁻ γ b f b⊩⟦f⟧ΞR))
    syntacticTransportPreservesRealizers⁺ {Γ} γ r (Relational.`¬ f) r⊩⟦f⟧Ξ = {!!}
    syntacticTransportPreservesRealizers⁺ {Γ} γ r (Relational.`∃ f) r⊩⟦f⟧Ξ =
      r⊩⟦f⟧Ξ >>=
        λ { ((γ' , b) , γ'≡γ , r⊩⟦f⟧Ξγ'b) → ∣ (γ' , b) , (γ'≡γ , (syntacticTransportPreservesRealizers⁺ (γ' , b) r f r⊩⟦f⟧Ξγ'b)) ∣₁ }
    syntacticTransportPreservesRealizers⁺ {Γ} γ r (Relational.`∀ f) r⊩⟦f⟧Ξ =
      λ { b (γ' , b') γ'≡γ → syntacticTransportPreservesRealizers⁺ (γ' , b') (r ⨾ b) f (r⊩⟦f⟧Ξ b (γ' , b') γ'≡γ) }
    syntacticTransportPreservesRealizers⁺ {Γ} γ r (Relational.rel Rsym t) r⊩⟦f⟧Ξ =
      subst
        (λ R' → r ⊩ ∣ R' ∣ (⟦ t ⟧ᵗ γ))
        (sym (RΞsem (suc Rsym) ≡⟨ refl ⟩ (Ξsem Rsym ∎)))
        r⊩⟦f⟧Ξ

    syntacticTransportPreservesRealizers⁻ {Γ} γ r Relational.⊤ᵗ r⊩⟦f⟧ΞR = r⊩⟦f⟧ΞR
    syntacticTransportPreservesRealizers⁻ {Γ} γ r (f Relational.`∨ f₁) r⊩⟦f⟧ΞR = {!!}
    syntacticTransportPreservesRealizers⁻ {Γ} γ r (f Relational.`∧ f₁) r⊩⟦f⟧ΞR = {!!}
    syntacticTransportPreservesRealizers⁻ {Γ} γ r (f Relational.`→ f₁) r⊩⟦f⟧ΞR = {!!}
    syntacticTransportPreservesRealizers⁻ {Γ} γ r (Relational.`¬ f) r⊩⟦f⟧ΞR = {!!}
    syntacticTransportPreservesRealizers⁻ {Γ} γ r (Relational.`∃ f) r⊩⟦f⟧ΞR = {!!}
    syntacticTransportPreservesRealizers⁻ {Γ} γ r (Relational.`∀ f) r⊩⟦f⟧ΞR = {!!}
    syntacticTransportPreservesRealizers⁻ {Γ} γ r (Relational.rel k₁ x) r⊩⟦f⟧ΞR = {!!}

    transportPreservesHoldsInTripos : ∀ {Γ} → (f : ΞFormula Γ) → SoundnessΞ.holdsInTripos f → SoundnessΞR.holdsInTripos (transportAlongWeakening f)
    transportPreservesHoldsInTripos {Γ} f holds = {!!}
  

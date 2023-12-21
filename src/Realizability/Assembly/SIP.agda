open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.SIP
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Realizability.CombinatoryAlgebra

module Realizability.Assembly.SIP {ℓ} {A : Type ℓ} (ca : CombinatoryAlgebra A) where
open CombinatoryAlgebra ca
open Realizability.CombinatoryAlgebra.Combinators ca renaming (i to Id; ia≡a to Ida≡a)
open import Realizability.Assembly.Base ca
open import Realizability.Assembly.Morphism ca


AssemblyStr : (X : Type ℓ) → Type _
AssemblyStr X = AssemblyΣ X

AssemblyStrEquiv : StrEquiv AssemblyStr _
AssemblyStrEquiv =
  λ {
    (X , isSetX , _⊩X_ , ⊩Xsurjective)
    (Y , isSetY , _⊩Y_ , ⊩Ysurjective) e →
      ((∀ (x : X) (a : A) (a⊩x : ⟨ a ⊩X x ⟩) → ⟨ a ⊩Y (equivFun e x) ⟩)) ×
      (∃[ eFibers ∈ A ] (∀ (y : Y) (b : A) (b⊩y : ⟨ b ⊩Y y ⟩) → ⟨ (eFibers ⨾ b) ⊩X (equivCtr e y .fst) ⟩)) }

AssemblyStrEquiv→PathP : ∀ {X Y : TypeWithStr ℓ AssemblyStr} (e : ⟨ X ⟩ ≃ ⟨ Y ⟩) → AssemblyStrEquiv X Y e → PathP (λ i → AssemblyStr (ua e i)) (str X) (str Y)
AssemblyStrEquiv→PathP {X} {Y} e strEquiv i =
  (isProp→PathP {B = λ j → isSet (ua e j)} (λ j → isPropIsSet) (X .snd .fst) (Y .snd .fst) i) ,
  funExt
    (λ a →
      funExtDep
        {A = λ j → ua e j}
        {B = λ j α → hProp ℓ}
        {f = X .snd .snd .fst a}
        {g = Y .snd .snd .fst a}
        λ {x} {y} p →
          Σ≡Prop
            (λ A → isPropIsProp {A = A})
            (hPropExt
              (X .snd .snd .fst a x .snd)
              (Y .snd .snd .fst a y .snd)
              (λ a⊩x →
                subst
                  (λ y → Y .snd .snd .fst a y .fst)
                  (sym (uaβ e x) ∙ (λ j → fromPathP (transport-filler (ua e) x) j) ∙ fromPathP p)
                  (strEquiv .fst x a a⊩x))
              λ a⊩y → subst (λ x → X .snd .snd .fst a x .fst) {!!} {!!})) i ,
        λ u → {!!}

AssemblyStrUnivalent : UnivalentStr AssemblyStr AssemblyStrEquiv
AssemblyStrUnivalent {A = X} {B = Y} e = {!!}

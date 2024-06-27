open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.HITs.SetQuotients as SQ

module Utils.SQElim where

private
  variable
    ℓ ℓ' ℓ'' : Level
    A B C Q : Type ℓ
    R S T W : A → A → Type ℓ

elim2 : {P : A / R → B / S → Type ℓ}
  → (∀ x y → isSet (P x y))
  → (f : ∀ a b → P [ a ] [ b ])
  → (∀ a b c → (s : S b c) → PathP (λ i → P [ a ] (eq/ b c s i)) (f a b) (f a c))
  → (∀ a b c → (r : R a b) → PathP (λ i → P (eq/ a b r i) [ c ]) (f a c) (f b c))
  → ∀ x y → P x y
elim2 {P = P} isSetP f coh1 coh2 x y =
  SQ.elim
    {P = λ x → ∀ y → P x y}
    (λ x → isSetΠ λ y → isSetP x y)
    (λ a y →
      SQ.elim
        {P = λ y → P [ a ] y}
        (λ y → isSetP [ a ] y)
        (λ b → f a b)
        (λ b c r → coh1 a b c r)
        y)
    (λ a b r →
      funExt
        λ z →
          SQ.elimProp
            {P = λ z →  PathP (λ z₁ → P (eq/ a b r z₁) z) (elim (λ y₁ → isSetP [ a ] y₁) (λ b₁ → f a b₁) (λ b₁ c r₁ → coh1 a b₁ c r₁) z) (elim (λ y₁ → isSetP [ b ] y₁) (λ b₁ → f b b₁) (λ b₁ c r₁ → coh1 b b₁ c r₁) z)}
             (λ z p q i j →
               isSet→SquareP
                 {A = λ i' j' → P (eq/ a b r j') z}
                 (λ i' j' → isSetP (eq/ a b r j') z)
                 {a₀₀ = elim (isSetP [ a ]) (f a) (coh1 a) z}
                 {a₀₁ = elim (isSetP [ b ]) (f b) (coh1 b) z}
                 p
                 {a₁₀ = elim (isSetP [ a ]) (f a) (coh1 a) z}
                 {a₁₁ = elim (isSetP [ b ]) (f b) (coh1 b) z}
                 q
                 refl
                 refl
                 i j)
             (λ c → coh2 a b c r)
             z)
    x y


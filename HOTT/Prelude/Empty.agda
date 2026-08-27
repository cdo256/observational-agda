module HOTT.Prelude.Empty where

open import HOTT.Prelude.Universe
open import HOTT.Prelude.PrimitiveIdentity
open import HOTT.Prelude.ObservationalIdentity

data ⊥ : Type where

absurd : ∀ {ℓA} {A : Type ℓA} → ⊥ → A
absurd ()

postulate
  Id⊥ : ∀ x₀ x₁
    → Id ⊥ x₀ x₁
    ≡₀ ⊥

{-# REWRITE Id⊥ #-}

isFib⊥ : isFibrant ⊥
isFib⊥ .trr ()
isFib⊥ .liftr ()
isFib⊥ .trl ()
isFib⊥ .liftl ()
isFib⊥ .id ()

¬_ : ∀ {ℓA} (A : Type ℓA) → Type ℓA
¬ A = A → ⊥

_ : ∀ {ℓA} (A : Type ℓA) (x₀ x₁ : ¬ A)
  → Id (¬ A) x₀ x₁
  ≡₀ (∀ {a₀ a₁ : A} (a₂ : a₀ ≡ a₁)
      → x₀ a₀ ≡ x₁ a₁)
_ = λ _ _ _ → refl₀

{-
isFib¬ : ∀ {ℓA} (A : Type ℓA)
  → isFibrant A
  → isFibrant (¬ A)
isFib¬ A isFibA .trr x = x
isFib¬ A isFibA .liftr x₀ {a₀} {a₁} a₂ =
  absurd (x₀ a₀)
isFib¬ A isFibA .trl x = x
isFib¬ A isFibA .liftl x₁ {a₀} {a₁} a₂ =
  absurd (x₁ a₀)
isFib¬ A isFibA .id a₂₀ a₂₁ .trr x = x
isFib¬ A isFibA .id a₂₀ a₂₁ .liftr a₀ x₂ =
  {!!}
isFib¬ A isFibA .id a₂₀ a₂₁ .trl = {!!}
isFib¬ A isFibA .id a₂₀ a₂₁ .liftl = {!!}
isFib¬ A isFibA .id a₂₀ a₂₁ .id = {!!}
-}

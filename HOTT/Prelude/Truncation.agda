module HOTT.Prelude.Truncation where

open import HOTT.Prelude.Universe

data ∥_∥ (A : Type ℓA) : Prop ℓA where
  ∣_∣ : A → ∥ A ∥

Trunc₁ : {A : Type ℓA} {ℓB : Level} → (A → Type ℓB) → (A → Prop ℓB)
Trunc₁ R x = ∥ R x ∥

Trunc₂ : {A : Type ℓA} {ℓB : Level} → (A → A → Type ℓB) → (A → A → Prop ℓB)
Trunc₂ R x y = ∥ R x y ∥

data ∥_∥ˢ (A : Type ℓA) : SSet ℓA where
  ∣_∣ˢ : A → ∥ A ∥ˢ

∣_∣ˢ⁻ : {A : Type ℓA} → ∥ A ∥ˢ → A
∣ ∣ x ∣ˢ ∣ˢ⁻ = x

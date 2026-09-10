module HOTT.Prelude.HLevel where

open import HOTT.Prelude.Universe
open import HOTT.Prelude.Types
open import HOTT.Prelude.Truncation
open import HOTT.Prelude.Identity
open import HOTT.Prelude.Logic

isProp : Type ℓA → Type ℓA
isProp A = ∀ (x y : A) → x ≡ y

hProp : ∀ ℓA → Type (lsuc ℓA)
hProp ℓA = Σ (Type ℓA) isProp

isContr : Type ℓA → Type ℓA
isContr A = Σ A λ x → ∀ y → x ≡ y

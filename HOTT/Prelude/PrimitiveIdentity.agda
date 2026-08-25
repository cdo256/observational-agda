{-# OPTIONS --injective-type-constructors #-}
module HOTT.Prelude.PrimitiveIdentity where

open import HOTT.Prelude.Universe

infix 4 _≡₀_
data _≡₀_ {ℓ} {A : Type ℓ} : (x y : A) → Prop ℓ where
  refl₀ : ∀ {x} → x ≡₀ x

{-# BUILTIN EQUALITY _≡₀_ #-}
{-# BUILTIN REWRITE _≡₀_ #-}

postulate
  subst₀ : ∀ {ℓA ℓB} {A : Type ℓA}
    → (B : A → Type ℓB)
    → {x y : A} → x ≡₀ y
    → B x → B y

data _≡ˢ_ {ℓA} {A : Type ℓA} : (x y : A) → Type ℓA where
  reflˢ : ∀ {x} → x ≡ˢ x

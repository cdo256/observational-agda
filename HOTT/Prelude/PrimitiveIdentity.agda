module HOTT.Prelude.PrimitiveIdentity where

open import HOTT.Prelude.Universe

infix 4 _≡₀_
data _≡₀_ {ℓA} {A : Type ℓA} : (x y : A) → Set ℓA where
  refl₀ : ∀ {x} → x ≡₀ x

-- Alias
Id₀ : ∀ {ℓA} (A : Type ℓA) (x y : A) → Set ℓA
Id₀ A x y = x ≡₀ y

{-# BUILTIN EQUALITY _≡₀_ #-}
{-# BUILTIN REWRITE _≡₀_ #-}

sym₀ : ∀ {ℓA} {A : Type ℓA}
  → {x y : A} → x ≡₀ y
  → y ≡₀ x
sym₀ refl₀ = refl₀

trans₀ : ∀ {ℓA} {A : Type ℓA}
  → {x y z : A}
  → x ≡₀ y
  → y ≡₀ z
  → x ≡₀ z
trans₀ refl₀ p = p

ap₀ : ∀ {ℓA ℓB} {A : Type ℓA}
  → {B : Type ℓB}
  → (f : A → B)
  → {x y : A}
  → x ≡₀ y
  → f x ≡₀ f y
ap₀ B refl₀ = refl₀

ap²₀ : ∀ {ℓA ℓB ℓC}
  → {A : Type ℓA}
  → {B : Type ℓB}
  → {C : Type ℓC}
  → (f : A → B → C)
  → {a₀ a₁ : A}
  → (a₂ : a₀ ≡₀ a₁)
  → {b₀ b₁ : B}
  → (b₂ : b₀ ≡₀ b₁)
  → f a₀ b₀ ≡₀ f a₁ b₁
ap²₀ f refl₀ refl₀ = refl₀

subst₀ : ∀ {ℓA ℓB} {A : Type ℓA}
  → (B : A → Type ℓB)
  → {x y : A} → x ≡₀ y
  → B x → B y
subst₀ B refl₀ b = b

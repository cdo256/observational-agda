{-# OPTIONS --injective-type-constructors #-}
{-# OPTIONS --confluence-check #-}
module HOTT.Prelude.ObservationalIdentity where

open import HOTT.Prelude.PrimitiveIdentity
open import HOTT.Prelude.Universe

postulate
  Id : ∀ {ℓA} → (A : Type ℓA)
    → (a₀ : A) (a₁ : A)
    → Type ℓA
  refl : ∀ {ℓA} → (A : Type ℓA)
    → (a : A)
    → Id A a a

postulate
  IdType : ∀ {ℓA}
    → (A₀ A₁ : Type ℓA)
    → Id (Type ℓA) A₀ A₁
    ≡₀ ((a₀ : A₀) → (a₁ : A₁) → Type ℓA)

{-# REWRITE IdType #-}

postulate
  reflType : ∀ {ℓA}
    → (A : Type ℓA)
    → refl (Type ℓA) A
    ≡₀ (λ (a₀ a₁ : A) → Id A a₀ a₁)
    
{-# REWRITE reflType #-}

_≡_ : {A : Type ℓA}
  → (a₀ : A) (a₁ : A)
  → Type ℓA
a₀ ≡ a₁ = Id _ a₀ a₁

-- Required for bootstrapping.
postulate
  ap : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : Type ℓB}
    → (f : A → B)
    → (∀ {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
        → f x₀ ≡ f x₁)

postulate
  IdΠ : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : A → Type ℓB}
    → (f₀ f₁ : (a : A) → B a)
    → Id ((a : A) → B a) f₀ f₁
    ≡₀ (∀ {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
        → ap B x₂ (f₀ x₀) (f₁ x₁))

{-# REWRITE IdΠ #-}

refl₂ : ∀ {ℓA}
  → {A₀ A₁ : Type ℓA}
  → (A₂ : A₀ ≡ A₁)
  → {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
  → Id (Type ℓA) (A₂ a₀₀ a₁₀) (A₂ a₀₁ a₁₁)
refl₂ {ℓA} {A₀} {A₁} A₂ {a₀₀} {a₀₁} {a₁₀} {a₁₁} a₂₀ a₂₁ =
  {!!}
  where
  u : ap (λ a → ap A₂ {!b!})  {!!}

{-
record isBisim {ℓA} {A₀ A₁ : Type ℓA}
  (A₂ : A₀ → A₁ → Type ℓA)
  : Type ℓA where
  coinductive
  field
    trr : A₀ → A₁
    liftr : (a₀ : A₀) → A₂ a₀ (trr a₀)
    trl : A₁ → A₀
    liftl : (a₁ : A₁) → A₂ (trl a₁) a₁
    id : {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
      → (a₂₀ : A₂ a₀₀ a₁₀) 
      → (a₂₁ : A₂ a₀₁ a₁₁) 
      → isBisim
        {A₀ = Id A₀ a₀₀ a₀₁}
        {A₁ = Id A₁ a₁₀ a₁₁}
        λ a₀₂ a₁₂ → refl₂ {!!} {!!} {!!} {!!} {!!}
-}

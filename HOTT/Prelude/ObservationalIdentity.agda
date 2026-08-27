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

postulate
  apConst : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : Type ℓB}
    → {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
    → ap (λ (_ : A) → B) x₂
    ≡₀ Id B

{-# REWRITE apConst #-}

postulate
  apRefl : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : A → Type ℓB}
    → (x : A)
    → ap B (refl A x)
    ≡₀ Id (B x)

{-# REWRITE apRefl #-}

postulate
  reflΠ : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : A → Type ℓB}
    → (f : (a : A) → B a)
    → (x : A)
    → refl ((a : A) → B a) f (refl A x)
    ≡₀ refl (B x) (f x)

-- {-# REWRITE reflΠ #-}

postulate
  apβ : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : Type ℓB}
    → (f : A → B)
    → Id₀ (Id (A → B) f f)
          (ap f)
          (refl (A → B) f)

record Σ {ℓA ℓB} (A : Type ℓA) (B : A → Type ℓB)
  : Type (ℓA ⊔ ℓB) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

_×_ : (A : Type ℓA) (B : Type ℓB) → Type (ℓA ⊔ ℓB)
A × B = Σ A (λ _ → B)

postulate
  IdΣ : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : A → Type ℓB}
    → (x₀ x₁ : Σ A B)
    → Id (Σ A B) x₀ x₁
    ≡₀ Σ (x₀ .fst ≡ x₁ .fst)
         (λ a₂ → ap B a₂ (x₀ .snd) (x₁ .snd))
      
{-# REWRITE IdΣ #-}

postulate
  reflΣ : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : A → Type ℓB}
    → (x : Σ A B)
    → Id₀ (Id (Σ A B) x x)
          (refl (Σ A B) x)
          (refl A (x .fst) , refl (B (x .fst)) (x .snd))
    
{-# REWRITE reflΣ #-}

refl₂ : ∀ {ℓA}
  → {A₀ A₁ : Type ℓA}
  → (A₂ : A₀ ≡ A₁)
  → {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
  → (a₂₀ : A₂ a₀₀ a₁₀) 
  → (a₂₁ : A₂ a₀₁ a₁₁) 
  → Id A₀ a₀₀ a₀₁ ≡ Id A₁ a₁₀ a₁₁
refl₂ {A₀ = A₀} {A₁} A₂ a₂₀ a₂₁ a₀₂ a₁₂ =
  ap (λ ((a , b) : A₀ × A₁) → A₂ a b) (a₀₂ , a₁₂) a₂₀ a₂₁

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
      → isBisim (refl₂ A₂ a₂₀ a₂₁)

isFibrant : ∀ {ℓA} → Type ℓA → Type ℓA
isFibrant {ℓA} A = isBisim (refl (Type ℓA) A)

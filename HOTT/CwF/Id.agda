module HOTT.CwF.Id where

open import HOTT.Prelude hiding (_,_; refl)
open import HOTT.CwF.Base
open import HOTT.CwF.Con
open import HOTT.CwF.Sub

postulate
  U : ∀ {Γ} → Ty Γ

  U[] : ∀ {Γ Δ}
    → (σ : Sub Δ Γ)
    → U [ σ ]ᵀ ≡ U

{-# REWRITE U[] #-}

postulate
  El : ∀ {Γ} → Tm Γ U → Ty Γ

  El[] : ∀ {Γ Δ}
    → (σ : Sub Δ Γ)
    → (A : Tm Γ U)
    → El A [ σ ]ᵀ ≡ El (A [ σ ]ᵗ)

{-# REWRITE El[] #-}

postulate
  Id : ∀ {Γ}
    → (A : Ty Γ)
    → (a₀ : Tm Γ A)
    → (a₁ : Tm Γ A)
    → Type

{-
  ⟨_⟩ⁱ : ∀ {Γ}
    → {A : Ty Γ}
    → {a₀ : Tm Γ A}
    → {a₁ : Tm Γ A}
    → Id A a₀ a₁
    → Ty Γ

  refl : ∀ {Γ}
    → (A : Ty Γ)
    → (a : Tm Γ A)
    → Id A a a

postulate
  reflU : ∀ {Γ}
    → (A : Tm Γ U)
    → ⟨ refl U A ⟩ᴵ ≡ {!!}

postulate
  Id* : ∀ {Γ}
    → (A₀ A₁ : Ty Γ)
    → (A₂ : IdU Γ A₀ A₁)
    → (a₀ : Tm Γ A₀)
    → (a₁ : Tm Γ A₁)
    → Ty Γ

  Id

  refl : ∀ {Γ}
    → (A : Ty Γ)
    → (a : Tm Γ A)
    → Tm Γ (Id A a a)

sq : ∀ {Γ}
  → (A : Ty Γ)
  → {a₀₀ : Tm Γ A}
  → {a₁₀ : Tm Γ A}
  → {a₀₁ : Tm Γ A}
  → {a₁₁ : Tm Γ A}
  → (a₂₀ : Tm Γ (Id A a₀₀ a₁₀))
  → (a₂₁ : Tm Γ (Id A a₀₁ a₁₁))
  → (a₀₂ : Tm Γ (Id A a₀₀ a₀₁))
  → (a₁₂ : Tm Γ (Id A a₁₀ a₁₁))
  → Tm Γ (Id {!!} a₀₂ {!a₁₂!})
-}

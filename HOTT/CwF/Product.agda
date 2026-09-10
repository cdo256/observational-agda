module HOTT.CwF.Product where

open import HOTT.Prelude hiding (_,_; _×_)
open import HOTT.CwF.Base
open import HOTT.CwF.Con
open import HOTT.CwF.Sub

postulate
  _×_ : ∀ {Γ}
    → (A : Ty Γ)
    → (B : Ty Γ)
    → Ty Γ

  ×[] : ∀ {Γ Δ} (σ : Sub Δ Γ)
    → (A : Ty Γ)
    → (B : Ty Γ)
    → (A × B) [ σ ]ᵀ ≡ (A [ σ ]ᵀ × B [ σ ]ᵀ)

{-# REWRITE ×[] #-}

postulate
  ×i : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty Γ}
    → (a : Tm Γ A)
    → (b : Tm Γ B)
    → Tm Γ (A × B)

  ×i[] : ∀ {Γ Δ}
    → (σ : Sub Δ Γ)
    → {A : Ty Γ}
    → {B : Ty Γ}
    → (a : Tm Γ A)
    → (b : Tm Γ B)
    → (×i a b) [ σ ]ᵗ ≡ (×i (a [ σ ]ᵗ) (b [ σ ]ᵗ))

{-# REWRITE ×i[] #-}

postulate
  ×e₁
    : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty Γ}
    → (p : Tm Γ (A × B))
    → Tm Γ A

  ×e₂
    : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty Γ}
    → (p : Tm Γ (A × B))
    → Tm Γ B

  ×β₁
    : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty Γ}
    → (a : Tm Γ A)
    → (b : Tm Γ B)
    → ×e₁ (×i a b) ≡ a

  ×β₂
    : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty Γ}
    → (a : Tm Γ A)
    → (b : Tm Γ B)
    → ×e₂ (×i a b) ≡ b

postulate
  ×e₁[]
    : ∀ {Γ Δ}
    → (σ : Sub Δ Γ)
    → {A B : Ty Γ}
    → (p : Tm Γ (A × B))
    → (×e₁ p) [ σ ]ᵗ ≡ ×e₁ (p [ σ ]ᵗ)

  ×e₂[]
    : ∀ {Γ Δ}
    → (σ : Sub Δ Γ)
    → {A B : Ty Γ}
    → (p : Tm Γ (A × B))
    → (×e₂ p) [ σ ]ᵗ ≡ ×e₂ (p [ σ ]ᵗ)

{-# REWRITE ×e₁[] ×e₂[] ×β₁ ×β₂ #-}

postulate
  ×η
    : ∀ {Γ}
    → {A B : Ty Γ}
    → (p : Tm Γ (A × B))
    → ×i (×e₁ p) (×e₂ p) ≡ p

module HOTT.CwF.Bool where

open import HOTT.Prelude hiding (_,_)
open import HOTT.CwF.Base
open import HOTT.CwF.Con
open import HOTT.CwF.Sub

postulate
  𝔹 : ∀ {Γ} → Ty Γ

  𝔹[] : ∀ {Γ Δ} (σ : Sub Δ Γ)
       → 𝔹 [ σ ]ᵀ ≡ 𝔹

{-# REWRITE 𝔹[] #-}

postulate
  𝔹i₁ : ∀ {Γ} → Tm Γ 𝔹

  𝔹i₁[] : ∀ {Γ Δ} (σ : Sub Δ Γ)
        → 𝔹i₁ [ σ ]ᵗ ≡ 𝔹i₁

  𝔹i₂ : ∀ {Γ} → Tm Γ 𝔹

  𝔹i₂[] : ∀ {Γ Δ} (σ : Sub Δ Γ)
        → 𝔹i₂ [ σ ]ᵗ ≡ 𝔹i₂

{-# REWRITE 𝔹i₁[] 𝔹i₂[] #-}

postulate
  𝔹e
    : ∀ {Γ}
    → (A : Ty (Γ ▹ 𝔹))
    → Tm Γ (A [ id , 𝔹i₁ ]ᵀ)
    → Tm Γ (A [ id , 𝔹i₂ ]ᵀ)
    → (t : Tm Γ 𝔹)
    → Tm Γ (A [ id , t ]ᵀ)

  𝔹β₁
    : ∀ {Γ}
    → (A : Ty (Γ ▹ 𝔹))
    → (a : Tm Γ (A [ id , 𝔹i₁ ]ᵀ))
    → (b : Tm Γ (A [ id , 𝔹i₂ ]ᵀ))
    → 𝔹e A a b 𝔹i₁ ≡ a

  𝔹β₂
    : ∀ {Γ}
    → (A : Ty (Γ ▹ 𝔹))
    → (a : Tm Γ (A [ id , 𝔹i₁ ]ᵀ))
    → (b : Tm Γ (A [ id , 𝔹i₂ ]ᵀ))
    → 𝔹e A a b 𝔹i₂ ≡ b

{-# REWRITE 𝔹β₁ 𝔹β₂ #-}

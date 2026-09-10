module HOTT.CwF.Function where

open import HOTT.Prelude hiding (_,_)
open import HOTT.CwF.Base
open import HOTT.CwF.Con
open import HOTT.CwF.Sub

postulate
  ⇨ : ∀ {Γ}
    → (A : Ty Γ)
    → (B : Ty Γ)
    → Ty Γ

  ⇨[] : ∀ {Γ Δ} (σ : Sub Δ Γ)
    → (A : Ty Γ)
    → (B : Ty Γ)
    → (⇨ A B) [ σ ]ᵀ
    ≡ (⇨ (A [ σ ]ᵀ) (B [ σ ]ᵀ))

{-# REWRITE ⇨[] #-}

postulate
  ⇨i : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty Γ}
    → (f : Tm (Γ ▹ A) (B [ wk ]ᵀ))
    → Tm Γ (⇨ A B)

postulate
  ⇨i[] : ∀ {Γ Δ}
    → (σ : Sub Δ Γ)
    → {A : Ty Γ}
    → {B : Ty Γ}
    → (f : Tm (Γ ▹ A) (B [ wk ]ᵀ))
    → ⇨i f [ σ ]ᵗ
    ≡ ⇨i (f [ σ ↑ A ]ᵗ)

{-# REWRITE ⇨i[] #-}

postulate
  ⇨e
    : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty Γ}
    → (f : Tm Γ (⇨ A B))
    → (x : Tm Γ A)
    → Tm Γ B

  ⇨β
    : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty Γ}
    → (f : Tm (Γ ▹ A) (B [ wk ]ᵀ))
    → (x : Tm Γ A)
    → ⇨e (⇨i f) x
    ≡ f [ id , x ]ᵗ

{-# REWRITE ⇨β #-}

postulate
  ⇨e[]
    : ∀ {Γ Δ}
    → (σ : Sub Δ Γ)
    → {A : Ty Γ}
    → {B : Ty Γ}
    → (f : Tm Γ (⇨ A B))
    → (x : Tm Γ A)
    → ⇨e f x [ σ ]ᵗ
    ≡ ⇨e (f [ σ ]ᵗ) (x [ σ ]ᵗ)

{-# REWRITE ⇨e[] #-}

postulate
  ⇨η
    : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty Γ}
    → (f : Tm Γ (⇨ A B))
    → (x : Tm Γ A)
    -- λ x . f x ≡ f
    → ⇨i (⇨e (f [ wk ]ᵗ) vz) ≡ f

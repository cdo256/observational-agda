{-# OPTIONS --allow-unsolved-metas #-}
module HOTT.CwF.Proj where

open import HOTT.Prelude hiding (_,_)
open import HOTT.CwF.Cube
open import HOTT.CwF.Sorts
open import HOTT.CwF.Sub

infixl 30 _⟨_⟩ᶜ _⟨_⟩ᵀ
-- _⟨_⟩ᵗ _⟨_⟩ˢ

postulate
  _⟨_⟩ᶜ : ∀ {m n}
    → Con n
     → CubeMap m n
    → Con m

  ⟨id⟩ᶜ : ∀ {n}
    → (Γ : Con n)
     → Γ ⟨ idᵐ n ⟩ᶜ ≡ Γ

  ⟨∘⟩ᶜ : ∀ {l m n}
    → (Γ : Con n)
      → (i* : CubeMap m n)
      → (j* : CubeMap l m)
      → (Γ ⟨ i* ⟩ᶜ) ⟨ j* ⟩ᶜ ≡ Γ ⟨ j* ∘ᵐ i* ⟩ᶜ

  ∙⟨⟩ᶜ : ∀ {m n}
      → (i* : CubeMap m n)
     → ∙ ⟨ i* ⟩ᶜ ≡ ∙

{-# REWRITE ⟨id⟩ᶜ ⟨∘⟩ᶜ ∙⟨⟩ᶜ #-}

Proj : ∀ {m n} → Con m → CubeMap m n → Con n → Type
Proj Γ i* Δ = Sub Γ (Δ ⟨ i* ⟩ᶜ)

Idᶜ : ∀ {n}
  → (Γ : Con n)
  → Con (ds n)
Idᶜ {n} Γ = Γ ⟨ geᵐ ⟩ᶜ

postulate
  _⟨_⟩ᵀ : ∀ {m n} {Γ : Con n}
    → Ty Γ
      → (i* : CubeMap m n)
     → Ty (Γ ⟨ i* ⟩ᶜ)

  ⟨id⟩ᵀ : ∀ {n} {Γ : Con n}
    → (A : Ty Γ)
     → A ⟨ idᵐ n ⟩ᵀ
    ≡ A

  ⟨∘⟩ᵀ : ∀ {l m n} {Γ : Con n}
    → (A : Ty Γ)
      → (i* : CubeMap m n)
      → (j* : CubeMap l m)
      → (A ⟨ i* ⟩ᵀ) ⟨ j* ⟩ᵀ
      ≡ A ⟨ j* ∘ᵐ i* ⟩ᵀ

{-# REWRITE ⟨id⟩ᵀ ⟨∘⟩ᵀ #-}

postulate
  ▹⟨⟩ᶜ : ∀ {m n} {Γ : Con n}
    → (A : Ty Γ)
      → (i* : CubeMap m n)
     → (Γ ▹ A) ⟨ i* ⟩ᶜ
      ≡ ((Γ ⟨ i* ⟩ᶜ) ▹ (A ⟨ i* ⟩ᵀ))

{-# REWRITE ▹⟨⟩ᶜ #-}

postulate
  _⟨_⟩ᵗ : ∀ {m n} {Γ : Con n} {A : Ty Γ}
    → Tm Γ A
      → (i* : CubeMap m n)
     → Tm (Γ ⟨ i* ⟩ᶜ) (A ⟨ i* ⟩ᵀ)

  ⟨id⟩ᵗ : ∀ {n} {Γ : Con n} {A : Ty Γ}
    → (a : Tm Γ A)
     → a ⟨ idᵐ n ⟩ᵗ
    ≡ a

  ⟨∘⟩ᵗ : ∀ {l m n} {Γ : Con n} {A : Ty Γ}
    → (a : Tm Γ A)
      → (i* : CubeMap m n)
      → (j* : CubeMap l m)
     → (a ⟨ i* ⟩ᵗ) ⟨ j* ⟩ᵗ
      ≡ a ⟨ j* ∘ᵐ i* ⟩ᵗ

{-# REWRITE ⟨id⟩ᵗ ⟨∘⟩ᵗ #-}

postulate
  _⟨_⟩ˢ : ∀ {m n} {Γ Δ : Con n}
    → Sub Γ Δ
      → (i* : CubeMap m n)
     → Sub (Γ ⟨ i* ⟩ᶜ) (Δ ⟨ i* ⟩ᶜ)

  ⟨id⟩ˢ : ∀ {n} {Γ Δ : Con n}
    → (σ : Sub Γ Δ)
     → σ ⟨ idᵐ n ⟩ˢ
    ≡ σ

  ⟨∘⟩ˢ : ∀ {l m n} {Γ Δ : Con n}
    → (σ : Sub Γ Δ)
      → (i* : CubeMap m n)
      → (j* : CubeMap l m)
     → (σ ⟨ i* ⟩ˢ) ⟨ j* ⟩ˢ
      ≡ σ ⟨ j* ∘ᵐ i* ⟩ˢ

{-# REWRITE ⟨id⟩ˢ ⟨∘⟩ˢ #-}

postulate
  []⟨⟩ᵀ :
    ∀ {m n}
    → {Γ Δ : Con n}
    → (A : Ty Δ)
    → (σ : Sub Γ Δ)
      → (i* : CubeMap m n)
     → (A [ σ ]ᵀ) ⟨ i* ⟩ᵀ
     ≡ (A ⟨ i* ⟩ᵀ) [ σ ⟨ i* ⟩ˢ ]ᵀ

{-# REWRITE []⟨⟩ᵀ #-}

postulate
  []⟨⟩ᵗ :
    ∀ {m n}
    → {Γ Δ : Con n}
    → {A : Ty Δ}
    → (a : Tm Δ A)
    → (σ : Sub Γ Δ)
      → (i* : CubeMap m n)
     → (a [ σ ]ᵗ) ⟨ i* ⟩ᵗ
     ≡ (a ⟨ i* ⟩ᵗ) [ σ ⟨ i* ⟩ˢ ]ᵗ

{-# REWRITE []⟨⟩ᵗ #-}

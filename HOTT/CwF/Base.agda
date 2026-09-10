{-# OPTIONS --rewriting #-}

module HOTT.CwF.Base where

open import Agda.Primitive
open import Agda.Builtin.Equality

{-# BUILTIN REWRITE _≡_ #-}

------------------------------------------------------------------------
-- The four sorts

postulate
  Con : Set 

  Sub : Con → Con → Set 

  Ty  : Con → Set 

  Tm  : (Γ : Con) → Ty Γ → Set 

------------------------------------------------------------------------
-- Category of contexts and substitutions

postulate
  id  : ∀ {Γ}
      → Sub Γ Γ

  _∘_ : ∀ {Γ Δ Θ}
      → Sub Δ Γ
      → Sub Θ Δ
      → Sub Θ Γ

infixr 40 _∘_

postulate
  idl : ∀ {Γ Δ} (σ : Sub Δ Γ)
      → id ∘ σ ≡ σ

  idr : ∀ {Γ Δ} (σ : Sub Δ Γ)
      → σ ∘ id ≡ σ

  assoc
    : ∀ {Γ Δ Θ Ξ}
      (σ : Sub Δ Γ)
      (δ : Sub Θ Δ)
      (ν : Sub Ξ Θ)
    → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)

------------------------------------------------------------------------
-- Substitution into types

postulate
  _[_]ᵀ : ∀ {Γ Δ}
         → Ty Γ
         → Sub Δ Γ
         → Ty Δ

infixl 50 _[_]ᵀ

postulate
  Ty-id
    : ∀ {Γ} (A : Ty Γ)
    → A [ id ]ᵀ ≡ A

  Ty-∘
    : ∀ {Γ Δ Θ}
      (A : Ty Γ)
      (σ : Sub Δ Γ)
      (δ : Sub Θ Δ)
    → (A [ σ ]ᵀ) [ δ ]ᵀ ≡ A [ σ ∘ δ ]ᵀ

{-# REWRITE Ty-id Ty-∘ #-}

------------------------------------------------------------------------
-- Substitution into terms

postulate
  _[_]ᵗ
    : ∀ {Γ Δ} {A : Ty Γ}
    → Tm Γ A
    → (σ : Sub Δ Γ)
    → Tm Δ (A [ σ ]ᵀ)

infixl 50 _[_]ᵗ

postulate
  Tm-id
    : ∀ {Γ} {A : Ty Γ}
      (t : Tm Γ A)
    → t [ id ]ᵗ ≡ t

  Tm-∘
    : ∀ {Γ Δ Θ} {A : Ty Γ}
      (t : Tm Γ A)
      (σ : Sub Δ Γ)
      (δ : Sub Θ Δ)
    → (t [ σ ]ᵗ) [ δ ]ᵗ ≡ t [ σ ∘ δ ]ᵗ

{-# REWRITE Tm-id Tm-∘ #-}

------------------------------------------------------------------------
-- Empty context

postulate
  ∙ : Con

  ε : ∀ {Γ}
    → Sub Γ ∙

  εη : ∀ {Γ}
      (σ : Sub Γ ∙)
    → σ ≡ ε

------------------------------------------------------------------------
-- Context extension

postulate
  _▹_ : (Γ : Con)
      → Ty Γ
      → Con

infixl 30 _▹_

postulate
  p : ∀ {Γ A}
    → Sub (Γ ▹ A) Γ

  q : ∀ {Γ A}
    → Tm (Γ ▹ A) (A [ p ]ᵀ)

  _,_ : ∀ {Γ Δ A}
      → (σ : Sub Δ Γ)
      → Tm Δ (A [ σ ]ᵀ)
      → Sub Δ (Γ ▹ A)

infixr 20 _,_

------------------------------------------------------------------------
-- Comprehension equations

postulate
  ▹β₁
    : ∀ {Γ Δ A}
      (σ : Sub Δ Γ)
      (t : Tm Δ (A [ σ ]ᵀ))
    → p ∘ (σ , t) ≡ σ

{-# REWRITE ▹β₁ #-}

postulate
  ▹β₂
    : ∀ {Γ Δ A}
      (σ : Sub Δ Γ)
      (t : Tm Δ (A [ σ ]ᵀ))
    → q [ σ , t ]ᵗ ≡ t

{-# REWRITE ▹β₂ #-}

postulate
  ▹η
    : ∀ {Γ Δ A}
      (σ : Sub Δ (Γ ▹ A))
    → (p ∘ σ , q [ σ ]ᵗ) ≡ σ

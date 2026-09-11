module HOTT.CwF.Sub where

open import HOTT.Prelude hiding (_,_)
open import HOTT.CwF.Cube
open import HOTT.CwF.Sorts

infixr 20 _,_
infixl 25 _▹_
infixl 30 _[_]ᵀ _[_]ᵗ
infixr 40 _∘_

postulate
  ∙ : ∀ {n} → Con n

  ε : ∀ {n}
    → {Γ : Con n}
    → Sub Γ ∙

  εη : ∀ {n}
    → {Γ : Con n}
    → (σ : Sub Γ ∙)
    → σ ≡ ε

postulate
  _▹_ : ∀ {n}
    →(Γ : Con n)
    → Ty Γ
    → Con n

------------------------------------------------------------------------
-- Category of contexts and substitutions

postulate
  id : ∀ {n} {Γ : Con n}
    → Sub Γ Γ

  _∘_ : ∀ {n} {Γ Δ Θ : Con n}
    → Sub Δ Γ
    → Sub Θ Δ
    → Sub Θ Γ

postulate
  idl : ∀ {n} {Γ Δ : Con n} (σ : Sub Δ Γ)
    → id ∘ σ ≡ σ

  idr : ∀ {n} {Γ Δ : Con n} (σ : Sub Δ Γ)
    → σ ∘ id ≡ σ

  assoc
    : ∀ {n} {Γ Δ Θ Ξ : Con n}
    → (σ : Sub Δ Γ)
    → (δ : Sub Θ Δ)
    → (ν : Sub Ξ Θ)
    → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)

{-# REWRITE idl idr assoc #-}


------------------------------------------------------------------------
-- Substitution into types

postulate
  _[_]ᵀ : ∀ {n} {Γ Δ : Con n}
    → Ty Γ
    → Sub Δ Γ
    → Ty Δ

postulate
  [id]ᵀ : ∀ {n} {Γ : Con n}
    → (A : Ty Γ)
    → A [ id ]ᵀ ≡ A

  [∘]ᵀ
     : ∀ {n} {Γ Δ Θ : Con n}
    → (A : Ty Γ)
    → (σ : Sub Δ Γ)
    → (δ : Sub Θ Δ)
    → (A [ σ ]ᵀ) [ δ ]ᵀ ≡ A [ σ ∘ δ ]ᵀ

{-# REWRITE [id]ᵀ [∘]ᵀ #-}

------------------------------------------------------------------------
-- Substitution into terms

postulate
  _[_]ᵗ : ∀ {n} {Γ Δ : Con n}
    → {A : Ty Γ}
    → Tm Γ A
    → (σ : Sub Δ Γ)
    → Tm Δ (A [ σ ]ᵀ)

postulate
  [id]ᵗ
    : ∀ {n} {Γ : Con n} {A : Ty Γ}
    → (t : Tm Γ A)
    → t [ id ]ᵗ ≡ t

  [∘]ᵗ
    : ∀ {n} {Γ Δ Θ : Con n} {A : Ty Γ}
    → (t : Tm Γ A)
    → (σ : Sub Δ Γ)
    → (δ : Sub Θ Δ)
    → (t [ σ ]ᵗ) [ δ ]ᵗ ≡ t [ σ ∘ δ ]ᵗ

{-# REWRITE [id]ᵗ [∘]ᵗ #-}

------------------------------------------------------------------------
-- Context extension

postulate
  wk : ∀ {n} {Γ : Con n} {A : Ty Γ}
    → Sub (Γ ▹ A) Γ

  vz : ∀ {n} {Γ : Con n} {A : Ty Γ}
    → Tm (Γ ▹ A) (A [ wk ]ᵀ)

  _,_ : ∀ {n} {Γ Δ : Con n} {A : Ty Γ}
    → (σ : Sub Δ Γ)
    → Tm Δ (A [ σ ]ᵀ)
    → Sub Δ (Γ ▹ A)

------------------------------------------------------------------------
-- Comprehension equations

postulate
  ▹β₁ : ∀ {n} {Γ Δ : Con n} {A : Ty Γ}
    → (σ : Sub Δ Γ)
    → (t : Tm Δ (A [ σ ]ᵀ))
    → wk ∘ (σ , t) ≡ σ

{-# REWRITE ▹β₁ #-}

postulate
  ▹β₂ : ∀ {n} {Γ Δ : Con n} {A : Ty Γ}
    → (σ : Sub Δ Γ)
    → (t : Tm Δ (A [ σ ]ᵀ))
    → vz [ σ , t ]ᵗ ≡ t

{-# REWRITE ▹β₂ #-}

postulate
  ▹η : ∀ {n} {Γ Δ : Con n} {A : Ty Γ}
    → (σ : Sub Δ (Γ ▹ A))
    → (wk ∘ σ , vz [ σ ]ᵗ) ≡ σ

vs
  : ∀ {n} {Γ : Con n}
  → {A B : Ty Γ}
  → Tm Γ B
  → Tm (Γ ▹ A) (B [ wk ]ᵀ)
vs b = b [ wk ]ᵗ

wkᵀ
  : ∀ {n} {Γ : Con n}
  → {A : Ty Γ}
  → Ty Γ
  → Ty (Γ ▹ A)
wkᵀ B = B [ wk ]ᵀ

_↑_
  : ∀ {n} {Γ Δ : Con n}
  → (σ : Sub Δ Γ)
  → (A : Ty Γ)
  → Sub (Δ ▹ A [ σ ]ᵀ) (Γ ▹ A)
σ ↑ A = (σ ∘ wk , vz)

postulate
  ,∘
    : ∀ {n} {Γ Δ Θ : Con n}
    → {A : Ty Γ}
    → (σ : Sub Δ Γ)
    → (a : Tm Δ (A [ σ ]ᵀ))
    → (δ : Sub Θ Δ)
    → (σ , a) ∘ δ
    ≡ (σ ∘ δ , a [ δ ]ᵗ)

{-# REWRITE ,∘ #-}

postulate
  []∘ : ∀ {n} {Γ Δ : Con n}
    → (σ : Sub Δ Γ)
    → {A : Ty Γ}
    → (B : Ty (Γ ▹ A))
    → (a : Tm Γ A)
    → B [ (id , a) ∘ σ ]ᵀ
    ≡ B [ (σ ↑ A) ∘ (id , a [ σ ]ᵗ) ]ᵀ


module HOTT.CwF.Sub where

open import HOTT.Prelude hiding (_,_)
open import HOTT.CwF.Base
open import HOTT.CwF.Con

------------------------------------------------------------------------
-- Category of contexts and substitutions

postulate
  id : ∀ {Γ}
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
    → (σ : Sub Δ Γ)
    → (δ : Sub Θ Δ)
    → (ν : Sub Ξ Θ)
    → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)

{-# REWRITE idl idr assoc #-}

{-
Then you must also solve the identity and pentagon monoidal laws, for instance both paths:

A [ σ ∘ id ]
  ≡⟨ A [ idr ] ⟩
A [ σ ]

A [ σ ∘ id ]
  ≡⟨ Ty-∘ ⟩
A [ σ ] [ id ]
  ≡⟨ Ty-id ⟩
A [ σ ]

must be equal.

This is easy under UIP of course. I did want to avoid UIP here though.
-}

------------------------------------------------------------------------
-- Substitution into types

postulate
  _[_]ᵀ : ∀ {Γ Δ}
    → Ty Γ
    → Sub Δ Γ
    → Ty Δ

infixl 50 _[_]ᵀ

postulate
  Ty-id : ∀ {Γ}
    → (A : Ty Γ)
    → A [ id ]ᵀ ≡ A

  Ty-∘
    : ∀ {Γ Δ Θ}
    → (A : Ty Γ)
    → (σ : Sub Δ Γ)
    → (δ : Sub Θ Δ)
    → (A [ σ ]ᵀ) [ δ ]ᵀ ≡ A [ σ ∘ δ ]ᵀ

{-# REWRITE Ty-id Ty-∘ #-}

------------------------------------------------------------------------
-- Substitution into terms

postulate
  _[_]ᵗ : ∀ {Γ Δ}
    → {A : Ty Γ}
    → Tm Γ A
    → (σ : Sub Δ Γ)
    → Tm Δ (A [ σ ]ᵀ)

infixl 50 _[_]ᵗ

postulate
  Tm-id
    : ∀ {Γ} {A : Ty Γ}
    → (t : Tm Γ A)
    → t [ id ]ᵗ ≡ t

  Tm-∘
    : ∀ {Γ Δ Θ} {A : Ty Γ}
    → (t : Tm Γ A)
    → (σ : Sub Δ Γ)
    → (δ : Sub Θ Δ)
    → (t [ σ ]ᵗ) [ δ ]ᵗ ≡ t [ σ ∘ δ ]ᵗ

{-# REWRITE Tm-id Tm-∘ #-}

------------------------------------------------------------------------
-- Context extension

postulate
  wk : ∀ {Γ A}
    → Sub (Γ ▹ A) Γ

  vz : ∀ {Γ A}
    → Tm (Γ ▹ A) (A [ wk ]ᵀ)

  _,_ : ∀ {Γ Δ A}
    → (σ : Sub Δ Γ)
    → Tm Δ (A [ σ ]ᵀ)
    → Sub Δ (Γ ▹ A)

infixr 20 _,_

------------------------------------------------------------------------
-- Comprehension equations

postulate
  ▹β₁ : ∀ {Γ Δ A}
    → (σ : Sub Δ Γ)
    → (t : Tm Δ (A [ σ ]ᵀ))
    → wk ∘ (σ , t) ≡ σ

{-# REWRITE ▹β₁ #-}

postulate
  ▹β₂ : ∀ {Γ Δ A}
    → (σ : Sub Δ Γ)
    → (t : Tm Δ (A [ σ ]ᵀ))
    → vz [ σ , t ]ᵗ ≡ t

{-# REWRITE ▹β₂ #-}

postulate
  ▹η : ∀ {Γ Δ A}
    → (σ : Sub Δ (Γ ▹ A))
    → (wk ∘ σ , vz [ σ ]ᵗ) ≡ σ

vs
  : ∀ {Γ}
  → {A B : Ty Γ}
  → Tm Γ B
  → Tm (Γ ▹ A) (B [ wk ]ᵀ)
vs b = b [ wk ]ᵗ

wkᵀ
  : ∀ {Γ}
  → {A : Ty Γ}
  → Ty Γ
  → Ty (Γ ▹ A)
wkᵀ B = B [ wk ]ᵀ

_↑_
  : ∀ {Γ Δ}
  → (σ : Sub Δ Γ)
  → (A : Ty Γ)
  → Sub (Δ ▹ A [ σ ]ᵀ) (Γ ▹ A)
σ ↑ A = (σ ∘ wk , vz)

postulate
  ,∘
    : ∀ {Γ Δ Θ}
    → {A : Ty Γ}
    → (σ : Sub Δ Γ)
    → (a : Tm Δ (A [ σ ]ᵀ))
    → (δ : Sub Θ Δ)
    → _∘_ {Γ ▹ A} {Δ} {Θ} (_,_ {Γ} {Δ} σ a) δ
    ≡ ((_∘_ {Γ} {Δ} {Θ} σ δ) , a [ δ ]ᵗ)

{-# REWRITE ,∘ #-}

{-
postulate
  ,∘
    : ∀ {Γ Δ Θ}
    → {A : Ty Γ}
    → (σ : Sub Δ Γ)
    → (a : Tm Δ (A [ σ ]ᵀ))
    → (δ : Sub Θ Δ)
    → (σ , a) ∘ δ
    ≡ (σ ∘ δ , a [ δ ]ᵗ)

# REWRITE ,∘ #-}

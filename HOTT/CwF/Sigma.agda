module HOTT.CwF.Sigma where

open import HOTT.Prelude hiding (_,_; Σ)
open import HOTT.CwF.Base
open import HOTT.CwF.Con
open import HOTT.CwF.Sub

postulate
  Σ : ∀ {Γ}
    → (A : Ty Γ)
    → (B : Ty (Γ ▹ A))
    → Ty Γ

  Σ[] : ∀ {Γ Δ} (σ : Sub Δ Γ)
    → (A : Ty Γ)
    → (B : Ty (Γ ▹ A))
    → (Σ A B) [ σ ]ᵀ
    ≡ (Σ (A [ σ ]ᵀ) (B [ σ ↑ A ]ᵀ))
{-# REWRITE Σ[] #-}

postulate
  Σi : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty (Γ ▹ A)}
    → (a : Tm Γ A)
    → (b : Tm Γ (B [ id , a ]ᵀ))
    → Tm Γ (Σ A B)

postulate
  []∘ : ∀ {Γ Δ}
    → (σ : Sub Δ Γ)
    → {A : Ty Γ}
    → (B : Ty (Γ ▹ A))
    → (a : Tm Γ A)
    → B [ (id , a) ∘ σ ]ᵀ
    ≡ B [ (σ ↑ A) ∘ (id , a [ σ ]ᵗ) ]ᵀ

postulate
  Σi[] : ∀ {Γ Δ}
    → (σ : Sub Δ Γ)
    → {A : Ty Γ}
    → {B : Ty (Γ ▹ A)}
    → (a : Tm Γ A)
    → (b : Tm Γ (B [ id , a ]ᵀ))
    → Σi a b [ σ ]ᵗ
    ≡ Σi (a [ σ ]ᵗ) (subst (Tm Δ) ([]∘ σ B a) (b [ σ ]ᵗ))

{-# REWRITE Σi[] #-}

postulate
  Σe₁
    : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty (Γ ▹ A)}
    → (p : Tm Γ (Σ A B))
    → Tm Γ A

  Σe₂
    : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty (Γ ▹ A)}
    → (p : Tm Γ (Σ A B))
    → Tm Γ (B [ id , Σe₁ p ]ᵀ)

  Σβ₁
    : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty (Γ ▹ A)}
    → (a : Tm Γ A)
    → (b : Tm Γ (B [ id , a ]ᵀ))
    → Σe₁ (Σi a b) ≡ a

{-# REWRITE Σβ₁ #-}

postulate
  Σβ₂
    : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty (Γ ▹ A)}
    → (a : Tm Γ A)
    → (b : Tm Γ (B [ id , a ]ᵀ))
    → Σe₂ (Σi a b) ≡ b

{-# REWRITE Σβ₂ #-}

postulate
  Σe₁[]
    : ∀ {Γ Δ}
    → (σ : Sub Δ Γ)
    → {A : Ty Γ}
    → {B : Ty (Γ ▹ A)}
    → (p : Tm Γ (Σ A B))
    → (Σe₁ p) [ σ ]ᵗ ≡ Σe₁ (p [ σ ]ᵗ)

{-# REWRITE Σe₁[] #-}

postulate
  Σe₂[]
    : ∀ {Γ Δ}
    → (σ : Sub Δ Γ)
    → {A : Ty Γ}
    → {B : Ty (Γ ▹ A)}
    → (p : Tm Γ (Σ A B))
    → (Σe₂ {Γ} {A} {B} p) [ σ ]ᵗ
    ≡ subst (Tm Δ) (sym ([]∘ σ B (Σe₁ p)))
        (Σe₂ {Δ} {A [ σ ]ᵀ} {B [ σ ↑ A ]ᵀ} (p [ σ ]ᵗ))

{-# REWRITE Σe₂[] #-}

postulate
  Ση
    : ∀ {Γ}
    → {A : Ty Γ}
    → {B : Ty (Γ ▹ A)}
    → (p : Tm Γ (Σ A B))
    → Σi (Σe₁ p) (Σe₂ p) ≡ p

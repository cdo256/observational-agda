module HOTT.CwF.Unit where

open import HOTT.Prelude hiding (_,_)
open import HOTT.CwF.Base
open import HOTT.CwF.Con
open import HOTT.CwF.Sub

postulate
  ⊤ : ∀ {Γ} → Ty Γ

  ⊤[] : ∀ {Γ Δ} (σ : Sub Δ Γ)
       → ⊤ [ σ ]ᵀ ≡ ⊤

{-# REWRITE ⊤[] #-}

postulate
  ⊤i : ∀ {Γ} → Tm Γ ⊤

  ⊤i[] : ∀ {Γ Δ} (σ : Sub Δ Γ)
        → ⊤i [ σ ]ᵗ ≡ ⊤i

{-# REWRITE ⊤i[] #-}

postulate
  ⊤e
    : ∀ {Γ}
    → (A : Ty (Γ ▹ ⊤))
    → Tm Γ (A [ id , ⊤i ]ᵀ)
    → (t : Tm Γ ⊤)
    → Tm Γ (A [ id , t ]ᵀ)

  ⊤β
    : ∀ {Γ}
    → (A : Ty (Γ ▹ ⊤))
    → (a : Tm Γ (A [ id , ⊤i ]ᵀ))
    → ⊤e A a ⊤i ≡ a

{-# REWRITE ⊤β #-}

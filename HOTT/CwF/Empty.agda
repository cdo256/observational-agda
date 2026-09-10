module HOTT.CwF.Empty where

open import HOTT.Prelude hiding (_,_)
open import HOTT.CwF.Base
open import HOTT.CwF.Con
open import HOTT.CwF.Sub

postulate
  ⊥ : ∀ {Γ} → Ty Γ

  ⊥[] : ∀ {Γ Δ} (σ : Sub Δ Γ)
       → ⊥ [ σ ]ᵀ ≡ ⊥ 

{-# REWRITE ⊥[] #-}

postulate
  ⊥e : ∀ {Γ A} → Tm (Γ ▹ ⊥) A

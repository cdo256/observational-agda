module HOTT.CwF.Sorts where

open import HOTT.Prelude hiding (_,_)
open import HOTT.CwF.Cube

postulate
  Con : Dim → Type 
  Sub : ∀ {n} → Con n → Con n → Type 
  Ty : ∀ {n} → Con n → Type 
  Tm : ∀ {n} → (Γ : Con n) → Ty Γ → Type 

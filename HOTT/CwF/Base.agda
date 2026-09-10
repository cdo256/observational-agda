module HOTT.CwF.Base where

open import HOTT.Prelude

postulate
  Con : Type 
  Sub : Con → Con → Type 
  Ty  : Con → Type 
  Tm  : (Γ : Con) → Ty Γ → Type 

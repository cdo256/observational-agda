module HOTT.CwF.Con where

open import HOTT.Prelude hiding (_,_)
open import HOTT.CwF.Base

postulate
  ∙ : Con

  ε : ∀ {Γ}
    → Sub Γ ∙

  εη : ∀ {Γ}
      (σ : Sub Γ ∙)
    → σ ≡ ε

postulate
  _▹_ : (Γ : Con)
      → Ty Γ
      → Con

infixl 30 _▹_

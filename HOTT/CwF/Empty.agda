module HOTT.CwF.Empty where

open import HOTT.Prelude hiding (_,_; ⊥)
open import HOTT.CwF.Cube
open import HOTT.CwF.Sorts
open import HOTT.CwF.Sub
open import HOTT.CwF.Proj
open import HOTT.CwF.Universe

postulate
  ⊥ : ∀ {n}
    → {Γ : Con n}
    → Tm Γ U

  ⊥[] : ∀ {n}
    → {Γ Δ : Con n}
    →(σ : Sub Δ Γ)
    → ⊥ [ σ ]ᵗ ≡ ⊥ 

{-# REWRITE ⊥[] #-}

postulate
  ⊥⟨⟩ : ∀ {m n}
    → {Γ : Con n}
    → (i* : CubeMap m n)
    → ⊥ {n} {Γ} ⟨ i* ⟩ᵗ
    ≡ ⊥ {m} {Γ ⟨ i* ⟩ᶜ}

{-# REWRITE ⊥⟨⟩ #-}

postulate
  ⊥e : ∀ {n}
    → {Γ : Con n}
    → (A : Ty (Γ ▹ El ⊥))
    → Tm (Γ ▹ El ⊥) A

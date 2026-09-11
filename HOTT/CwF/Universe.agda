module HOTT.CwF.Universe where

open import HOTT.Prelude hiding (_,_; ⊥)
open import HOTT.CwF.Cube
open import HOTT.CwF.Sorts
open import HOTT.CwF.Sub
open import HOTT.CwF.Proj

postulate
  U : ∀ {n}
    → {Γ : Con n}
    → Ty Γ

  U[] : ∀ {n}
    → {Γ Δ : Con n}
    →(σ : Sub Δ Γ)
    → U [ σ ]ᵀ ≡ U 

{-# REWRITE U[] #-}

postulate
  U⟨⟩ : ∀ {m n}
    → {Γ : Con n}
    → (i* : CubeMap m n)
    → U {n} {Γ} ⟨ i* ⟩ᵀ
    ≡ U {m} {Γ ⟨ i* ⟩ᶜ}

{-# REWRITE U⟨⟩ #-}

postulate
  El : ∀ {n}
    → {Γ : Con n}
    → Tm Γ U
    → Ty Γ

  El[] : ∀ {n}
    → {Γ Δ : Con n}
    → (σ : Sub Δ Γ)
    → (A : Tm Γ U)
    → El A [ σ ]ᵀ ≡ El (A [ σ ]ᵗ) 

{-# REWRITE El[] #-}

postulate
  El⟨⟩ : ∀ {m n}
    → {Γ : Con n}
    → (i* : CubeMap m n)
    → (A : Tm Γ U)
    → El A ⟨ i* ⟩ᵀ
    ≡ El (A ⟨ i* ⟩ᵗ)

{-# REWRITE El⟨⟩ #-}

module HOTT.Unit where

open import HOTT.Universe
open import HOTT.PrimitiveIdentity
open import HOTT.ObservationalIdentity

data ⊤ : Type where
  tt : ⊤

postulate
  Id⊤ : ∀ x₀ x₁
    → Id ⊤ x₀ x₁
    ≡₀ ⊤

{-# REWRITE Id⊤ #-}

postulate
  refl⊤
    : refl ⊤ tt
    ≡₀ tt

isFib⊤ : isFibrant ⊤
isFib⊤ .trr tt = tt
isFib⊤ .liftr tt = tt
isFib⊤ .trl tt = tt
isFib⊤ .liftl tt = tt
isFib⊤ .id tt tt = isFib⊤

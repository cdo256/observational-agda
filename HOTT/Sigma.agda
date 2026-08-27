{-# OPTIONS --confluence-check #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --type-in-type #-}
module HOTT.Sigma where

open import HOTT.Identity.Primitive.Base
open import HOTT.Identity.Observational.Base
open import HOTT.Universe

record Σ (A : U) (B : El A → U)
  : Type where
  constructor _,_
  field
    fst : El A
    snd : El (B fst)
open Σ public

postulate
  Σᵘ : (A : U) (B : El A → U) → U
  ElΣβ : (A : U) (B : El A → U) → El (Σᵘ A B) ≡₀ Σ A B

{-# REWRITE ElΣβ #-}

postulate
  IdΣ
    : {A : U} {B : El A → U}
    → (x₀ x₁ : El (Σᵘ A B))
    → Id (Σᵘ A B) x₀ x₁
    ≡₀ Σᵘ (Id A (x₀ .fst) (x₁ .fst)) (λ a₂ → ap B a₂ (x₀ .snd) (x₁ .snd))
      
{-# REWRITE Id× #-}

{-
postulate
  refl×
    : {A : U} {B : U}
    → (x : El (A ×ᵘ B))
    → (refl (A ×ᵘ B) x)
    ≡₀ (refl A (x .fst) , refl B (x .snd))
    
{-# REWRITE refl× #-}

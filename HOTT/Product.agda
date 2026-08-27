{-# OPTIONS --confluence-check #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --type-in-type #-}
module HOTT.Product where

open import HOTT.Identity.Primitive.Base
open import HOTT.Identity.Observational.FlatPostulated
open import HOTT.Universe

record _×_ (A : U) (B : U)
  : Type where
  constructor _,_
  field
    fst : El A
    snd : El B
open _×_ public

postulate
  _×ᵘ_ : (A B : U) → U
  El×β : (A B : U) → El (A ×ᵘ B) ≡₀ A × B

{-# REWRITE El×β #-}

postulate
  Id×
    : {A : U} {B : U}
    → (x₀ x₁ : El (A ×ᵘ B))
    → Id (A ×ᵘ B) x₀ x₁
    ≡₀ Id A (x₀ .fst) (x₁ .fst) ×ᵘ Id B (x₀ .snd) (x₁ .snd)
      
{-# REWRITE Id× #-}

postulate
  refl×
    : {A : U} {B : U}
    → (x : El (A ×ᵘ B))
    → (refl (A ×ᵘ B) x)
    ≡₀ (refl A (x .fst) , refl B (x .snd))
    
{-# REWRITE refl× #-}

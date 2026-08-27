{-# OPTIONS --confluence-check #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --type-in-type #-}
module HOTT.Function where

open import HOTT.Identity.Primitive.Base
open import HOTT.Identity.Observational.Base
open import HOTT.Universe

postulate
  _⇨ᵘ_ : (A : U) (B : U) → U
  El⇨β : (A : U) (B : U) → El (A ⇨ᵘ B) ≡₀ (El A → El B)

{-# REWRITE El⇨β #-}

postulate
  Id⇨
    : {A : U} {B : U}
    → (f₀ f₁ : El (A ⇨ᵘ B))
    → Id (A ⇨ᵘ B) f₀ f₁
    ≡₀ ({!!} ⇨ᵘ {!!})


{-
(Id A (x₀ .fst) (x₁ .fst)) ⇨ᵘ ((λ a₂ → ap B a₂ (x₀ .snd) (x₁ .snd)) ⇨ᵘ ?)
      
{-# REWRITE Id× #-}

postulate
  refl×
    : {A : U} {B : U}
    → (x : El (A ×ᵘ B))
    → (refl (A ×ᵘ B) x)
    ≡₀ (refl A (x .fst) , refl B (x .snd))
    
# REWRITE refl× #-}

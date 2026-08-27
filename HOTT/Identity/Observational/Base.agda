{-# OPTIONS --confluence-check #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --type-in-type #-}
module HOTT.Identity.Observational.Base where

open import HOTT.Identity.Primitive.Base
open import HOTT.Universe

postulate
  U : Type
  El : U → Type

⟨_⟩ = El

postulate
  Id : (A : U) → (a₀ a₁ : El A) → U
  refl : (A : U) → (a : El A) → El (Id A a a)

_≡_ : {A : U}
  → (a₀ : El A) (a₁ : El A)
  → U
a₀ ≡ a₁ = Id _ a₀ a₁

postulate
  Uᵘ : U
  ElUβ : El Uᵘ ≡₀ U

{-# REWRITE ElUβ #-}

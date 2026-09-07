{-# OPTIONS --allow-unsolved-metas #-}
module HOTT.Iso where

open import HOTT.Universe
open import HOTT.PrimitiveIdentity
open import HOTT.ObservationalIdentity
open import HOTT.Empty
open import HOTT.Unit

-- Half-adjoint equiv
record Iso {ℓA ℓB} (A : Type ℓA) (B : Type ℓB) : Type (ℓA ⊔ ℓB) where
  field
    ltr : A → B
    rtl : B → A
    linv : (a : A) → rtl (ltr a) ≡ a
    rinv : (b : B) → ltr (rtl b) ≡ b
    triangle : (a : A)
      → ap ltr (linv a)
      ≡ rinv (ltr a)

_≅_ : ∀ {ℓA ℓB} (A : Type ℓA) (B : Type ℓB) → Type (ℓA ⊔ ℓB)
_≅_ = Iso

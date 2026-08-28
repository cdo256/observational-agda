{-# OPTIONS --allow-unsolved-metas #-}
module HOTT.Prelude.Iso where

open import HOTT.Prelude.Universe
open import HOTT.Prelude.PrimitiveIdentity
open import HOTT.Prelude.ObservationalIdentity
open import HOTT.Prelude.Empty
open import HOTT.Prelude.Unit

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

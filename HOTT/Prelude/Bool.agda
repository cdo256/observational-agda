module HOTT.Prelude.Bool where

open import HOTT.Prelude.Universe
open import HOTT.Prelude.PrimitiveIdentity
open import HOTT.Prelude.ObservationalIdentity

data Bool : Type where
  false : Bool
  true : Bool

postulate
  IdBool : ∀ x₀ x₁
    → Id Bool x₀ x₁
    ≡₀ Bool

{-# REWRITE IdBool #-}

postulate
  reflFalse
    : refl Bool false
    ≡₀ false
  reflTrue
    : refl Bool true
    ≡₀ true

{-# REWRITE reflTrue #-}

false≢true : {!false ≢ true!}

isFibBool : isFibrant Bool
isFibBool .trr x = x
isFibBool .liftr x = x
isFibBool .trl x = x
isFibBool .liftl x = x
isFibBool .id false false = isFibBool
isFibBool .id false true = {!!}
isFibBool .id true a₂₁ = {!!}

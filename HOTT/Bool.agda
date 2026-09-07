{-# OPTIONS --allow-unsolved-metas #-}
module HOTT.Bool where

open import HOTT.Universe
open import HOTT.PrimitiveIdentity
open import HOTT.ObservationalIdentity
open import HOTT.Empty
open import HOTT.Unit
open import HOTT.Iso

data Bool : Type where
  false : Bool
  true : Bool

{-
postulate
  IdBool-ff 
    : Id Bool false false
    ≡₀ ⊤
  IdBool-ft
    : Id Bool false true
    ≡₀ ⊥
  IdBool : ∀ x₀ x₁
    → Id Bool x₀ x₁
    ≡₀ ⊤
{-# REWRITE IdBool #-}

postulate
  reflBool : (x : Bool)
    → refl Bool x
    ≡₀ tt

{-# REWRITE reflBool #-}
-}

BoolCode : Bool → Bool → Type
BoolCode false false = ⊤
BoolCode false true = ⊥
BoolCode true false = ⊥
BoolCode true true = ⊤

postulate
  IdBool : (x₀ x₁ : Bool)
    → Id Bool x₀ x₁
    ≡₀ BoolCode x₀ x₁

{-# REWRITE IdBool #-}

IdBoolHom : (x : Bool)
  → BoolCode x x
  ≡₀ ⊤
IdBoolHom false = refl₀
IdBoolHom true = refl₀

{-# REWRITE IdBoolHom #-}

isPropIdBool : (a₀ a₁ : Bool)
  → (a₂₀ a₂₁ : Id Bool a₀ a₁)
  → a₂₀ ≡ a₂₁
isPropIdBool false false tt tt = tt
isPropIdBool true true tt tt = tt

-- postulate
--   reflBool : (x : Bool)
--     → refl Bool x
--     ≡₀ tt
-- 
-- {-# REWRITE reflBool #-}

false≢true : false ≢ true
false≢true ()

isBisimBool : isBisim (refl₂ (Id Bool) {true} {true} {true} {true} (refl Bool true) (refl Bool true))
isBisimBool .trr x = x
isBisimBool .liftr x = {!!}
  where
  v : refl Type (Id Bool true true) (refl Bool true) (refl Bool true)
  v = tt
  u : refl₂ (Id Bool) {true} {true} {true} {true} (refl Bool true) (refl Bool true) (refl Bool true) (refl Bool true) 
  u = subst₀ (λ A → A) (sym₀ (refl₂Refl Bool (refl Bool true) (refl Bool true))) v
isBisimBool .trl x = x
isBisimBool .liftl = {!!}
isBisimBool .id = {!!}

isFibBool : isFibrant Bool
isFibBool .trr x = x
isFibBool .liftr x = refl Bool x
isFibBool .trl x = x
isFibBool .liftl x = refl Bool x
isFibBool .id a₂₀ a₂₁ = {!!}
{-
isFibBool .id {false} {false} {false} {false} tt tt .trr x = x
isFibBool .id {false} {false} {false} {false} tt tt .liftr tt = {!!}
isFibBool .id {false} {false} {false} {false} tt tt .trl x = x
isFibBool .id {false} {false} {false} {false} tt tt .liftl tt = {!!}
isFibBool .id {false} {false} {false} {false} tt tt .id = {!!}
isFibBool .id {false} {true} {false} {true} tt tt .trr x = x
isFibBool .id {false} {true} {false} {true} tt tt .liftr ()
isFibBool .id {false} {true} {false} {true} tt tt .trl x = x
isFibBool .id {false} {true} {false} {true} tt tt .liftl ()
isFibBool .id {false} {true} {false} {true} tt tt .id {}
isFibBool .id {true} {a₀₁} {a₁₀} {a₁₁} a₂₀ a₂₁ = {!!}

-}

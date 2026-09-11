module HOTT.Prelude.Decidability where

open import HOTT.Prelude.Universe
open import HOTT.Prelude.Types
open import HOTT.Prelude.Truncation
open import HOTT.Prelude.Identity
open import HOTT.Prelude.Logic hiding (⊥; ⊤)

data Dec (A : Type ℓA) : Type ℓA where
  yes : A → Dec A
  no : (A → ⊥) → Dec A

data Decᵖ (A : Prop ℓA) : Type ℓA where
  yes : A → Decᵖ A
  no : (A → ⊥) → Decᵖ A

data True : Bool → Prop where
  true : True true

True? : ∀ b → Decᵖ (True b)
True? false = no (λ ())
True? true = yes true

case_returning_of_
  : {A : Type ℓA} (x : A) (B : A → Type ℓB)
  → ((x : A) → B x) → B x
case x returning B of f = f x
{-# INLINE case_returning_of_ #-}

case_of_ : {A : Type ℓA} {B : Type ℓB} → A → (A → B) → B
case a of f = f a
{-# INLINE case_of_ #-}

Discrete : (A : Type ℓA) → Type ℓA
Discrete A = ∀ (x y : A) → Dec (x ≡ y)

-- Conditional expression based on decidability.
infixr 3 if_then_else_
if_then_else_
  : {A : Type ℓA} {B : Type ℓB}
  → (decA : Dec A) → B → B → B
if yes _ then b else b' = b
if no _ then b else b' = b'

-- Conditional expression based on decidability.
infixr 3 ifᵖ_then_else_
ifᵖ_then_else_
  : {A : Prop ℓA} {B : Type ℓB}
  → (decA : Decᵖ A) → B → B → B
ifᵖ yes _ then b else b' = b
ifᵖ no _ then b else b' = b'

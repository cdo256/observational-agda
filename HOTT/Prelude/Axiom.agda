module HOTT.Prelude.Axiom where

open import HOTT.Prelude.Universe
open import HOTT.Prelude.Logic
open import HOTT.Prelude.Identity
open import HOTT.Prelude.HLevel

record PropExt : Typeω where
  field
    propExt : ∀ {ℓA}
            → {A B : Prop ℓA}
            → A ⇔ B → A ≡ B

record A!C : Typeω where
  field
    a!c : ∀ {ℓA} (A : Type ℓA) → isContr A → A

record FunExt : Typeω where
  field
    funExt : ∀ {ℓA ℓB} {A : Type ℓA} {B : A → Type ℓB}
           → {f g : ∀ a → B a} → (∀ x → f x ≡ g x)
           → f ≡ g

    funExtp : ∀ {ℓA ℓB} {A : Prop ℓA} {B : A → Type ℓB}
           → {f g : ∀ a → B a} → (∀ x → f x ≡ g x)
           → f ≡ g

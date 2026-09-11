postulate
  _[_]ᶜ : ∀ {m n}
    → Con n
    → Degen m n
    → Con m

  U  : ∀ {n}
    → {Γ : Con n}
    → Ty Γ
  El : ∀ {n}
    → {Γ : Con n}
    → Tm Γ U → Ty Γ

Idᶜ : ∀ {n}
  → (Γ : Con n)
  → Con (ds n)
Idᶜ {n} Γ = Γ [ ge ]ᶜ

postulate
  Id : ∀ {n}
    → (Γ : Con n)
    → (A : Ty Γ)
    → (a₀ a₁ : Tm Γ A)
    → Ty (Idᶜ Γ)

  -- Tarski universe codes for Id
  Idᵘ : ∀ {n} {Γ : Con n}
    → (A : Tm Γ U)
    → (a₀ a₁ : Tm Γ (El A))
    → Tm (Idᶜ Γ) U

postulate
  refl : ∀ {n} {Γ : Con n}
    → (A : Tm Γ U)
    → (a : Tm Γ (El A))
    → Tm (Idᶜ Γ) (El (Idᵘ A a a))


{-# OPTIONS --confluence-check #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --type-in-type #-}
module HOTT.Pi where

open import HOTT.Identity.Primitive.Base
open import HOTT.Identity.Observational.Base
open import HOTT.Universe

infixr 5 _⇨ᵘ_
infixl 20 _⋆ˢ_
infixl 20 _⋆_

postulate
  _⇨ᵘ_ : (A : U) (B : U) → U
  -- El⇨β : (A : U) (B : U) → El (A ⇨ᵘ B) ≡₀ (El A → El B)
  Πᵘ : (A : U) (B : El (A ⇨ᵘ Uᵘ)) → U
  Id₂ : U → U 
  id₂ : (A : U)
    → {a₀ a₁ : El A} → (a₂ : El (Id A a₀ a₁))
    → El (Id₂ A)
  id₂₀ : {A : U} → El (Id₂ A) → El A
  id₂₁ : {A : U} → El (Id₂ A) → El A
  id₂₂ : {A : U} → (id2 : El (Id₂ A))
    → El (Id A (id₂₀ id2) (id₂₁ id2))
  ƛˢ : (A : U) (B : U)
    → (f : El A → El B)
    → (f₂ : (a₂ : El (Id₂ A))
      → El (Id B (f (id₂₀ a₂)) (f (id₂₁ a₂))))
    → El (A ⇨ᵘ B)
  _⋆ˢ_ : {A : U} {B : U} (f : El (A ⇨ᵘ B)) → El A → El B 
  ƛ : (A : U) (B : El (A ⇨ᵘ Uᵘ))
    → (f : (a : El A) → El (B ⋆ˢ a))
    → El (Πᵘ A B)
  _⋆_ : {A : U} {B : El (A ⇨ᵘ Uᵘ)}
    → (f : El (Πᵘ A B))
    → (a : El A)
    → El (B ⋆ˢ a) 

--   ElΠβ : (A : U) (B : El A → U)
--     → El (Πᵘ A B) ≡₀ ((a : El A) → El (B a))
--   ElΠβ : (A : U) (B : El A → U)
--     → El (Πᵘ A B) ≡₀ ({a : El A} → El (B a))
-- 
-- {-# REWRITE El⇨β #-}
-- {-# REWRITE ElΠβ #-}

postulate
  Id⇨
    : {A : U} {B : U}
    → (f₀ f₁ : El (A ⇨ᵘ B))
    → Id (A ⇨ᵘ B) f₀ f₁
    ≡₀ Πᵘ (Id₂ A) (ƛˢ (Id₂ A) Uᵘ {!!} {!!})

{-
postulate
  Id⇨
    : {A : U} {B : U}
    → (f₀ f₁ : El (A ⇨ᵘ B))
    → Id (A ⇨ᵘ B) f₀ f₁
    ≡₀ Πᵘ A (ƛˢ A Uᵘ (λ a₀
    → Πᵘ A (ƛˢ A Uᵘ {!λ a₁
    → Πᵘ (Id A a₀ a₁) {!ƛˢ _ Uᵘ (λ a₂
    → Id B (f₀ ⋆ˢ a₀) (f₁ ⋆ˢ a₁))!} ?!} {!!}))
    {!!})

{-# REWRITE Id⇨ #-}

-- postulate
--   refl⇨
--     : {A : U} {B : U}
--     → (f : El (A ⇨ᵘ B))
--     → refl (A ⇨ᵘ B) f
--     ≡₀ ƛ A _ λ {a₀}
--     → {!!}

-- {-# REWRITE refl⇨ #-}

ap
  : {A B : U}
  → (f : El (A ⇨ᵘ B))
  → {x₀ x₁ : El A}
  → (x₂ : El (Id A x₀ x₁))
  → El (Id B (f ⋆ˢ x₀) (f ⋆ˢ x₁))

ap {A} {B} f {x₀} {x₁} x₂ =
  let u = refl (A ⇨ᵘ B) f
      v : El (ƛˢ A Uᵘ
            (λ a₀ →
               Πᵘ A
               (ƛˢ A Uᵘ
                (λ a₁ →
                   Πᵘ (Id A a₀ a₁)
                   (ƛˢ (Id A a₀ a₁) Uᵘ (λ a₂ → Id B (f ⋆ˢ a₀) (f ⋆ˢ a₁))))))
            ⋆ˢ x₀)
      v = u ⋆ x₀ ⋆ x₁
      w = u ⋆ x₀
  in {!((u ⋆ {x₀}) ⋆ {x₁}) ⋆ x₂!}

postulate
  ap
    : {A : U} {B : U}
    → (f : El (A ⇨ᵘ B))
    → (∀ {x₀ x₁ : El A}
      → (x₂ : El (Id A x₀ x₁))
      → El (Id B (f ⋆ˢ x₀) (f ⋆ˢ x₁)))


{-
apᵘ
  : (A : U) (B : U) → U
apᵘ A B =
    Πᵘ (A ⇨ᵘ B) λ f
  → Πᵘ A λ a₀
  → Πᵘ A λ a₁ 
  → Πᵘ (Id A a₀ a₁) λ a₂
  → Id B (f a₀) (f a₁)

-- λ a₂ 
--   → Id B (f a₀) (f a₁)
-}

postulate
  Id⇨
    : {A : U} {B : U}
    → (f₀ f₁ : El (A ⇨ᵘ B))
    → Id (A ⇨ᵘ B) f₀ f₁
    ≡₀ Πᵘ A (ƛˢ A Uᵘ λ a₀
    → Πᵘ A (ƛˢ A Uᵘ λ a₁
    → Πᵘ (Id A a₀ a₁) (ƛˢ _ Uᵘ λ a₂
    → Id B (f₀ ⋆ˢ a₀) (f₁ ⋆ˢ a₁))))

{-# REWRITE Id⇨ #-}

postulate
  refl⇨
    : {A : U} {B : U}
    → (f : El (A ⇨ᵘ B))
    → refl (A ⇨ᵘ B) f
    ≡₀ ƛ A _ λ {a₀}
    → {!!}

{-# REWRITE refl⇨ #-}


postulate
  IdΠ
    : {A : U} {B : El (A ⇨ᵘ Uᵘ)}
    → (f₀ f₁ : El (Πᵘ A B))
    → Id (Πᵘ A B) f₀ f₁
    ≡₀ Πᵘ A (ƛˢ A Uᵘ λ a₀
    → Πᵘ A (ƛˢ A Uᵘ λ a₁
    → Πᵘ (Id A a₀ a₁) (ƛˢ _ Uᵘ λ a₂
    → ap {!B!} {!!} (f₀ ⋆ a₀) {!f₁ ⋆ a₁!})))

postulate
  IdΠ
    : {A : U} {B : El (A ⇨ᵘ Uᵘ)}
    → (f₀ f₁ : El (Πᵘ A B))
    → Id (Πᵘ A B) f₀ f₁
    ≡₀ (Πᵘ A λ a₀
      → Πᵘ A λ a₁
      → Πᵘ (Id A a₀ a₁) λ a₂
      → refl {!B!} {!!} {!!} {!!})


(Id A (x₀ .fst) (x₁ .fst)) ⇨ᵘ ((λ a₂ → ap B a₂ (x₀ .snd) (x₁ .snd)) ⇨ᵘ ?)
      
{-# REWRITE Id× #-}

postulate
  refl×
    : {A : U} {B : U}
    → (x : El (A ×ᵘ B))
    → (refl (A ×ᵘ B) x)
    ≡₀ (refl A (x .fst) , refl B (x .snd))
    
{-# REWRITE refl× #-}

--
-}

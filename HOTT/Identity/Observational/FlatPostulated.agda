{-# OPTIONS --confluence-check #-}
{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --type-in-type #-}
module HOTT.Identity.Observational.FlatPostulated where

open import HOTT.Identity.Primitive.Base
open import HOTT.Universe

data ⊥ : Type where

data ⊤ : Type where
  tt : ⊤

data ℕ : Type where
  z : ℕ
  s : ℕ → ℕ

data 𝔹 : Type where
  false : 𝔹
  true : 𝔹

-- interleaved mutual
--   data U : Type
--   data El : U → Type

--   data _ where
--     ⊥ᵘ : U
--     ⊤ᵘ : U
--     tᵉ : El ⊤ᵘ
--     ℕᵘ : U
--     zᵉ : El ℕᵘ
--     sᵉ : El ℕᵘ → El ℕᵘ
--     Πᵘ : (A : U) → (El A → U) → U
--     Πᵉ : ∀ A B → El (Πᵘ A B)
--     Σᵘ : (A : U) → (El A → U) → U
--     Idᵘ : (A : U) → El A → El A → U

record Σ {ℓA ℓB} (A : Type ℓA) (B : A → Type ℓB)
  : Type (ℓA ⊔ ℓB) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

_×_ : ∀ {ℓA ℓB} (A : Type ℓA) (B : Type ℓB) → Type (ℓA ⊔ ℓB)
A × B = Σ A (λ _ → B)

postulate
  U : Type
  El : U → Type

⟨_⟩ = El

postulate
  Id : (A : U) → (a₀ a₁ : El A) → U
  refl : (A : U) → (a : El A) → El (Id A a a)

postulate
  ⊥ᵘ : U
  El⊥β : El ⊥ᵘ ≡₀ ⊥
  ⊤ᵘ : U
  El⊤β : El ⊤ᵘ ≡₀ ⊤
  𝔹ᵘ : U
  El𝔹β : El 𝔹ᵘ ≡₀ 𝔹
  ℕᵘ : U
  Elℕβ : El ℕᵘ ≡₀ ℕ
  Πᵘ : (A : U) → (El A → U) → U
  ElΠβ : ∀ A B → El (Πᵘ A B) ≡₀ (∀ (a : El A) → El (B a))
  Σᵘ : (A : U) → (El A → U) → U
  ElΣβ : ∀ A B → El (Σᵘ A B) ≡₀ Σ (El A) (λ a → El (B a))
  Uᵘ : U
  -- exploiting type-in-type for now.
  Uᴱ : El Uᵘ ≡₀ U 

{-
postulate
  IdU
    : (A₀ A₁ : El Uᵘ)
    → Id (Uᵘ , {!!}) A₀ A₁
    ≡₀ {!!}

{-# REWRITE IdU #-}

postulate
  reflType
    : refl Uᵘ
    ≡₀ Id

-}
    
{-# REWRITE reflType #-}

_≡_ : {A : U}
  → (a₀ : El A) (a₁ : El A)
  → {!!}
a₀ ≡ a₁ = Id _ a₀ a₁

{-
postulate
  ap
    : {A : U} {B : U}
    → (f : A → B)
    → (∀ {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
        → f x₀ ≡ f x₁)

postulate
  Id×
    : {A : U} {B : U}
    → (x₀ x₁ : El (Σᵘ A (λ _ → B)))
    → Id (Σᵘ A (λ _ → B)) x₀ x₁
    ≡₀ (x₀ .fst ≡ x₁ .fst) × ((x₀ .snd) ≡ (x₁ .snd))
      
{-# REWRITE IdΣ #-}

postulate
  reflΣ
    : {A : Type } {B : A → Type }
    → (x : Σ A B)
    → Id₀ (Id (Σ A B) x x)
          (refl (Σ A B) x)
          (refl A (x .fst) , refl (B (x .fst)) (x .snd))
    
{-# REWRITE reflΣ #-}

postulate
  IdΣ
    : {A : Type } {B : A → Type }
    → (x₀ x₁ : Σ A B)
    → Id (Σ A B) x₀ x₁
    ≡₀ Σ (x₀ .fst ≡ x₁ .fst)
         (λ a₂ → ap B a₂ (x₀ .snd) (x₁ .snd))
      
{-# REWRITE IdΣ #-}

postulate
  reflΣ
    : {A : Type } {B : A → Type }
    → (x : Σ A B)
    → Id₀ (Id (Σ A B) x x)
          (refl (Σ A B) x)
          (refl A (x .fst) , refl (B (x .fst)) (x .snd))
    
{-# REWRITE reflΣ #-}



-- Required for bootstrapping.
postulate
  ap
    : {A : Type} {B : Type}
    → (f : A → B)
    → (∀ {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
        → f x₀ ≡ f x₁)

postulate
  IdΠ
    : {A : Type } {B : A → Type }
    → (f₀ f₁ : (a : A) → B a)
    → Id ((a : A) → B a) f₀ f₁
    ≡₀ (∀ {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
        → ap B x₂ (f₀ x₀) (f₁ x₁))

{-# REWRITE IdΠ #-}

postulate
  apConst
    : {A : Type} {B : Type}
    → {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
    → ap (λ (_ : A) → B) x₂
    ≡₀ Id B

-- {-# REWRITE apConst #-}

postulate
  apβ
    : {A : Type } {B : Type }
    → (f : A → B)
    → {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
    → ap f x₂
    ≡₀ subst₀ (λ ○ → ○ (f x₀) (f x₁)) (apConst x₂)
         (refl (A → B) f x₂)

-- {-# REWRITE apβ #-}

postulate
  apConst'
    : {A : Type } {B : Type }
    → {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
    → refl (A → Type ) (λ (_ : A) → B) x₂
    ≡₀ let B₂ = Id B in {!B₂!}
    -- subst₀ (λ ○ → ○ (Type ) (Type )) {!apConst!} (Id B)

-- {-# REWRITE apConst' #-}


postulate
  apRefl 
    : {A : Type } {B : A → Type }
    → (x : A)
    -- → ap B (refl A x)
    → ap B (refl A x)
    ≡₀ Id (B x)

{-# REWRITE apRefl #-}

-- postulate
--   apId : ∀ { }
--     → {B : Type  → Type }
--     → (A : Type )
--     → ap B (Id A)
--     ≡₀ Id (B A)
-- 
-- {-# REWRITE apId #-}


--          apRefl                    reflType 
-- Id (B A) <----- ap B (refl Type A) ------> ap B (Id A).

--                apRefl                             reflΣ
-- Id (C (x , y)) <----- ap C (refl (Σ A B) (x , y)) ------> ap C (refl A x , refl (B x) y).

-- Id (C ((a : A) → B a))
--  ↑
--  | apId
--  |
-- ap C (Id ((a : A) → B a))
--  |
--  | IdΠ
--  ↓
-- ap C (λ a₀ a₁ →
--    {x₀ x₁ : A} (x₂ : x₀ ≡ x₁) → ap B x₂ (a₀ x₀) (a₁ x₁)).


-- ap (λ z → B z) (refl (Lift ' A) (lift x)) can be rewritten to
-- either Id (B (lift x)) or ap (λ z → B z) (lift (refl A x)).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → B z) (refl (Lift ' A) (lift x)) to resolve the
-- ambiguity.
-- when checking confluence of the rewrite rule apRefl with reflLift
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id ((a : A) → B a) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl ((a : A) → B a) a₀) (refl ((a : A) → B a) a₁)
-- can be rewritten to either
-- refl (Type ( ⊔ )) (Id ((a : A) → B a) a₀ a₁) a₀₂ a₁₂ or
-- ap
-- (λ z →
--    {x₀ x₁ : A} (x₂ : x₀ ≡ x₁) →
--    ap (λ v → B v) x₂ (z .fst x₀) (z .snd x₁))
-- (a₀₂ , a₁₂) (refl ((a : A) → B a) a₀) (refl ((a : A) → B a) a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id ((a : A) → B a) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl ((a : A) → B a) a₀) (refl ((a : A) → B a) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with IdΠ
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Lift ' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ' A) (lift x)) (refl (Lift ' A) a₁)
-- can be rewritten to either
-- refl (Type ( ⊔ ')) (Id (Lift ' A) (lift x) a₁) a₀₂ a₁₂ or
-- ap (λ z → Id (Lift ' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (lift (refl A x)) (refl (Lift ' A) a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Lift ' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ' A) (lift x)) (refl (Lift ' A) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with
-- reflLift
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Lift ' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ' A) a₀) (refl (Lift ' A) (lift x))
-- can be rewritten to either
-- refl (Type ( ⊔ ')) (Id (Lift ' A) a₀ (lift x)) a₀₂ a₁₂ or
-- ap (λ z → Id (Lift ' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ' A) a₀) (lift (refl A x)).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Lift ' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ' A) a₀) (refl (Lift ' A) (lift x))
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with
-- reflLift
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Lift ' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ' A) a₀) (refl (Lift ' A) a₁)
-- can be rewritten to either
-- refl (Type ( ⊔ ')) (Id (Lift ' A) a₀ a₁) a₀₂ a₁₂ or
-- ap (λ z → Lift ' (Id A (z .fst .lower) (z .snd .lower)))
-- (a₀₂ , a₁₂) (refl (Lift ' A) a₀) (refl (Lift ' A) a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Lift ' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ' A) a₀) (refl (Lift ' A) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with IdLift
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Type ) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ) a₀) (refl (Type ) a₁)
-- can be rewritten to either
-- refl (Type (lsuc )) (Id (Type ) a₀ a₁) a₀₂ a₁₂ or
-- ap (λ z → Id (Type ) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ) a₀) (Id a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Type ) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ) a₀) (refl (Type ) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with
-- reflType
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Type ) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ) a₀) (refl (Type ) a₁)
-- can be rewritten to either
-- refl (Type (lsuc )) (Id (Type ) a₀ a₁) a₀₂ a₁₂ or
-- ap (λ z → Id (Type ) (z .fst) (z .snd)) (a₀₂ , a₁₂) (Id a₀)
-- (refl (Type ) a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Type ) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ) a₀) (refl (Type ) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with
-- reflType
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Type ) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ) a₀) (refl (Type ) a₁)
-- can be rewritten to either
-- refl (Type (lsuc )) (Id (Type ) a₀ a₁) a₀₂ a₁₂ or
-- ap (λ z → z .fst → z .snd → Type ) (a₀₂ , a₁₂)
-- (refl (Type ) a₀) (refl (Type ) a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Type ) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ) a₀) (refl (Type ) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with IdType
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Σ A (λ z₁ → B z₁)) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Σ A (λ z → B z)) a₀) (refl (Σ A (λ z → B z)) a₁)
-- can be rewritten to either
-- refl (Type ( ⊔ )) (Id (Σ A (λ z → B z)) a₀ a₁) a₀₂ a₁₂ or
-- ap
-- (λ z →
--    Σ (z .fst .fst ≡ z .snd .fst)
--    (λ a₂ → ap (λ v → B v) a₂ (z .fst .snd) (z .snd .snd)))
-- (a₀₂ , a₁₂) (refl (Σ A (λ z → B z)) a₀)
-- (refl (Σ A (λ z → B z)) a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Σ A (λ z₁ → B z₁)) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Σ A (λ z → B z)) a₀) (refl (Σ A (λ z → B z)) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with IdΣ
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Σ A (λ z₁ → B z₁)) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Σ A (λ z → B z)) a₀) (refl (Σ A (λ z → B z)) a₁)
-- can be rewritten to either
-- refl (Type ( ⊔ )) (Id (Σ A (λ z → B z)) a₀ a₁) a₀₂ a₁₂ or
-- ap (λ z → Id (Σ A (λ z₁ → B z₁)) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Σ A (λ z → B z)) a₀)
-- (refl A (a₁ .fst) , refl (B (a₁ .fst)) (a₁ .snd)).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Σ A (λ z₁ → B z₁)) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Σ A (λ z → B z)) a₀) (refl (Σ A (λ z → B z)) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with reflΣ
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Σ A (λ z₁ → B z₁)) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Σ A (λ z → B z)) a₀) (refl (Σ A (λ z → B z)) a₁)
-- can be rewritten to either
-- refl (Type ( ⊔ )) (Id (Σ A (λ z → B z)) a₀ a₁) a₀₂ a₁₂ or
-- ap (λ z → Id (Σ A (λ z₁ → B z₁)) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl A (a₀ .fst) , refl (B (a₀ .fst)) (a₀ .snd))
-- (refl (Σ A (λ z → B z)) a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Σ A (λ z₁ → B z₁)) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Σ A (λ z → B z)) a₀) (refl (Σ A (λ z → B z)) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with reflΣ
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id A (z .fst) (z .snd)) (refl (Σ A (λ _ → A)) (a₀ , a₀))
-- (refl A a₀) (refl A a₀)
-- can be rewritten to either
-- refl (Type ) (Id A a₀ a₀) (refl (Σ A (λ _ → A)) (a₀ , a₀) .fst)
-- (refl (Σ A (λ _ → A)) (a₀ , a₀) .snd)
-- or Id (Id A a₀ a₀) (refl A a₀) (refl A a₀).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id A (z .fst) (z .snd)) (refl (Σ A (λ _ → A)) (a₀ , a₀))
-- (refl A a₀) (refl A a₀)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with apRefl
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteMaybeNonConfluent]
-- Couldn't determine overlap between left-hand sides
-- ap (λ z → Id _A_326 (z .fst) (z .snd)) (_a₀₂_329 , _a₁₂_330)
-- (refl _A_326 _a₀_327) (refl _A_326 _a₁_328)
-- and
-- ap (λ _ → _B_334) (_a₀₂_329 , _a₁₂_330) (refl _A_326 _a₀_327)
-- (refl _A_326 _a₁_328)
-- because of unsolved constraints:
--   Id _A_326 (x .fst) (x .snd) = _B_334 : Type __325
--     (blocked on any(_A_326, _B_334))
-- when checking confluence of the rewrite rule refl₂Refl with apConst

postulate
  reflΠ
    : {A : Type } {B : A → Type }
    → (f : (a : A) → B a)
    → (x : A)
    → refl ((a : A) → B a) f (refl A x)
    ≡₀ refl (B x) (f x)

-- {-# REWRITE reflΠ #-}

postulate
  apβ
    : {A : Type } {B : Type }
    → (f : A → B)
    → Id₀ (Id (A → B) f f)
          (ap f)
          (refl (A → B) f)

postulate
  IdLift : ∀ { '}
    → (A : Type )
    → (x₀ x₁ : A)
    → Id (Lift ' A) (lift x₀) (lift x₁)
    ≡₀ Lift ' (Id A x₀ x₁)
  
{-# REWRITE IdLift #-}

postulate
  reflLift : ∀ { '}
    → (A : Type )
    → (x : A)
    → refl (Lift ' A) (lift x)
    ≡₀ lift (refl A x)
  
{-# REWRITE reflLift #-}

Id₂ : ∀ {}
  → {A₀ A₁ : Type }
  → (A₂ : A₀ ≡ A₁)
  → {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
  → (a₂₀ : A₂ a₀₀ a₁₀) 
  → (a₂₁ : A₂ a₀₁ a₁₁) 
  → (a₀₂ : Id A₀ a₀₀ a₀₁)
  → (a₁₂ : Id A₁ a₁₀ a₁₁)
  → Type (lsuc )
Id₂ {} A₂ a₂₀ a₂₁ a₀₂ a₁₂ = Type 

refl₂ : ∀ {}
  → {A₀ A₁ : Type }
  → (A₂ : A₀ ≡ A₁)
  → {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
  → (a₂₀ : A₂ a₀₀ a₁₀) 
  → (a₂₁ : A₂ a₀₁ a₁₁) 
  → Id A₀ a₀₀ a₀₁ ≡ Id A₁ a₁₀ a₁₁
refl₂ {A₀ = A₀} {A₁} A₂ a₂₀ a₂₁ a₀₂ a₁₂ =
  ap (λ ((a₀ , a₁) : A₀ × A₁) → A₂ a₀ a₁)
     (a₀₂ , a₁₂) a₂₀ a₂₁

postulate
  refl₂Refl : ∀ {}
    → (A : Type )
    → {a₀ a₁ : A}
    → (a₀₂ : Id A a₀ a₁)
    → (a₁₂ : Id A a₀ a₁)
    -- → refl₂ (Id A) (refl A a₀) (refl A a₁) a₀₂ a₁₂
    → ap (λ ((a₀ , a₁) : A × A) → Id A a₀ a₁)
         (a₀₂ , a₁₂) (refl A a₀) (refl A a₁)
    ≡₀ refl (Type ) (Id A a₀ a₁) a₀₂ a₁₂

{-# REWRITE refl₂Refl #-}

record isBisim {} {A₀ A₁ : Type }
  (A₂ : A₀ → A₁ → Type )
  : Type  where
  coinductive
  field
    trr : A₀ → A₁
    liftr : (a₀ : A₀) → A₂ a₀ (trr a₀)
    trl : A₁ → A₀
    liftl : (a₁ : A₁) → A₂ (trl a₁) a₁
    id : {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
      → (a₂₀ : A₂ a₀₀ a₁₀) 
      → (a₂₁ : A₂ a₀₁ a₁₁) 
      → isBisim (refl₂ A₂ a₂₀ a₂₁)

isFibrant : ∀ {} → Type  → Type 
isFibrant {} A = isBisim (refl (Type ) A)

open isBisim public

[_] : ∀ { }
  → {A : Set } {B : A → Type }
  → (f : (a : A) → B a)
  → ∀ {a₀ a₁} → (a₂ : Id A a₀ a₁)
  → ap B a₂ (f a₀) (f a₁)
[_] {A = A} {B} f a₂ =
  refl ((a : A) → B a) f a₂

Σ₂ : ∀ { }
 → {A₀ A₁ : Type }
 → {B₀ : A₀ → Type }
 → {B₁ : A₁ → Type }
 → (A₂ : A₀ ≡ A₁)
 → (B₂ : ∀ {a₀ a₁} (a₂ : A₂ a₀ a₁) → B₀ a₀ ≡ B₁ a₁)
 → (Σ A₀ B₀) ≡ (Σ A₁ B₁)
(Σ₂ A₂ B₂) (a₀ , b₀) (a₁ , b₁) =
  Σ (A₂ a₀ a₁) λ a₂ → B₂ a₂ b₀ b₁

_×₂_ : ∀ { }
 → {A₀ A₁ : Type } {B₀ B₁ : Type }
 → (A₂ : A₀ ≡ A₁)
 → (B₂ : B₀ ≡ B₁)
 → (A₀ × B₀) ≡ (A₁ × B₁)
A₂ ×₂ B₂ = Σ₂ A₂ (λ _ → B₂)

postulate
  refl₂× :
    ∀ {A₀ A₁ : Type } {B₀ B₁ : Type }
    → (A₂ : A₀ ≡ A₁)
    → (B₂ : B₀ ≡ B₁)
    → {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
    → {b₀₀ b₀₁ : B₀} {b₁₀ b₁₁ : B₁}
    → (a₂₀ : A₂ a₀₀ a₁₀) (a₂₁ : A₂ a₀₁ a₁₁)
    → (b₂₀ : B₂ b₀₀ b₁₀) (b₂₁ : B₂ b₀₁ b₁₁)
    → refl₂ (A₂ ×₂ B₂) (a₂₀ , b₂₀) (a₂₁ , b₂₁)
    ≡₀ (refl₂ A₂ a₂₀ a₂₁ ×₂ refl₂ B₂ b₂₀ b₂₁)

  refl₂Σ :
    ∀ {A₀ A₁ : Type }
    → {B₀ : A₀ → Type }
    → {B₁ : A₁ → Type }
    → (A₂ : A₀ ≡ A₁)
    → (B₂ : ∀ {a₀ a₁} (a₂ : A₂ a₀ a₁) → B₀ a₀ ≡ B₁ a₁)
    → {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
    → (a₂₀ : A₂ a₀₀ a₁₀) (a₂₁ : A₂ a₀₁ a₁₁)
    → {b₀₀ : B₀ a₀₀} {b₁₀ : B₁ a₁₀}
    → {b₀₁ : B₀ a₀₁} {b₁₁ : B₁ a₁₁}
    → (b₂₀ : B₂ a₂₀ b₀₀ b₁₀) (b₂₁ : B₂ a₂₁ b₀₁ b₁₁)
    → refl₂ (Σ₂ A₂ B₂) (a₂₀ , b₂₀) (a₂₁ , b₂₁)
    ≡₀ (Σ₂ (refl₂ A₂ a₂₀ a₂₁) λ {a₀₂} {a₁₂} a₂₂ b₀₂ b₁₂ → {!!})

postulate
  refl₂Σ :
    ∀ {A₀ A₁ : Type }
    → {B₀ : A₀ → Type }
    → {B₁ : A₁ → Type }
    → (A₂ : A₀ ≡ A₁)
    → (B₂ : ∀ {a₀ a₁} (a₂ : A₂ a₀ a₁) → B₀ a₀ ≡ B₁ a₁)
    → {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
    → {b₀₀ b₀₁ : B₀} {b₁₀ b₁₁ : B₁}
    → (a₂₀ : A₂ a₀₀ a₁₀) (a₂₁ : A₂ a₀₁ a₁₁)
    → (b₂₀ : B₂ b₀₀ b₁₀) (b₂₁ : B₂ b₀₁ b₁₁)
    → refl₂ (Σ₂ A₂ B₂) (a₂₀ , b₂₀) (a₂₁ , b₂₁)
    ≡₀ {!refl₂ A₂ a₂₀ a₂₁ ×₂ refl₂ B₂ b₂₀ b₂₁!}

{-# TERMINATING #-} -- FIXME: subst₀ obscures the corecursion.
isBisim× : ∀ {} {}
  → {A₀ A₁ : Type } (A₂ : A₀ ≡ A₁)
  → {B₀ B₁ : Type } (B₂ : B₀ ≡ B₁)
  → isBisim A₂
  → isBisim B₂
  → isBisim (A₂ ×₂ B₂)
isBisim× A₂ B₂ isBisimA₂ isBisimB₂ .trr (a₀ , b₀) =
  isBisimA₂ .trr a₀ , isBisimB₂ .trr b₀
isBisim× A₂ B₂ isBisimA₂ isBisimB₂ .liftr (a₀ , b₀) =
  isBisimA₂ .liftr a₀ , isBisimB₂ .liftr b₀
isBisim× A₂ B₂ isBisimA₂ isBisimB₂ .trl (a₁ , b₁) =
  isBisimA₂ .trl a₁ , isBisimB₂ .trl b₁
isBisim× A₂ B₂ isBisimA₂ isBisimB₂ .liftl (a₁ , b₁) =
  isBisimA₂ .liftl a₁ , isBisimB₂ .liftl b₁
isBisim× A₂ B₂ isBisimA₂ isBisimB₂ .id (a₂₀ , b₂₀) (a₂₁ , b₂₁) =
  subst₀ isBisim (sym₀ (refl₂× A₂ B₂ a₂₀ a₂₁ b₂₀ b₂₁))
         (isBisim×
           (refl₂ A₂ a₂₀ a₂₁)
           (refl₂ B₂ b₂₀ b₂₁)
           (isBisimA₂ .id a₂₀ a₂₁)
           (isBisimB₂ .id b₂₀ b₂₁))

isFib× : ∀ {} {} {A : Type } {B : Type }
  → isFibrant A
  → isFibrant B
  → isFibrant (A × B)
isFib× {A = A} {B} isFibA isFibB =
  isBisim× (refl _ A) (refl _ B) isFibA isFibB

{-# TERMINATING #-} -- FIXME: subst₀ obscures the corecursion.
isBisimΣ : ∀ {} {}
  → {A₀ A₁ : Type } (A₂ : A₀ ≡ A₁)
  → {B₀ B₁ : Type } (B₂ : B₀ ≡ B₁)
  → isBisim A₂
  → isBisim B₂
  → isBisim (Σ₂ A₂ B₂)
isBisimΣ A₂ B₂ isBisimA₂ isBisimB₂ .trr (a₀ , b₀) =
  isBisimA₂ .trr a₀ , isBisimB₂ .trr b₀
isBisimΣ A₂ B₂ isBisimA₂ isBisimB₂ .liftr (a₀ , b₀) =
  isBisimA₂ .liftr a₀ , isBisimB₂ .liftr b₀
isBisimΣ A₂ B₂ isBisimA₂ isBisimB₂ .trl (a₁ , b₁) =
  isBisimA₂ .trl a₁ , isBisimB₂ .trl b₁
isBisimΣ A₂ B₂ isBisimA₂ isBisimB₂ .liftl (a₁ , b₁) =
  isBisimA₂ .liftl a₁ , isBisimB₂ .liftl b₁
isBisimΣ A₂ B₂ isBisimA₂ isBisimB₂ .id (a₂₀ , b₂₀) (a₂₁ , b₂₁) =
  subst₀ isBisim (sym₀ (refl₂× A₂ B₂ a₂₀ a₂₁ b₂₀ b₂₁))
         (isBisimΣ
           (refl₂ A₂ a₂₀ a₂₁)
           (refl₂ B₂ b₂₀ b₂₁)
           (isBisimA₂ .id a₂₀ a₂₁)
           (isBisimB₂ .id b₂₀ b₂₁))

isFibΣ : ∀ {} {} {A : Type } {B : Type }
  → isFibrant A
  → isFibrant B
  → isFibrant (A × B)
isFibΣ {A = A} {B} isFibA isFibB =
  isBisimΣ (refl _ A) (refl _ B) isFibA isFibB
-}

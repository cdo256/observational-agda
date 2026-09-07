{-# OPTIONS --confluence-check #-}
{-# OPTIONS --allow-unsolved-metas #-}
module HOTT.Identity.Observational.FlatPostulated where

open import HOTT.Identity.Primitive.Base
open import HOTT.Universe

postulate
  Id : ∀ {ℓA} → (A : Type ℓA)
    → (a₀ : A) (a₁ : A)
    → Type ℓA
  refl : ∀ {ℓA} → (A : Type ℓA)
    → (a : A)
    → Id A a a

postulate
  IdType : ∀ {ℓA}
    → (A₀ A₁ : Type ℓA)
    → Id (Type ℓA) A₀ A₁
    ≡₀ ((a₀ : A₀) → (a₁ : A₁) → Type ℓA)

{-# REWRITE IdType #-}

postulate
  reflType : ∀ {ℓA}
    → refl (Type ℓA)
    ≡₀ Id
    
{-# REWRITE reflType #-}

record Retract {ℓA ℓB} (A : Type ℓA) (B : Type ℓB) : Type (ℓA ⊔ ℓB) where
  field
    to : A → B
    fro : B → A
    inv : (b : B) → to (fro b) ≡₀ b

_≡_ : {A : Type ℓA}
  → (a₀ : A) (a₁ : A)
  → Type ℓA
a₀ ≡ a₁ = Id _ a₀ a₁

-- Required for bootstrapping.
postulate
  ap : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : Type ℓB}
    → (f : A → B)
    → (∀ {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
        → f x₀ ≡ f x₁)

postulate
  IdΠ : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : A → Type ℓB}
    → (f₀ f₁ : (a : A) → B a)
    → Id ((a : A) → B a) f₀ f₁
    ≡₀ (∀ {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
        → ap B x₂ (f₀ x₀) (f₁ x₁))

{-# REWRITE IdΠ #-}

postulate
  apConst : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : Type ℓB}
    → {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
    → ap (λ (_ : A) → B) x₂
    ≡₀ Id B

-- {-# REWRITE apConst #-}

postulate
  apβ : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : Type ℓB}
    → (f : A → B)
    → {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
    → ap f x₂
    ≡₀ subst₀ (λ ○ → ○ (f x₀) (f x₁)) (apConst x₂)
         (refl (A → B) f x₂)

-- {-# REWRITE apβ #-}

postulate
  apConst' : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : Type ℓB}
    → {x₀ x₁ : A} (x₂ : x₀ ≡ x₁)
    → refl (A → Type ℓB) (λ (_ : A) → B) x₂
    ≡₀ let B₂ = Id B in {!B₂!}
    -- subst₀ (λ ○ → ○ (Type ℓB) (Type ℓB)) {!apConst!} (Id B)

-- {-# REWRITE apConst' #-}


{-
postulate
  apRefl : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : A → Type ℓB}
    → (x : A)
    -- → ap B (refl A x)
    → ap B (refl A x)
    ≡₀ Id (B x)

{-# REWRITE apRefl #-}

-- postulate
--   apId : ∀ {ℓA ℓB}
--     → {B : Type ℓA → Type ℓB}
--     → (A : Type ℓA)
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


-- ap (λ z → B z) (refl (Lift ℓA' A) (lift x)) can be rewritten to
-- either Id (B (lift x)) or ap (λ z → B z) (lift (refl A x)).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → B z) (refl (Lift ℓA' A) (lift x)) to resolve the
-- ambiguity.
-- when checking confluence of the rewrite rule apRefl with reflLift
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id ((a : A) → B a) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl ((a : A) → B a) a₀) (refl ((a : A) → B a) a₁)
-- can be rewritten to either
-- refl (Type (ℓA ⊔ ℓB)) (Id ((a : A) → B a) a₀ a₁) a₀₂ a₁₂ or
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
-- ap (λ z → Id (Lift ℓA' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ℓA' A) (lift x)) (refl (Lift ℓA' A) a₁)
-- can be rewritten to either
-- refl (Type (ℓA ⊔ ℓA')) (Id (Lift ℓA' A) (lift x) a₁) a₀₂ a₁₂ or
-- ap (λ z → Id (Lift ℓA' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (lift (refl A x)) (refl (Lift ℓA' A) a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Lift ℓA' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ℓA' A) (lift x)) (refl (Lift ℓA' A) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with
-- reflLift
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Lift ℓA' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ℓA' A) a₀) (refl (Lift ℓA' A) (lift x))
-- can be rewritten to either
-- refl (Type (ℓA ⊔ ℓA')) (Id (Lift ℓA' A) a₀ (lift x)) a₀₂ a₁₂ or
-- ap (λ z → Id (Lift ℓA' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ℓA' A) a₀) (lift (refl A x)).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Lift ℓA' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ℓA' A) a₀) (refl (Lift ℓA' A) (lift x))
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with
-- reflLift
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Lift ℓA' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ℓA' A) a₀) (refl (Lift ℓA' A) a₁)
-- can be rewritten to either
-- refl (Type (ℓA ⊔ ℓA')) (Id (Lift ℓA' A) a₀ a₁) a₀₂ a₁₂ or
-- ap (λ z → Lift ℓA' (Id A (z .fst .lower) (z .snd .lower)))
-- (a₀₂ , a₁₂) (refl (Lift ℓA' A) a₀) (refl (Lift ℓA' A) a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Lift ℓA' A) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Lift ℓA' A) a₀) (refl (Lift ℓA' A) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with IdLift
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Type ℓA) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ℓA) a₀) (refl (Type ℓA) a₁)
-- can be rewritten to either
-- refl (Type (lsuc ℓA)) (Id (Type ℓA) a₀ a₁) a₀₂ a₁₂ or
-- ap (λ z → Id (Type ℓA) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ℓA) a₀) (Id a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Type ℓA) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ℓA) a₀) (refl (Type ℓA) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with
-- reflType
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Type ℓA) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ℓA) a₀) (refl (Type ℓA) a₁)
-- can be rewritten to either
-- refl (Type (lsuc ℓA)) (Id (Type ℓA) a₀ a₁) a₀₂ a₁₂ or
-- ap (λ z → Id (Type ℓA) (z .fst) (z .snd)) (a₀₂ , a₁₂) (Id a₀)
-- (refl (Type ℓA) a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Type ℓA) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ℓA) a₀) (refl (Type ℓA) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with
-- reflType
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Type ℓA) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ℓA) a₀) (refl (Type ℓA) a₁)
-- can be rewritten to either
-- refl (Type (lsuc ℓA)) (Id (Type ℓA) a₀ a₁) a₀₂ a₁₂ or
-- ap (λ z → z .fst → z .snd → Type ℓA) (a₀₂ , a₁₂)
-- (refl (Type ℓA) a₀) (refl (Type ℓA) a₁).
-- Possible fix: add a rewrite rule with left-hand side
-- ap (λ z → Id (Type ℓA) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Type ℓA) a₀) (refl (Type ℓA) a₁)
-- to resolve the ambiguity.
-- when checking confluence of the rewrite rule refl₂Refl with IdType
-- /home/cdo/src/observational-agda/HOTT/Prelude/ObservationalIdentity.agda:178.13-22: error: [RewriteAmbiguousRules]
-- Global confluence check failed:
-- ap (λ z → Id (Σ A (λ z₁ → B z₁)) (z .fst) (z .snd)) (a₀₂ , a₁₂)
-- (refl (Σ A (λ z → B z)) a₀) (refl (Σ A (λ z → B z)) a₁)
-- can be rewritten to either
-- refl (Type (ℓA ⊔ ℓB)) (Id (Σ A (λ z → B z)) a₀ a₁) a₀₂ a₁₂ or
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
-- refl (Type (ℓA ⊔ ℓB)) (Id (Σ A (λ z → B z)) a₀ a₁) a₀₂ a₁₂ or
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
-- refl (Type (ℓA ⊔ ℓB)) (Id (Σ A (λ z → B z)) a₀ a₁) a₀₂ a₁₂ or
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
-- refl (Type ℓA) (Id A a₀ a₀) (refl (Σ A (λ _ → A)) (a₀ , a₀) .fst)
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
--   Id _A_326 (x .fst) (x .snd) = _B_334 : Type _ℓA_325
--     (blocked on any(_A_326, _B_334))
-- when checking confluence of the rewrite rule refl₂Refl with apConst

postulate
  reflΠ : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : A → Type ℓB}
    → (f : (a : A) → B a)
    → (x : A)
    → refl ((a : A) → B a) f (refl A x)
    ≡₀ refl (B x) (f x)

-- {-# REWRITE reflΠ #-}

postulate
  apβ : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : Type ℓB}
    → (f : A → B)
    → Id₀ (Id (A → B) f f)
          (ap f)
          (refl (A → B) f)

record Σ {ℓA ℓB} (A : Type ℓA) (B : A → Type ℓB)
  : Type (ℓA ⊔ ℓB) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

_×_ : (A : Type ℓA) (B : Type ℓB) → Type (ℓA ⊔ ℓB)
A × B = Σ A (λ _ → B)

postulate
  IdΣ : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : A → Type ℓB}
    → (x₀ x₁ : Σ A B)
    → Id (Σ A B) x₀ x₁
    ≡₀ Σ (x₀ .fst ≡ x₁ .fst)
         (λ a₂ → ap B a₂ (x₀ .snd) (x₁ .snd))
      
{-# REWRITE IdΣ #-}

postulate
  reflΣ : ∀ {ℓA ℓB}
    → {A : Type ℓA} {B : A → Type ℓB}
    → (x : Σ A B)
    → Id₀ (Id (Σ A B) x x)
          (refl (Σ A B) x)
          (refl A (x .fst) , refl (B (x .fst)) (x .snd))
    
{-# REWRITE reflΣ #-}

postulate
  IdLift : ∀ {ℓA ℓA'}
    → (A : Type ℓA)
    → (x₀ x₁ : A)
    → Id (Lift ℓA' A) (lift x₀) (lift x₁)
    ≡₀ Lift ℓA' (Id A x₀ x₁)
  
{-# REWRITE IdLift #-}

postulate
  reflLift : ∀ {ℓA ℓA'}
    → (A : Type ℓA)
    → (x : A)
    → refl (Lift ℓA' A) (lift x)
    ≡₀ lift (refl A x)
  
{-# REWRITE reflLift #-}

Id₂ : ∀ {ℓA}
  → {A₀ A₁ : Type ℓA}
  → (A₂ : A₀ ≡ A₁)
  → {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
  → (a₂₀ : A₂ a₀₀ a₁₀) 
  → (a₂₁ : A₂ a₀₁ a₁₁) 
  → (a₀₂ : Id A₀ a₀₀ a₀₁)
  → (a₁₂ : Id A₁ a₁₀ a₁₁)
  → Type (lsuc ℓA)
Id₂ {ℓA} A₂ a₂₀ a₂₁ a₀₂ a₁₂ = Type ℓA

refl₂ : ∀ {ℓA}
  → {A₀ A₁ : Type ℓA}
  → (A₂ : A₀ ≡ A₁)
  → {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
  → (a₂₀ : A₂ a₀₀ a₁₀) 
  → (a₂₁ : A₂ a₀₁ a₁₁) 
  → Id A₀ a₀₀ a₀₁ ≡ Id A₁ a₁₀ a₁₁
refl₂ {A₀ = A₀} {A₁} A₂ a₂₀ a₂₁ a₀₂ a₁₂ =
  ap (λ ((a₀ , a₁) : A₀ × A₁) → A₂ a₀ a₁)
     (a₀₂ , a₁₂) a₂₀ a₂₁

postulate
  refl₂Refl : ∀ {ℓA}
    → (A : Type ℓA)
    → {a₀ a₁ : A}
    → (a₀₂ : Id A a₀ a₁)
    → (a₁₂ : Id A a₀ a₁)
    -- → refl₂ (Id A) (refl A a₀) (refl A a₁) a₀₂ a₁₂
    → ap (λ ((a₀ , a₁) : A × A) → Id A a₀ a₁)
         (a₀₂ , a₁₂) (refl A a₀) (refl A a₁)
    ≡₀ refl (Type ℓA) (Id A a₀ a₁) a₀₂ a₁₂

{-# REWRITE refl₂Refl #-}

record isBisim {ℓA} {A₀ A₁ : Type ℓA}
  (A₂ : A₀ → A₁ → Type ℓA)
  : Type ℓA where
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

isFibrant : ∀ {ℓA} → Type ℓA → Type ℓA
isFibrant {ℓA} A = isBisim (refl (Type ℓA) A)

open isBisim public

[_] : ∀ {ℓA ℓB}
  → {A : Set ℓA} {B : A → Type ℓB}
  → (f : (a : A) → B a)
  → ∀ {a₀ a₁} → (a₂ : Id A a₀ a₁)
  → ap B a₂ (f a₀) (f a₁)
[_] {A = A} {B} f a₂ =
  refl ((a : A) → B a) f a₂

Σ₂ : ∀ {ℓA ℓB}
 → {A₀ A₁ : Type ℓA}
 → {B₀ : A₀ → Type ℓB}
 → {B₁ : A₁ → Type ℓB}
 → (A₂ : A₀ ≡ A₁)
 → (B₂ : ∀ {a₀ a₁} (a₂ : A₂ a₀ a₁) → B₀ a₀ ≡ B₁ a₁)
 → (Σ A₀ B₀) ≡ (Σ A₁ B₁)
(Σ₂ A₂ B₂) (a₀ , b₀) (a₁ , b₁) =
  Σ (A₂ a₀ a₁) λ a₂ → B₂ a₂ b₀ b₁

_×₂_ : ∀ {ℓA ℓB}
 → {A₀ A₁ : Type ℓA} {B₀ B₁ : Type ℓB}
 → (A₂ : A₀ ≡ A₁)
 → (B₂ : B₀ ≡ B₁)
 → (A₀ × B₀) ≡ (A₁ × B₁)
A₂ ×₂ B₂ = Σ₂ A₂ (λ _ → B₂)

postulate
  refl₂× :
    ∀ {A₀ A₁ : Type ℓA} {B₀ B₁ : Type ℓB}
    → (A₂ : A₀ ≡ A₁)
    → (B₂ : B₀ ≡ B₁)
    → {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
    → {b₀₀ b₀₁ : B₀} {b₁₀ b₁₁ : B₁}
    → (a₂₀ : A₂ a₀₀ a₁₀) (a₂₁ : A₂ a₀₁ a₁₁)
    → (b₂₀ : B₂ b₀₀ b₁₀) (b₂₁ : B₂ b₀₁ b₁₁)
    → refl₂ (A₂ ×₂ B₂) (a₂₀ , b₂₀) (a₂₁ , b₂₁)
    ≡₀ (refl₂ A₂ a₂₀ a₂₁ ×₂ refl₂ B₂ b₂₀ b₂₁)

  refl₂Σ :
    ∀ {A₀ A₁ : Type ℓA}
    → {B₀ : A₀ → Type ℓB}
    → {B₁ : A₁ → Type ℓB}
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
    ∀ {A₀ A₁ : Type ℓA}
    → {B₀ : A₀ → Type ℓB}
    → {B₁ : A₁ → Type ℓB}
    → (A₂ : A₀ ≡ A₁)
    → (B₂ : ∀ {a₀ a₁} (a₂ : A₂ a₀ a₁) → B₀ a₀ ≡ B₁ a₁)
    → {a₀₀ a₀₁ : A₀} {a₁₀ a₁₁ : A₁}
    → {b₀₀ b₀₁ : B₀} {b₁₀ b₁₁ : B₁}
    → (a₂₀ : A₂ a₀₀ a₁₀) (a₂₁ : A₂ a₀₁ a₁₁)
    → (b₂₀ : B₂ b₀₀ b₁₀) (b₂₁ : B₂ b₀₁ b₁₁)
    → refl₂ (Σ₂ A₂ B₂) (a₂₀ , b₂₀) (a₂₁ , b₂₁)
    ≡₀ {!refl₂ A₂ a₂₀ a₂₁ ×₂ refl₂ B₂ b₂₀ b₂₁!}

{-# TERMINATING #-} -- FIXME: subst₀ obscures the corecursion.
isBisim× : ∀ {ℓA} {ℓB}
  → {A₀ A₁ : Type ℓA} (A₂ : A₀ ≡ A₁)
  → {B₀ B₁ : Type ℓB} (B₂ : B₀ ≡ B₁)
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

isFib× : ∀ {ℓA} {ℓB} {A : Type ℓA} {B : Type ℓB}
  → isFibrant A
  → isFibrant B
  → isFibrant (A × B)
isFib× {A = A} {B} isFibA isFibB =
  isBisim× (refl _ A) (refl _ B) isFibA isFibB

{-# TERMINATING #-} -- FIXME: subst₀ obscures the corecursion.
isBisimΣ : ∀ {ℓA} {ℓB}
  → {A₀ A₁ : Type ℓA} (A₂ : A₀ ≡ A₁)
  → {B₀ B₁ : Type ℓB} (B₂ : B₀ ≡ B₁)
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

isFibΣ : ∀ {ℓA} {ℓB} {A : Type ℓA} {B : Type ℓB}
  → isFibrant A
  → isFibrant B
  → isFibrant (A × B)
isFibΣ {A = A} {B} isFibA isFibB =
  isBisimΣ (refl _ A) (refl _ B) isFibA isFibB
-}

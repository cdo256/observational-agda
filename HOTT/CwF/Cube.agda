module HOTT.CwF.Cube where

open import HOTT.Prelude

{-
Dim ≈ ℕ - number of dimensions a cube has
Orient n ≈ Fin n - index into a cube 
Image n ≈ Source orientation + 0 + 1
RawCubeMap m n ≈ Vec n (Image m) raw cube map.
Injective! i* ≈ isInjective! (i* !ʳ_)
CubeMap m n ≈ (i* : RawCubeMap m n) × (Injective! i*)
Γ ⟨ d ⟩ᶜ - projection of Con
A ⟨ d ⟩ᵀ - projection of Ty
a ⟨ d ⟩ᵗ - projection of Tm
σ ⟨ d ⟩ˢ - projection of Sub
-}

data Dim : Type where
  dz : Dim
  ds : Dim → Dim

data Orient : Dim → Type where
  oz : ∀ {n} → Orient (ds n)
  os : ∀ {n}
    → Orient n
    → Orient (ds n)

-- Useful later for general cube maps.
-- Variable-only maps use only iv.
data Image (m : Dim) : Type where
  i0 : Image m
  i1 : Image m
  iv : Orient m → Image m

infixr 30 _∷_

data RawCubeMap (m : Dim) : Dim → Type where
  []  : RawCubeMap m dz
  _∷_ : ∀ {n}
    → Image m
    → RawCubeMap m n
    → RawCubeMap m (ds n)

infixl 20 _!ʳ_

_!ʳ_ : ∀ {m n}
  → RawCubeMap m n
  → Orient n
  → Image m
[] !ʳ ()
(i ∷ i*) !ʳ oz = i
(i ∷ i*) !ʳ os j = i* !ʳ j

Injective! : ∀ {m n}
  → RawCubeMap m n
  → Type
Injective! i* =
  ∀ {i j k}
  → i* !ʳ i ≡ iv k
  → i* !ʳ j ≡ iv k
  → i ≡ j

record CubeMap (m n : Dim) : Type where
  constructor cm
  field
    raw : RawCubeMap m n
    inj : Injective! raw

open CubeMap public

iwk : ∀ {m} → Image m → Image (ds m)
iwk i0 = i0
iwk i1 = i1
iwk (iv i) = iv (os i)

iwkʳ : ∀ {m n}
  → RawCubeMap m n
  → RawCubeMap (ds m) n
iwkʳ {m} {dz} [] = []
iwkʳ {m} {ds n} (i ∷ i*) = iwk i ∷ iwkʳ i*

wk!ʳ : ∀ {m n}
  → (i* : RawCubeMap m n)
  → (i : Orient n)
  → iwkʳ i* !ʳ i ≡ iwk (i* !ʳ i)
wk!ʳ [] ()
wk!ʳ (i ∷ i*) oz = refl
wk!ʳ (i ∷ i*) (os j) = wk!ʳ i* j

iwk-inj : ∀ {m}
  → (i j : Image m)
  → iwk i ≡ iwk j
  → i ≡ j
iwk-inj i0 i0 refl = refl
iwk-inj i0 i1 ()
iwk-inj i0 (iv j) ()
iwk-inj i1 i0 ()
iwk-inj i1 i1 refl = refl
iwk-inj i1 (iv j) ()
iwk-inj (iv i) i0 ()
iwk-inj (iv i) i1 ()
iwk-inj (iv i) (iv j) refl = refl

iwk≢oz : ∀ {m}
  → {i : Image m}
  → iwk i ≢ iv oz
iwk≢oz {i = i0} ()
iwk≢oz {i = i1} ()
iwk≢oz {i = iv j} ()

wk-inj : ∀ {m n}
  → (i* : RawCubeMap m n)
  → Injective! i*
  → Injective! (iwkʳ i*)
wk-inj (x ∷ i*) q {oz} {oz} p r = refl
wk-inj (x ∷ i*) q {oz} {os j} {oz} p r =
  absurd (iwk≢oz p)
wk-inj (x ∷ i*) q {os i} {oz} {oz} p r =
  absurd (iwk≢oz r)
wk-inj (x ∷ i*) q {oz} {os j} {os k} p r =
  q head tail
  where
  head : _ ≡ iv k
  head = iwk-inj x (iv k) p
  tail : _ ≡ iv k
  tail = iwk-inj (i* !ʳ j) (iv k) (trans (sym (wk!ʳ i* j)) r)
wk-inj (x ∷ i*) q {os i} {oz} {os k} p r =
  q tail head
  where
  tail : _ ≡ iv k
  tail = iwk-inj (i* !ʳ i) (iv k) (trans (sym (wk!ʳ i* i)) p)
  head : _ ≡ iv k
  head = iwk-inj x (iv k) (trans r refl)
wk-inj (x ∷ i*) q {os i} {os j} {oz} p r =
  absurd (iwk≢oz (trans (sym (wk!ʳ i* i)) p))
wk-inj (x ∷ i*) q {os i} {os j} {os k} p r =
  q (iwk-inj (i* !ʳ i) (iv k) (trans (sym (wk!ʳ i* i)) p))
    (iwk-inj (i* !ʳ j) (iv k) (trans (sym (wk!ʳ i* j)) r))

iv-inj : ∀ {m} {i j : Orient m} → iv i ≡ iv j → i ≡ j
iv-inj refl = refl

oz≠os : ∀ {m}
  → {i : Orient m}
  → oz ≢ os i
oz≠os ()

wk!ʳ≢oz : ∀ {m n}
  → {i* : RawCubeMap m n}
  → {i : Orient n}
  → iwkʳ i* !ʳ i ≢ iv oz
wk!ʳ≢oz {i* = i*} {i = i} p =
  iwk≢oz (trans (sym (wk!ʳ i* i)) p)

_!ⁱ_ : ∀ {l m}
  → RawCubeMap l m
  → Image m
  → Image l
i* !ⁱ i0 = i0
i* !ⁱ i1 = i1
i* !ⁱ iv j = i* !ʳ j

_∘ʳ_ : ∀ {l m n}
  → RawCubeMap l m
  → RawCubeMap m n
  → RawCubeMap l n
i* ∘ʳ [] = []
i* ∘ʳ (j ∷ j*) = (i* !ⁱ j) ∷ (i* ∘ʳ j*)

!∘ʳ : ∀ {l m n}
  → (i* : RawCubeMap l m)
  → (j* : RawCubeMap m n)
  → (j : Orient n)
  → (i* ∘ʳ j*) !ʳ j
    ≡ i* !ⁱ (j* !ʳ j)
!∘ʳ i* [] ()
!∘ʳ i* (j ∷ j*) oz = refl
!∘ʳ i* (j ∷ j*) (os k) = !∘ʳ i* j* k

record VarPreimage {l m : Dim}
  (i* : RawCubeMap l m) (j : Image m) (k : Orient l) : Type where
  constructor pre
  field
    source : Orient m
    at : j ≡ iv source
    mapped : i* !ʳ source ≡ iv k

preimage : ∀ {l m} (i* : RawCubeMap l m) {j : Image m} {k : Orient l}
  → i* !ⁱ j ≡ iv k
  → VarPreimage i* j k
preimage i* {j = i0} ()
preimage i* {j = i1} ()
preimage i* {j = iv j} p = pre j refl p

∘ʳ-inj : ∀ {l m n}
  → {i* : RawCubeMap l m}
  → {j* : RawCubeMap m n}
  → Injective! i*
  → Injective! j*
  → Injective! (i* ∘ʳ j*)
∘ʳ-inj {i* = i*} {j* = j*} i*-inj j*-inj {i} {j} {k} p q
  with preimage i* {j = j* !ʳ i} (trans (sym (!∘ʳ i* j* i)) p) | preimage i* {j = j* !ʳ j} (trans (sym (!∘ʳ i* j* j)) q)
... | pre i' i-at i-map | pre j' j-at j-map
  = j*-inj i-at (trans j-at (cong iv (sym (i*-inj i-map j-map))))

_∘ᵐ_ : ∀ {l m n}
  → CubeMap l m
  → CubeMap m n
  → CubeMap l n
cm i* i*-inj ∘ᵐ cm j* j*-inj =
  cm (i* ∘ʳ j*) (∘ʳ-inj i*-inj j*-inj)

i0≢iv : ∀ {m} {i : Orient m} → i0 ≢ iv i
i0≢iv ()

i1≢iv : ∀ {m} {i : Orient m} → i1 ≢ iv i
i1≢iv ()

oz∷-inj : ∀ {m n} {i* : RawCubeMap m n}
  → Injective! (iwkʳ i*)
  → Injective! (iv oz ∷ iwkʳ i*)
oz∷-inj q {oz} {oz} p r = refl
oz∷-inj q {oz} {os j} {oz} p r = absurd (wk!ʳ≢oz r)
oz∷-inj q {oz} {os j} {os k} p r
  with oz≠os (iv-inj p)
... | ()
oz∷-inj q {os i} {oz} {oz} p r = absurd (wk!ʳ≢oz p)
oz∷-inj q {os i} {oz} {os k} p r
  with oz≠os (iv-inj r)
... | ()
oz∷-inj q {os i} {os j} p r = cong os (q p r)

wkᵐ : ∀ {m n} → CubeMap m n → CubeMap (ds m) n
wkᵐ (cm i* i*-inj) = cm (iwkʳ i*) (wk-inj i* i*-inj)

idʳ : (n : Dim) → RawCubeMap n n
idʳ dz = []
idʳ (ds n) = iv oz ∷ iwkʳ (idʳ n)

[]ʳ-inj : ∀ {m} → Injective! {m} {dz} []
[]ʳ-inj {i = ()}

idʳ-inj : ∀ (n : Dim) → Injective! (idʳ n)
idʳ-inj dz = []ʳ-inj
idʳ-inj (ds n) = oz∷-inj (wk-inj (idʳ n) (idʳ-inj n))

geʳ : (n : Dim) → RawCubeMap (ds n) n
geʳ dz = []
geʳ (ds n) = iv oz ∷ iwkʳ (geʳ n)

geʳ-inj : (n : Dim) → Injective! (geʳ n)
geʳ-inj dz = []ʳ-inj
geʳ-inj (ds n) = oz∷-inj (wk-inj (geʳ n) (geʳ-inj n))

geᵐ : ∀ {n} → CubeMap (ds n) n
geᵐ {n} = cm (geʳ n) (geʳ-inj n)

idᵐ : (n : Dim) → CubeMap n n
idᵐ dz = cm [] []ʳ-inj
idᵐ (ds n) = cm (idʳ (ds n)) (idʳ-inj (ds n))

δ0ʳ : ∀ {m n} → RawCubeMap m n → RawCubeMap m (ds n)
δ0ʳ i* = i0 ∷ i*

δ1ʳ : ∀ {m n} → RawCubeMap m n → RawCubeMap m (ds n)
δ1ʳ i* = i1 ∷ i*

δ0ʳ-inj : ∀ {m n} {i* : RawCubeMap m n}
  → Injective! i*
  → Injective! (δ0ʳ i*)
δ0ʳ-inj q {oz} {oz} p r = refl
δ0ʳ-inj q {oz} {os j} p r = absurd (i0≢iv p)
δ0ʳ-inj q {os i} {oz} p r = absurd (i0≢iv r)
δ0ʳ-inj q {os i} {os j} p r = cong os (q p r)

δ1ʳ-inj : ∀ {m n} {i* : RawCubeMap m n}
  → Injective! i*
  → Injective! (δ1ʳ i*)
δ1ʳ-inj q {oz} {oz} p r = refl
δ1ʳ-inj q {oz} {os j} p r = absurd (i1≢iv p)
δ1ʳ-inj q {os i} {oz} p r = absurd (i1≢iv r)
δ1ʳ-inj q {os i} {os j} p r = cong os (q p r)

δ0ᵐ : ∀ {m n} → CubeMap m n → CubeMap m (ds n)
δ0ᵐ (cm i* i*-inj) = cm (δ0ʳ i*) (δ0ʳ-inj i*-inj)

δ1ᵐ : ∀ {m n} → CubeMap m n → CubeMap m (ds n)
δ1ᵐ (cm i* i*-inj) = cm (δ1ʳ i*) (δ1ʳ-inj i*-inj)

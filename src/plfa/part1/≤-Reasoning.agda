open import plfa.part1.Equality using (_≡_; refl; ℕ; zero; suc; _+_; +-comm)

module plfa.part1.≤-Reasoning where


data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ} → zero ≤ n
  s≤s : ∀ {m n : ℕ} → m ≤ n → suc m ≤ suc n

infix 4 _≤_

infix  1 begin_
infixr 2 _≤⟨⟩_ _≤⟨_⟩_ _≡⟨_⟩_
infix  3 _∎

≤-trans : ∀ {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
≤-trans z≤n _ = z≤n
≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)

≤-refl : ∀ {x : ℕ} → x ≤ x
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

begin_ : ∀ {x y : ℕ} → x ≤ y → x ≤ y
begin x≤y = x≤y

_≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ} → x ≤ y → x ≤ y
x ≤⟨⟩ x≤y = x≤y

_≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
x ≤⟨ x≤y ⟩ y≤z = ≤-trans x≤y y≤z

_≡⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ} → x ≡ y → y ≤ z → x ≤ z
x ≡⟨ refl ⟩ y≤z = y≤z

_∎ : ∀ (x : ℕ) → x ≤ x
x ∎ = ≤-refl


+-monoʳ-≤ : ∀ (n p q : ℕ) → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q =
  begin
    zero + p
  ≤⟨ p≤q ⟩
    zero + q
  ∎
+-monoʳ-≤ (suc n) p q p≤q =
  begin
    suc n + p
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc n + q
  ∎

+-monoˡ-≤ : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n =
  begin
    m + p
  ≡⟨ +-comm m p ⟩
    p + m
  ≤⟨ +-monoʳ-≤ p m n m≤n ⟩
    p + n
  ≡⟨ +-comm p n ⟩
    n + p
  ∎

+-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
  begin
    m + p
  ≤⟨ +-monoˡ-≤ m n p m≤n ⟩
    n + p
  ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
    n + q
  ∎

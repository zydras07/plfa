open import Data.String using (String; _≟_)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary using (¬_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥-elim)

module plfa.part2.Hoare where

infix 4 _∈_
infix 5 _,_≔_
infix 6 ~_

infixl 7 _＋_
infix  8 ！_
infixr 4 _≔_
infixr 3 _⨾_
infix  2 _⦅_⦆_

Id : Set
Id = String

data Maybe (A : Set) : Set where
  just : A → Maybe A
  nothing : Maybe A

data AExpr : Set where
  lit : ℕ → AExpr
  _＋_ : AExpr → AExpr → AExpr
  _⋆_ : AExpr → AExpr → AExpr
  ！_ : Id → AExpr

data BExpr : Set where
  lit : Bool → BExpr
  _&_ : BExpr → BExpr → BExpr
  _∣_ : BExpr → BExpr → BExpr
  ~_ : BExpr → BExpr
  _⊏_ : AExpr → AExpr → BExpr
  _＝_ : AExpr → AExpr → BExpr

data Cmd : Set where
  skip : Cmd
  _≔_ : Id → AExpr → Cmd
  _⨾_ : Cmd → Cmd → Cmd
  if_then_else_ : BExpr → Cmd → Cmd → Cmd
  while_do′_ : BExpr → Cmd → Cmd

data Store : Set where
  ∅ : Store
  _,_≔_ : Store → Id → ℕ → Store

data _∈_ : Id → Store → Set where
  Z : ∀ {σ x n}
    → x ∈ σ , x ≔ n

  S : ∀ {σ x y n}
    → x ≢ y
    → x ∈ σ
    → x ∈ σ , y ≔ n

get : ∀ (σ : Store) (x : Id) → {x ∈ σ} → ℕ
get (σ , x ≔ n) x′ {Z} = n
get (σ , x ≔ n) x′ {S _ x∈σ} = get σ x′ {x∈σ}

get? : Store → Id → Maybe ℕ
get? ∅ x = nothing
get? (σ , y ≔ n) x with x ≟ y
... | yes _ = just n
... | no _  = get? σ x

Assertion : Set₁
Assertion = Store → Set

-- data Assertion′ : Store → Set where
--   ⊤′ : ∀ {σ : Store} → Assertion′ σ
--   ⊥′ : ∀ {σ : Store} → Assertion′ σ
--   _∧′_ : ∀ {σ : Store} → Assertion′ σ → Assertion′ σ → Assertion′ σ
--   _∨′_ : ∀ {σ : Store} → Assertion′ σ → Assertion′ σ → Assertion′ σ
--   _¬′_ : ∀ {σ : Store} → Assertion′ σ → Assertion′ σ
--   _≡′_ : ∀ {σ : Store} → AExpr → AExpr → Assertion′ σ

_<ᵇ_ : ℕ → ℕ → Bool
m <ᵇ zero = false
zero <ᵇ suc n = true
suc m <ᵇ suc n = m <ᵇ n

_=ᵇ_ : ℕ → ℕ → Bool
zero =ᵇ zero = true
zero =ᵇ suc n = false
suc m =ᵇ zero = false
suc m =ᵇ suc n = m =ᵇ n

data ⟨_,_⟩⇓ₐ_ : AExpr → Store → AExpr → Set where
  lit⇓ : ∀ {σ n}
    → ⟨ lit n , σ ⟩⇓ₐ lit n

  ＋⇓ : ∀ {σ m n e₁ e₂}
    → ⟨ e₁ , σ ⟩⇓ₐ lit m
    → ⟨ e₂ , σ ⟩⇓ₐ lit n
    → ⟨ e₁ ＋ e₂ , σ ⟩⇓ₐ lit (m + n)

  ⋆⇓ : ∀ {σ m n e₁ e₂}
    → ⟨ e₁ , σ ⟩⇓ₐ lit m
    → ⟨ e₂ , σ ⟩⇓ₐ lit n
    → ⟨ e₁ ⋆ e₂ , σ ⟩⇓ₐ lit (m * n)

  ！⇓ : ∀ {σ x}
    → {x∈σ : x ∈ σ}
    → ⟨ ！ x , σ ⟩⇓ₐ lit (get σ x {x∈σ})

data ⟨_,_⟩⇓₂_ : BExpr → Store → BExpr → Set where
  lit⇓ : ∀ {σ b}
    → ⟨ lit b , σ ⟩⇓₂ lit b

  &⇓ : ∀ {σ b₁ b₂ e₁ e₂}
    → ⟨ e₁ , σ ⟩⇓₂ lit b₁
    → ⟨ e₂ , σ ⟩⇓₂ lit b₂
    → ⟨ e₁ & e₂ , σ ⟩⇓₂ lit (b₁ ∧ b₂)

  ∣⇓ : ∀ {σ b₁ b₂ e₁ e₂}
    → ⟨ e₁ , σ ⟩⇓₂ lit b₁
    → ⟨ e₂ , σ ⟩⇓₂ lit b₂
    → ⟨ e₁ ∣ e₂ , σ ⟩⇓₂ lit (b₁ ∨ b₂)

  ~⇓ : ∀ {σ b e}
    → ⟨ e , σ ⟩⇓₂ lit b
    → ⟨ ~ e , σ ⟩⇓₂ lit (not b)

  ⊏⇓ : ∀ {σ m n e₁ e₂}
    → ⟨ e₁ , σ ⟩⇓ₐ lit m
    → ⟨ e₂ , σ ⟩⇓ₐ lit n
    → ⟨ e₁ ⊏ e₂ , σ ⟩⇓₂ lit (m <ᵇ n)

  ＝⇓ : ∀ {σ m n e₁ e₂}
    → ⟨ e₁ , σ ⟩⇓ₐ lit m
    → ⟨ e₂ , σ ⟩⇓ₐ lit n
    → ⟨ e₁ ＝ e₂ , σ ⟩⇓₂ lit (m =ᵇ n)

data ⟨_,_⟩⇓ᵢ_ : Cmd → Store → Store → Set where
  skip⇓ : ∀ {σ}
    → ⟨ skip , σ ⟩⇓ᵢ σ

  ≔⇓ : ∀ {σ σ′ x e n}
    → ⟨ e , σ ⟩⇓ₐ lit n
    → σ′ ≡ σ , x ≔ n
    → ⟨ x ≔ e , σ ⟩⇓ᵢ σ′

  ⨾⇓ : ∀ {σ σ′ σ′′ c₁ c₂}
    → ⟨ c₁ , σ ⟩⇓ᵢ σ′
    → ⟨ c₂ , σ′ ⟩⇓ᵢ σ′′
    → ⟨ c₁ ⨾ c₂ , σ ⟩⇓ᵢ σ′′

  if-true⇓ : ∀ {σ σ′ e c₁ c₂}
    → ⟨ e , σ ⟩⇓₂ lit true
    → ⟨ c₁ , σ ⟩⇓ᵢ σ′
    → ⟨ if e then c₁ else c₂ , σ ⟩⇓ᵢ σ′

  if-false⇓ : ∀ {σ σ′ e c₁ c₂}
    → ⟨ e , σ ⟩⇓₂ lit false
    → ⟨ c₂ , σ ⟩⇓ᵢ σ′
    → ⟨ if e then c₁ else c₂ , σ ⟩⇓ᵢ σ′

  while-true⇓ : ∀ {σ σ′ σ′′ e c}
    → ⟨ e , σ ⟩⇓₂ lit true
    → ⟨ c , σ ⟩⇓ᵢ σ′
    → ⟨ while e do′ c , σ′ ⟩⇓ᵢ σ′′
    → ⟨ while e do′ c , σ ⟩⇓ᵢ σ′′

  while-false⇓ : ∀ {σ e c}
    → ⟨ e , σ ⟩⇓₂ lit false
    → ⟨ while e do′ c , σ ⟩⇓ᵢ σ

-- data _⦅_⦆_ : BExpr → Cmd → BExpr → Set where
--   ⦅⦆-skip : ∀ {P}
--     → P ⦅ skip ⦆ P

--   ⦅⦆-⨾ : ∀ {P Q R c₁ c₂}
--     → P ⦅ c₁ ⦆ Q
--     → Q ⦅ c₂ ⦆ R
--     → P ⦅ c₁ ⨾ c₂ ⦆ R

--   ⦅⦆-if : ∀ {P B Q c₁ c₂}
--     → P & B ⦅ c₁ ⦆ Q
--     → P & (~ B) ⦅ c₂ ⦆ Q
--     → P ⦅ if B then c₁ else c₂ ⦆ Q

--   ⦅⦆-while : ∀ {P B c}
--     → P & B ⦅ c ⦆ P
--     → P ⦅ while B do′ c ⦆ P & (~ B)

--   ⦅⦆-⇒ : ∀ {P₁ P₂ Q₁ Q₂ c}
--     → P₁
--     → P & B ⦅ c ⦆ P
--     → P ⦅ while B do′ c ⦆ P & (~ B)



_⦅_⦆′_ : Assertion → Cmd → Assertion → Set
P ⦅ c ⦆′ Q = ∀ {σ σ′} → P σ → ⟨ c , σ ⟩⇓ᵢ σ′ → Q σ′

ex₁ : (λ _ → ⊤) ⦅ "x" ≔ lit 3 ⦆′ (λ σ → get? σ "x" ≡ just 3)
ex₁ tt (≔⇓ lit⇓ refl) = refl

ex₂ : (λ _ → ⊤) ⦅ "x" ≔ lit 3 ⨾ "y" ≔ ！ "x" ＋ lit 3 ⦆′ (λ σ → get? σ "y" ≡ just 6)
ex₂ tt (⨾⇓ (≔⇓ lit⇓ refl) (≔⇓ (＋⇓ (！⇓ {x∈σ = Z}) lit⇓) refl)) = refl
ex₂ tt (⨾⇓ (≔⇓ lit⇓ refl) (≔⇓ (＋⇓ (！⇓ {x∈σ = S x≢x _}) lit⇓) refl)) = ⊥-elim (x≢x refl)

-- ex₃ : (λ _ → ⊤) ⦅ "x" ≔ lit 0 ⨾ while ((！ "x") ⊏ (lit 3)) do′ ("x" ≔ ！ "x" ＋ lit 1) ⦆′ (λ σ → get? σ "x" ≡ just 3)
-- ex₃ tt (⨾⇓ (≔⇓ lit⇓ refl) (while-true⇓ xl (≔⇓ x x₁) (while-true⇓ x₂ (≔⇓ x₃ x₄) (while-true⇓ x₅ (≔⇓ x₆ x₇) (while-true⇓ x₈ (≔⇓ x₉ x₁₀) (while-true⇓ x₁₁ (≔⇓ x₁₂ x₁₃) (while-true⇓ x₁₄ (≔⇓ x₁₅ x₁₆) (while-true⇓ x₁₇ (≔⇓ x₁₈ x₁₉) x8)))))))) = {!!}
-- ex₃ tt (⨾⇓ (≔⇓ lit⇓ refl) (while-true⇓ xl (≔⇓ x x₁) (while-true⇓ x₂ (≔⇓ x₃ x₄) (while-true⇓ x₅ (≔⇓ x₆ x₇) (while-true⇓ x₈ (≔⇓ x₉ x₁₀) (while-true⇓ x₁₁ (≔⇓ x₁₂ x₁₃) (while-true⇓ x₁₄ (≔⇓ x₁₅ x₁₆) (while-false⇓ x₁₇)))))))) = {!!}
-- ex₃ tt (⨾⇓ (≔⇓ lit⇓ refl) (while-true⇓ xl (≔⇓ x x₁) (while-true⇓ x₂ (≔⇓ x₃ x₄) (while-true⇓ x₅ (≔⇓ x₆ x₇) (while-true⇓ x₈ (≔⇓ x₉ x₁₀) (while-true⇓ x₁₁ (≔⇓ x₁₂ x₁₃) (while-false⇓ x₁₄))))))) = {!!}
-- ex₃ tt (⨾⇓ (≔⇓ lit⇓ refl) (while-true⇓ xl (≔⇓ x x₁) (while-true⇓ x₂ (≔⇓ x₃ x₄) (while-true⇓ x₅ (≔⇓ x₆ x₇) (while-true⇓ x₈ (≔⇓ x₉ x₁₀) (while-false⇓ x₁₁)))))) = {!!}
-- ex₃ tt (⨾⇓ (≔⇓ lit⇓ refl) (while-true⇓ xl (≔⇓ x x₁) (while-true⇓ x₂ (≔⇓ x₃ x₄) (while-true⇓ x₅ (≔⇓ x₆ x₇) (while-false⇓ x₈))))) = {!!}
-- ex₃ tt (⨾⇓ (≔⇓ lit⇓ refl) (while-true⇓ xl (≔⇓ x x₁) (while-true⇓ x₂ (≔⇓ x₃ x₄) (while-false⇓ x₅)))) = {!!}
-- ex₃ tt (⨾⇓ (≔⇓ lit⇓ refl) (while-true⇓ xl (≔⇓ x x₁) (while-false⇓ x₂))) = {!!}
-- ex₃ tt (⨾⇓ (≔⇓ lit⇓ refl) (while-false⇓ )) = {!!}

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
    → suc m ≤ suc n

_² : ℕ → ℕ
n ² = n * n

ex₃ : ∀ (n : ℕ) → {1 ≤ n} → 1 ≤ (n ²)
ex₃ (suc n) = s≤s z≤n

+-monoˡ : ∀ (m n p : ℕ) → n ≤ p → (m + n) ≤ (m + p)
+-monoˡ zero n p n≤p = n≤p
+-monoˡ (suc m) n p n≤p = s≤s (+-monoˡ m n p n≤p)

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

ex₆ : ∀ (m n : ℕ) → m ≤ (n + m)
ex₆ zero n = z≤n
ex₆ (suc m) n rewrite +-suc n m = s≤s (ex₆ m n)

ex₄ : ∀ (m n : ℕ) → {1 ≤ n} → m ≤ (m * n)
ex₄ zero n = z≤n
ex₄ (suc m) (suc n) = s≤s ?

ex₅ : ∀ (n : ℕ) → {1 ≤ n} → ((n ²) + 4) ≤ ((n ²) + 4 * (n ²))
ex₅ (suc n) = s≤s (+-monoˡ (n + n * suc n) 4 (4 * (suc n ²)) {!!} )

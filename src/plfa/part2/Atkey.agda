module plfa.part2.Atkey where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)

data Expr (V : Set) : Set where
  literal : ℕ → Expr V
  var : V → Expr V
  _`+`_ : Expr V → Expr V → Expr V

evaluate : ∀ {V : Set} → Expr V → (V → ℕ) → ℕ
evaluate (literal n) env = n
evaluate (var v) env = env v
evaluate (e₁ `+` e₂) env = evaluate e₁ env + evaluate e₂ env

simplify : ∀ {V : Set} → Expr V → Expr V
simplify (literal n) = literal n
simplify (var v) = var v
simplify (e₁ `+` e₂) with simplify e₁
... | literal zero = simplify e₂
... | e₁′ with simplify e₂
... | literal zero = e₁′
... | e₂′ = e₁′ `+` e₂′

-- simplify-correct : {V : Set} (e : Expr V) (env : V → ℕ) → evaluate e env ≡ evaluate (simplify e) env
-- simplify-correct (literal n) env = refl
-- simplify-correct (var v) env = refl
-- simplify-correct (literal zero `+` e₂) env = simplify-correct e₂ env
-- simplify-correct (e₁ `+` literal zero) env = {!!}
-- simplify-correct (literal zero `+` e₂) env = simplify-correct e₂ env
-- simplify-correct (e₁ `+` literal zero) env rewrite +-identityʳ evaluate e₁ env = {!!}
-- simplify-correct (e₁ `+` e₂) env = {!!}

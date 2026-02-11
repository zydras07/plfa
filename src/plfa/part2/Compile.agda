module plfa.part2.Compile where

open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality hiding ([_])

data Expr : Set where
  Const : ℕ → Expr
  _⊞_ : Expr → Expr → Expr
  _⊠_ : Expr → Expr → Expr

eval : Expr → ℕ
eval (Const x) = x
eval (p ⊞ q) = eval p + eval q
eval (p ⊠ q) = eval p * eval q

data Instr : Set where
  Push : ℕ → Instr
  Mult Add : Instr

instr-semantics : Instr → List ℕ → List ℕ
instr-semantics (Push x) s       = x ∷ s
instr-semantics Mult (y ∷ x ∷ s) = x * y ∷ s
instr-semantics Add  (y ∷ x ∷ s) = x + y ∷ s
instr-semantics _ _ = []

execute : List Instr → List ℕ → List ℕ
execute []       s = s
execute (i ∷ is) s = execute is (instr-semantics i s)

compile : Expr → List Instr
compile (Const x) = [ Push x ]
compile (e₁ ⊞ e₂) = compile e₁ ++ compile e₂ ++ [ Add  ]
compile (e₁ ⊠ e₂) = compile e₁ ++ compile e₂ ++ [ Mult ]

execute-compile-++ : ∀ as bs s → execute (as ++ bs) s ≡ execute bs (execute as s)
execute-compile-++ [] bs s = refl
execute-compile-++ (a ∷ as) bs s = execute-compile-++ as bs (instr-semantics a s)

compile-correct′ : ∀ e s → execute (compile e) s ≡ eval e ∷ s
compile-correct′ (Const x) s = refl
compile-correct′ (e₁ ⊞ e₂) s
  rewrite execute-compile-++ (compile e₁) (compile e₂ ++ [ Add ]) s
        | execute-compile-++ (compile e₂) [ Add ] (execute (compile e₁) s)
        | compile-correct′ e₁ s
        | compile-correct′ e₂ (eval e₁ ∷ s) = refl
compile-correct′ (e₁ ⊠ e₂) s
  rewrite execute-compile-++ (compile e₁) (compile e₂ ++ [ Mult ]) s
        | execute-compile-++ (compile e₂) [ Mult ] (execute (compile e₁) s)
        | compile-correct′ e₁ s
        | compile-correct′ e₂ (eval e₁ ∷ s) = refl

compile-correct : ∀ e → execute (compile e) [] ≡ [ eval e ]
compile-correct e = compile-correct′ e []

module plfa.part2.BisimulationProduct where

open import plfa.part2.More

infix  4 _~_
infix  5 ~ƛ_
infix  7 _~·_

data _~_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ~` : ∀ {Γ A} {x : Γ ∋ A}
     ---------
   → ` x ~ ` x

  ~ƛ_ : ∀ {Γ A B} {N N† : Γ , A ⊢ B}
    → N ~ N†
      ----------
    → ƛ N ~ ƛ N†

  _~·_ : ∀ {Γ A B} {L L† : Γ ⊢ A ⇒ B} {M M† : Γ ⊢ A}
    → L ~ L†
    → M ~ M†
      ---------------
    → L · M ~ L† · M†

  ~let : ∀ {Γ A B} {M M† : Γ ⊢ A} {N N† : Γ , A ⊢ B}
    → M ~ M†
    → N ~ N†
      ----------------------
    → `let M N ~ (ƛ N†) · M†

  ~proj₁ : ∀ {Γ A B} {M M† : Γ ⊢ A `× B}
    → M ~ M†
      -------------------------
    → `proj₁ M ~ case× M† (# 1)

  ~proj₂ : ∀ {Γ A B} {M M† : Γ ⊢ A `× B}
    → M ~ M†
      -------------------------
    → `proj₂ M ~ case× M† (# 0)


~val : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M
    --------
  → Value M†
~val ~`           ()
~val (~ƛ ~N)      V-ƛ  =  V-ƛ
~val (~L ~· ~M)   ()
~val (~let ~M ~N) ()
~val (~proj₁ ~M)  ()
~val (~proj₂ ~M)  ()


~val⁻¹ : ∀ {Γ A} {M M† : Γ ⊢ A}
  → M ~ M†
  → Value M†
    --------
  → Value M
~val⁻¹ ~`           ()
~val⁻¹ (~ƛ ~N)      V-ƛ  =  V-ƛ
~val⁻¹ (~L ~· ~M)   ()
~val⁻¹ (~let ~M ~N) ()
~val⁻¹ (~proj₁ ~M)  ()
~val⁻¹ (~proj₂ ~M)  ()


~rename : ∀ {Γ Δ}
  → (ρ : ∀ {A} → Γ ∋ A → Δ ∋ A)
    ----------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → rename ρ M ~ rename ρ M†)
~rename ρ (~`)          =  ~`
~rename ρ (~ƛ ~N)       =  ~ƛ (~rename (ext ρ) ~N)
~rename ρ (~L ~· ~M)    =  (~rename ρ ~L) ~· (~rename ρ ~M)
~rename ρ (~let ~M ~N)  =  ~let (~rename ρ ~M) (~rename (ext ρ) ~N)
~rename ρ (~proj₁ ~M)   =  ~proj₁ (~rename ρ ~M)
~rename ρ (~proj₂ ~M)   =  ~proj₂ (~rename ρ ~M)


~exts : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    --------------------------------------------------
  → (∀ {A B} → (x : Γ , B ∋ A) → exts σ x ~ exts σ† x)
~exts ~σ Z      =  ~`
~exts ~σ (S x)  =  ~rename S_ (~σ x)


~subst : ∀ {Γ Δ}
  → {σ  : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → {σ† : ∀ {A} → Γ ∋ A → Δ ⊢ A}
  → (∀ {A} → (x : Γ ∋ A) → σ x ~ σ† x)
    ---------------------------------------------------------
  → (∀ {A} {M M† : Γ ⊢ A} → M ~ M† → subst σ M ~ subst σ† M†)
~subst ~σ (~` {x = x})  =  ~σ x
~subst ~σ (~ƛ ~N)       =  ~ƛ (~subst (~exts ~σ) ~N)
~subst ~σ (~L ~· ~M)    =  (~subst ~σ ~L) ~· (~subst ~σ ~M)
~subst ~σ (~let ~M ~N)  =  ~let (~subst ~σ ~M) (~subst (~exts ~σ) ~N)
~subst ~σ (~proj₁ ~M)   =  ~proj₁ (~subst ~σ ~M)
~subst ~σ (~proj₂ ~M)   =  ~proj₂ (~subst ~σ ~M)


~sub : ∀ {Γ A B} {N N† : Γ , B ⊢ A} {M M† : Γ ⊢ B}
  → N ~ N†
  → M ~ M†
    -----------------------
  → (N [ M ]) ~ (N† [ M† ])
~sub {Γ} {A} {B} ~N ~M = ~subst {Γ , B} {Γ} ~σ {A} ~N
  where
  ~σ : ∀ {A} → (x : Γ , B ∋ A) → _ ~ _
  ~σ Z      =  ~M
  ~σ (S x)  =  ~`


data Leg {Γ A} (M† N : Γ ⊢ A) : Set where

  leg : ∀ {N† : Γ ⊢ A}
    → N ~ N†
    → M† —→ N†
      --------
    → Leg M† N


sim : ∀ {Γ A} {M M† N : Γ ⊢ A}
  → M ~ M†
  → M —→ N
    ---------
  → Leg M† N
sim ~`              ()
sim (~ƛ ~N)         ()
sim (~L ~· ~M)      (ξ-·₁ L—→)
  with sim ~L L—→
...  | leg ~L′ L†—↠                 = leg (~L′ ~· ~M)    (ξ-·₁ L†—↠)
sim (~V ~· ~M)      (ξ-·₂ VV M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→                 =  leg (~V ~· ~M′)   (ξ-·₂ (~val ~V VV) M†—→)
sim ((~ƛ ~N) ~· ~V) (β-ƛ VV)        =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
sim (~let ~M ~N)    (ξ-let M—→)
  with sim ~M M—→
...  | leg ~M′ M†—→                 =  leg (~let ~M′ ~N) (ξ-·₂ V-ƛ M†—→)
sim (~let ~V ~N)    (β-let VV)      =  leg (~sub ~N ~V)  (β-ƛ (~val ~V VV))
sim (~proj₁ ~M)     (ξ-proj₁ M—→)
  with sim ~M M—→
... | leg ~M′ M†—→ = leg (~proj₁ ~M′) (ξ-case× M†—→)
sim (~proj₂ ~M)     (ξ-proj₂ M—→)
  with sim ~M M—→
... | leg ~M′ M†—→ = leg (~proj₂ ~M′) (ξ-case× M†—→)


data Leg⁻¹ {Γ A} (M N† : Γ ⊢ A) : Set where
  leg⁻¹ : ∀ {N : Γ ⊢ A}
    → N ~ N†
    → M —→ N
      ----------
    → Leg⁻¹ M N†


sim⁻¹ : ∀ {Γ A} {M M† N† : Γ ⊢ A}
  → M ~ M†
  → M† —→ N†
    ----------
  → Leg⁻¹ M N†
sim⁻¹ ~` ()
sim⁻¹ (~ƛ ~N) ()
sim⁻¹ (~L ~· ~M) (ξ-·₁ L†—→)
  with sim⁻¹ ~L L†—→
... | leg⁻¹ ~L′ L—→ = leg⁻¹ (~L′ ~· ~M) (ξ-·₁ L—→)
sim⁻¹ (~L ~· ~M) (ξ-·₂ V-L† M†—→)
  with sim⁻¹ ~M M†—→
... | leg⁻¹ ~M′ M—→ = leg⁻¹ (~L ~· ~M′) (ξ-·₂ (~val⁻¹ ~L V-L†) M—→)
sim⁻¹ ((~ƛ ~N) ~· ~M) (β-ƛ V-M†) = leg⁻¹ (~sub ~N ~M) (β-ƛ (~val⁻¹ ~M V-M†))
sim⁻¹ (~let ~M ~N) (ξ-·₂ V-N† M†—→)
  with sim⁻¹ ~M M†—→
... | leg⁻¹ ~M′ M—→ = leg⁻¹ (~let ~M′ ~N) (ξ-let M—→)
sim⁻¹ (~let ~M ~N) (β-ƛ V-M†) = leg⁻¹ (~sub ~N ~M) (β-let (~val⁻¹ ~M V-M†))
sim⁻¹ (~proj₁ ~M) (ξ-case× M†—→)
  with sim⁻¹ ~M M†—→
... | leg⁻¹ ~M′ M—→ = leg⁻¹ (~proj₁ ~M′) (ξ-proj₁ M—→)
sim⁻¹ (~proj₂ ~M) (ξ-case× M†—→)
  with sim⁻¹ ~M M†—→
... | leg⁻¹ ~M′ M—→ = leg⁻¹ (~proj₂ ~M′) (ξ-proj₂ M—→)

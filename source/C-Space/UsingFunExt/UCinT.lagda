Chuangjie Xu 2013 (update in February 2015, ported to TypeTopology in 2025)

We extend System T with a Fan functional, use it to formulate the
uniform-continuity principle, and validate the principle via C-spaces.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (_+_)
open import UF.FunExt using (DN-funext)

module C-Space.UsingFunExt.UCinT (fe : DN-funext 𝓤₀ 𝓤₀) where

open import Naturals.Properties

open import C-Space.Preliminaries.Sequence
open import C-Space.Preliminaries.Naturals.Order
open import C-Space.UniformContinuity
open import C-Space.Coverage
open import C-Space.UsingFunExt.Space
open import C-Space.UsingFunExt.CartesianClosedness fe
open import C-Space.UsingFunExt.DiscreteSpace fe
open import C-Space.UsingFunExt.YonedaLemma fe
open import C-Space.UsingFunExt.Fan fe

\end{code}

Syntax

\begin{code}

infixr 10 _⊠_
infixr 10 _⇨_

data Ty : Set where
 ② : Ty
 Ⓝ : Ty
 _⊠_ : Ty → Ty → Ty
 _⇨_ : Ty → Ty → Ty

infixl 10 _₊_

data Cxt : ℕ → Set where
 ε : Cxt zero
 _₊_ : {n : ℕ} → Cxt n → Ty → Cxt (succ n)

data Fin : ℕ → Set where
 zero : {n : ℕ} → Fin (succ n)
 succ : {n : ℕ} → Fin n → Fin (succ n)

_[_] : {n : ℕ} → Cxt n → Fin n → Ty
(xs ₊ x) [ zero ]   = x
(xs ₊ x) [ succ i ] = xs [ i ]

infixl 10 _◦_

data Tm : {n : ℕ} → Cxt n → Ty → Set where
 VAR  : {n : ℕ}{Γ : Cxt n}           → (i : Fin n) → Tm Γ (Γ [ i ])
 ⊥    : {n : ℕ}{Γ : Cxt n}           → Tm Γ ②
 ⊤    : {n : ℕ}{Γ : Cxt n}           → Tm Γ ②
 IF   : {n : ℕ}{Γ : Cxt n}{σ : Ty}   → Tm Γ (② ⇨ σ ⇨ σ ⇨ σ)
 ZERO : {n : ℕ}{Γ : Cxt n}           → Tm Γ Ⓝ
 SUCC : {n : ℕ}{Γ : Cxt n}           → Tm Γ (Ⓝ ⇨ Ⓝ)
 REC  : {n : ℕ}{Γ : Cxt n}{σ : Ty}   → Tm Γ (σ ⇨ (Ⓝ ⇨ σ ⇨ σ) ⇨ Ⓝ ⇨ σ)
 PAIR : {n : ℕ}{Γ : Cxt n}{σ τ : Ty} → Tm Γ σ → Tm Γ τ → Tm Γ (σ ⊠ τ)
 PRJ₁ : {n : ℕ}{Γ : Cxt n}{σ τ : Ty} → Tm Γ (σ ⊠ τ) → Tm Γ σ
 PRJ₂ : {n : ℕ}{Γ : Cxt n}{σ τ : Ty} → Tm Γ (σ ⊠ τ) → Tm Γ τ
 LAM  : {n : ℕ}{Γ : Cxt n}{σ τ : Ty} → Tm (Γ ₊ σ) τ → Tm Γ (σ ⇨ τ)
 _◦_  : {n : ℕ}{Γ : Cxt n}{σ τ : Ty} → Tm Γ (σ ⇨ τ) → Tm Γ σ → Tm Γ τ
 FAN  : {n : ℕ}{Γ : Cxt n}           → Tm Γ (((Ⓝ ⇨ ②) ⇨ Ⓝ) ⇨ Ⓝ)

infix  10 _==_
infixr 10 _→→_
infixl 10 _∧∧_

data Fml : {n : ℕ} → Cxt n → Set where
 _==_ : {n : ℕ}{Γ : Cxt n}{σ : Ty} → Tm Γ σ → Tm Γ σ → Fml Γ
 _∧∧_ : {n : ℕ}{Γ : Cxt n}         → Fml Γ  → Fml Γ  → Fml Γ
 _→→_ : {n : ℕ}{Γ : Cxt n}         → Fml Γ  → Fml Γ  → Fml Γ

\end{code}

Interpretation

\begin{code}

⟦_⟧ʸ : Ty → Space
⟦ ② ⟧ʸ = 𝟚Space
⟦ Ⓝ ⟧ʸ = ℕSpace
⟦ σ ⊠ τ ⟧ʸ = ⟦ σ ⟧ʸ ⊗ ⟦ τ ⟧ʸ
⟦ σ ⇨ τ ⟧ʸ = ⟦ σ ⟧ʸ ⇒ ⟦ τ ⟧ʸ

⟦_⟧ᶜ : {n : ℕ} → Cxt n → Space
⟦ ε ⟧ᶜ = 𝟙Space
⟦ Γ ₊ A ⟧ᶜ = ⟦ Γ ⟧ᶜ ⊗ ⟦ A ⟧ʸ

continuous-prj : {n : ℕ}(Γ : Cxt n)(i : Fin n) → Map ⟦ Γ ⟧ᶜ ⟦ Γ [ i ] ⟧ʸ
continuous-prj  ε      ()
continuous-prj (Γ ₊ σ)  zero    = pr₂ , (λ _ → pr₂)
continuous-prj (Γ ₊ σ) (succ i) = prjᵢ₊₁ , cprjᵢ₊₁
 where
  prjᵢ : U ⟦ Γ ⟧ᶜ → U ⟦ Γ [ i ] ⟧ʸ
  prjᵢ = pr₁ (continuous-prj Γ i)
  prjᵢ₊₁ : U ⟦ Γ ₊ σ ⟧ᶜ → U ⟦ (Γ ₊ σ) [ succ i ] ⟧ʸ
  prjᵢ₊₁ (xs , _) = prjᵢ xs
  cprjᵢ : continuous ⟦ Γ ⟧ᶜ ⟦ Γ [ i ] ⟧ʸ prjᵢ
  cprjᵢ = pr₂ (continuous-prj Γ i)
  cprjᵢ₊₁ : continuous ⟦ Γ ₊ σ ⟧ᶜ ⟦ (Γ ₊ σ) [ succ i ] ⟧ʸ prjᵢ₊₁
  cprjᵢ₊₁ p pΓσ = cprjᵢ (pr₁ ∘ p) (pr₁ pΓσ)

⟦_⟧ᵐ : {n : ℕ}{Γ : Cxt n}{σ : Ty} → Tm Γ σ → Map ⟦ Γ ⟧ᶜ ⟦ σ ⟧ʸ
⟦ VAR {_} {Γ} i ⟧ᵐ            = continuous-prj Γ i
⟦ ⊥ {_} {Γ} ⟧ᵐ                = continuous-constant ⟦ Γ ⟧ᶜ ⟦ ② ⟧ʸ ₀
⟦ ⊤ {_} {Γ} ⟧ᵐ                = continuous-constant ⟦ Γ ⟧ᶜ ⟦ ② ⟧ʸ ₁
⟦ IF {_} {Γ} {σ} ⟧ᵐ           = continuous-constant ⟦ Γ ⟧ᶜ ⟦ ② ⇨ σ ⇨ σ ⇨ σ ⟧ʸ (continuous-if ⟦ σ ⟧ʸ)
⟦ ZERO {_} {Γ} ⟧ᵐ             = continuous-constant ⟦ Γ ⟧ᶜ ⟦ Ⓝ ⟧ʸ 0
⟦ SUCC {_} {Γ} ⟧ᵐ             = continuous-constant ⟦ Γ ⟧ᶜ ⟦ Ⓝ ⇨ Ⓝ ⟧ʸ continuous-succ
⟦ REC {_} {Γ} {σ} ⟧ᵐ          = continuous-constant ⟦ Γ ⟧ᶜ ⟦ σ ⇨ (Ⓝ ⇨ σ ⇨ σ) ⇨ Ⓝ ⇨ σ ⟧ʸ (continuous-rec ⟦ σ ⟧ʸ)
⟦ PAIR {_} {Γ} {σ} {τ} M N ⟧ᵐ = continuous-pair ⟦ Γ ⟧ᶜ ⟦ σ ⟧ʸ ⟦ τ ⟧ʸ ⟦ M ⟧ᵐ ⟦ N ⟧ᵐ
⟦ PRJ₁ {_} {Γ} {σ} {τ} W ⟧ᵐ   = continuous-pr₁ ⟦ Γ ⟧ᶜ ⟦ σ ⟧ʸ ⟦ τ ⟧ʸ ⟦ W ⟧ᵐ
⟦ PRJ₂ {_} {Γ} {σ} {τ} W ⟧ᵐ   = continuous-pr₂ ⟦ Γ ⟧ᶜ ⟦ σ ⟧ʸ ⟦ τ ⟧ʸ ⟦ W ⟧ᵐ
⟦ LAM {_} {Γ} {σ} {τ} M ⟧ᵐ    = continuous-λ ⟦ Γ ⟧ᶜ ⟦ σ ⟧ʸ ⟦ τ ⟧ʸ ⟦ M ⟧ᵐ
⟦ _◦_ {_} {Γ} {σ} {τ} M N ⟧ᵐ  = continuous-app ⟦ Γ ⟧ᶜ ⟦ σ ⟧ʸ ⟦ τ ⟧ʸ ⟦ M ⟧ᵐ ⟦ N ⟧ᵐ
⟦ FAN {_} {Γ} ⟧ᵐ              = continuous-constant ⟦ Γ ⟧ᶜ ⟦ ((Ⓝ ⇨ ②) ⇨ Ⓝ) ⇨ Ⓝ ⟧ʸ fan

⟦_⟧ᶠ : {n : ℕ}{Γ : Cxt n} → Fml Γ → U ⟦ Γ ⟧ᶜ → Set
⟦ t == u ⟧ᶠ ρ = pr₁ ⟦ t ⟧ᵐ ρ ＝ pr₁ ⟦ u ⟧ᵐ ρ
⟦ φ ∧∧ ψ ⟧ᶠ ρ = (⟦ φ ⟧ᶠ ρ) × (⟦ ψ ⟧ᶠ ρ)
⟦ φ →→ ψ ⟧ᶠ ρ = (⟦ φ ⟧ᶠ ρ) → (⟦ ψ ⟧ᶠ ρ)

\end{code}

We say a formula is validated by the model if

\begin{code}

_is-validated : {n : ℕ}{Γ : Cxt n} → Fml Γ → Set
φ is-validated = ∀ ρ → ⟦ φ ⟧ᶠ ρ

\end{code}

Formulation of the uniform-continuity principle within T:

\begin{code}

EQ : {n : ℕ}{Γ : Cxt n} → Tm Γ ② → Tm Γ ② → Tm Γ ②
EQ B₀ B₁ = IF ◦ B₀ ◦ (IF ◦ B₁ ◦ ⊤ ◦ ⊥) ◦ B₁

eq : 𝟚 → 𝟚 → 𝟚
eq b₀ b₁ = if b₀ (if b₁ ₁ ₀) b₁

Lemma[eq] : (b₀ b₁ : 𝟚) → eq b₀ b₁ ＝ ₁ → b₀ ＝ b₁
Lemma[eq] ₀ ₀ refl = refl
Lemma[eq] ₀ ₁ ()
Lemma[eq] ₁ ₀ ()
Lemma[eq] ₁ ₁ refl = refl

MIN : {n : ℕ}{Γ : Cxt n} → Tm Γ ② → Tm Γ ② → Tm Γ ②
MIN B₀ B₁ = IF ◦ B₀ ◦ ⊥ ◦ B₁

min : 𝟚 → 𝟚 → 𝟚
min b₀ b₁ = if b₀ ₀ b₁

Lemma[min] : (b₀ b₁ : 𝟚) → min b₀ b₁ ＝ ₁ → (b₀ ＝ ₁) × (b₁ ＝ ₁)
Lemma[min] ₀ ₀ ()
Lemma[min] ₀ ₁ ()
Lemma[min] ₁ ₀ ()
Lemma[min] ₁ ₁ refl = refl , refl


ν₀ : {n : ℕ}{Γ : Cxt (succ n)} →
     Tm Γ (Γ [ zero ])
ν₀ = VAR zero
ν₁ : {n : ℕ}{Γ : Cxt (succ (succ n))} →
     Tm Γ (Γ [ succ zero ])
ν₁ = VAR (succ zero)
ν₂ : {n : ℕ}{Γ : Cxt (succ (succ (succ n)))} →
     Tm Γ (Γ [ succ (succ zero) ])
ν₂ = VAR (succ (succ zero))
ν₃ : {n : ℕ}{Γ : Cxt (succ (succ (succ (succ n))))} →
     Tm Γ (Γ [ succ (succ (succ zero)) ])
ν₃ = VAR (succ (succ (succ zero)))

Γ : Cxt 3
Γ = ε ₊ ((Ⓝ ⇨ ②) ⇨ Ⓝ) ₊ (Ⓝ ⇨ ②) ₊ (Ⓝ ⇨ ②)

F : Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F = ν₂

A B : Tm Γ (Ⓝ ⇨ ②)
A = ν₁
B = ν₀

A' B' : Tm (Γ ₊ Ⓝ ₊ ②) (Ⓝ ⇨ ②)
A' = ν₃
B' = ν₂

A＝⟦FAN•F⟧B : Tm Γ ②
A＝⟦FAN•F⟧B = REC ◦ ⊤ ◦ (LAM (LAM (MIN (EQ (A' ◦ ν₁) (B' ◦ ν₁)) ν₀))) ◦ (FAN ◦ F)

Principle[UC] : Fml Γ
Principle[UC] = (A＝⟦FAN•F⟧B == ⊤) →→ ((F ◦ A) == (F ◦ B))

\end{code}

The uniform-continuity principle is validated by the model:

\begin{code}

Theorem : Principle[UC] is-validated
       -- ∀(ρ : U ⟦ Γ ⟧ᶜ) → ⟦ (A＝⟦FAN•F⟧B == ⊤) →→ (F ◦ A == F ◦ B) ⟧ᶠ ρ
Theorem ρ EN = fan-behaviour f α β en
 where
  f : Map (ℕSpace ⇒ 𝟚Space) ℕSpace
  f = pr₁ ⟦ F ⟧ᵐ ρ
  α β : Map ℕSpace 𝟚Space
  α = pr₁ ⟦ A ⟧ᵐ ρ
  β = pr₁ ⟦ B ⟧ᵐ ρ

  g : ℕ → 𝟚 → 𝟚
  g n b = pr₁ (pr₁ (pr₁ ⟦ LAM (LAM (MIN (EQ (A' ◦ ν₁) (B' ◦ ν₁)) ν₀)) ⟧ᵐ ρ) n) b

  lemma : (k : ℕ) → ℕ-induction ₁ g k ＝ ₁ → pr₁ α ＝⟦ k ⟧ pr₁ β
  lemma 0        refl = ＝⟦zero⟧
  lemma (succ k) esk  = ＝⟦succ⟧ IH claim₁
   where
    ek : ℕ-induction ₁ g k ＝ ₁
    ek = pr₂ (Lemma[min] (eq (pr₁ α k) (pr₁ β k)) (ℕ-induction ₁ g k) esk)
    IH : pr₁ α ＝⟦ k ⟧ pr₁ β
    IH = lemma k ek
    claim₀ : eq (pr₁ α k) (pr₁ β k) ＝ ₁
    claim₀ = pr₁ (Lemma[min] (eq (pr₁ α k) (pr₁ β k)) (ℕ-induction ₁ g k) esk)
    claim₁ : pr₁ α k ＝ pr₁ β k
    claim₁ = Lemma[eq] (pr₁ α k) (pr₁ β k) claim₀

  -- By the above lemma and the assumption that ⟦ A＝⟦FAN•F⟧B == ⊤ ⟧ᶠ ρ ＝ ₁,
  -- the interpretations of the two sequences are equal up to the first ⟦ N ⟧ᵐ position.
  en : pr₁ (pr₁ ⟦ A ⟧ᵐ ρ) ＝⟦ pr₁ ⟦ FAN ◦ F ⟧ᵐ ρ ⟧ pr₁ (pr₁ ⟦ B ⟧ᵐ ρ)
  en = lemma (pr₁ ⟦ FAN ◦ F ⟧ᵐ ρ) EN

\end{code}

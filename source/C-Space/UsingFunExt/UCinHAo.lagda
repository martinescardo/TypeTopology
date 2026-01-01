Chuangjie Xu 2013 (updated in February 2015, ported to TypeTopology in 2025)

We validate the uniform-continuity princile in HAω via C-spaces.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt using (DN-funext)

module C-Space.UsingFunExt.UCinHAo (fe : DN-funext 𝓤₀ 𝓤₀) where

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

infixr 10 _⇨_

data Ty : Set where
 ① : Ty
 ② : Ty
 Ⓝ : Ty
 _⊠_ : Ty → Ty → Ty
 _⇨_ : Ty → Ty → Ty

infixl 10 _₊_

data Cxt : ℕ → Set where
 ε : Cxt 0
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
 ✹    : {n : ℕ}{Γ : Cxt n}           → Tm Γ ①
 UNIT : {n : ℕ}{Γ : Cxt n}{σ : Ty}   → Tm Γ (σ ⇨ ①)
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


infix  9 _==_
infixl 8 _∧∧_
infixr 7 _→→_
infixr 6 Ā_·_
infixr 6 Ē_·_

data HAω : {n : ℕ} → Cxt n → Set where
 _==_ : {n : ℕ}{Γ : Cxt n}{σ : Ty} → Tm Γ σ   → Tm Γ σ      → HAω Γ
 _∧∧_ : {n : ℕ}{Γ : Cxt n}         → HAω Γ    → HAω Γ       → HAω Γ
 _→→_ : {n : ℕ}{Γ : Cxt n}         → HAω Γ    → HAω Γ       → HAω Γ
 Ā_·_ : {n : ℕ}{Γ : Cxt n}         → (σ : Ty) → HAω (Γ ₊ σ) → HAω Γ 
 Ē_·_ : {n : ℕ}{Γ : Cxt n}         → (σ : Ty) → HAω (Γ ₊ σ) → HAω Γ

\end{code}

Interpretation

\begin{code}

⟦_⟧ʸ : Ty → Space
⟦ ① ⟧ʸ = 𝟙Space
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
⟦ ✹ {_} {Γ} ⟧ᵐ                = continuous-constant ⟦ Γ ⟧ᶜ ⟦ ① ⟧ʸ ⋆
⟦ UNIT {_} {Γ} {σ} ⟧ᵐ         = continuous-constant ⟦ Γ ⟧ᶜ ⟦ σ ⇨ ① ⟧ʸ (continuous-unit ⟦ σ ⟧ʸ)
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

\end{code}

Realizability semantic

\begin{code}

∣_∣ : {n : ℕ}{Γ : Cxt n} → HAω Γ → Ty
∣ M == N ∣  = ①
∣ φ ∧∧ ψ ∣  = ∣ φ ∣ ⊠ ∣ ψ ∣
∣ φ →→ ψ ∣  = ∣ φ ∣ ⇨ ∣ ψ ∣
∣ Ā σ · φ ∣ = σ ⇨ ∣ φ ∣
∣ Ē σ · φ ∣ = σ ⊠ ∣ φ ∣

infix 50 _is-realized-by_

_is-realized-by_ : {n : ℕ}{Γ : Cxt n} → (φ : HAω Γ) → U ⟦ Γ ⟧ᶜ × U ⟦ ∣ φ ∣ ⟧ʸ → Set
(M == N)  is-realized-by (ρ , ⋆)     = pr₁ ⟦ M ⟧ᵐ ρ ＝ pr₁ ⟦ N ⟧ᵐ ρ
(φ ∧∧ ψ)  is-realized-by (ρ , x , y) = φ is-realized-by (ρ , x) × ψ is-realized-by (ρ , y)
(φ →→ ψ)  is-realized-by (ρ , f)     = ∀(x : U ⟦ ∣ φ ∣ ⟧ʸ) → φ is-realized-by (ρ , x) → ψ is-realized-by (ρ , pr₁ f x)
(Ā σ · φ) is-realized-by (ρ , f)     = ∀(x : U ⟦ σ ⟧ʸ) → φ is-realized-by ((ρ , x) , pr₁ f x)
(Ē σ · φ) is-realized-by (ρ , x , y) = φ is-realized-by ((ρ , x) , y)

_is-realizable : {n : ℕ}{Γ : Cxt n} → HAω Γ → Set
_is-realizable {n} {Γ} φ = Σ \(w : U ⟦ Γ ⟧ᶜ × U ⟦ ∣ φ ∣ ⟧ʸ) → φ is-realized-by w

\end{code}

Validation of UC

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
ν₄ : {n : ℕ}{Γ : Cxt (succ (succ (succ (succ (succ n)))))} →
     Tm Γ (Γ [ succ (succ (succ (succ zero))) ])
ν₄ = VAR (succ (succ (succ (succ zero))))
ν₅ : {n : ℕ}{Γ : Cxt (succ (succ (succ (succ (succ (succ n))))))} →
     Tm Γ (Γ [ succ (succ (succ (succ (succ zero)))) ])
ν₅ = VAR (succ (succ (succ (succ (succ zero)))))

Γ : Cxt 4
Γ = ε ₊ ((Ⓝ ⇨ ②) ⇨ Ⓝ) ₊ Ⓝ ₊ (Ⓝ ⇨ ②) ₊ (Ⓝ ⇨ ②)

F : Tm Γ ((Ⓝ ⇨ ②) ⇨ Ⓝ)
F = ν₃

M : Tm Γ Ⓝ
M = ν₂

A B : Tm Γ (Ⓝ ⇨ ②)
A = ν₁
B = ν₀

A' B' : Tm (Γ ₊ Ⓝ ₊ ②) (Ⓝ ⇨ ②)
A' = ν₃
B' = ν₂

A＝⟦M⟧B : Tm Γ ②
A＝⟦M⟧B = REC ◦ ⊤ ◦ (LAM (LAM (MIN (EQ (A' ◦ ν₁) (B' ◦ ν₁)) ν₀))) ◦ M

Principle[UC] : HAω ε
Principle[UC] =
   Ā (Ⓝ ⇨ ②) ⇨ Ⓝ     · Ē Ⓝ     · Ā Ⓝ ⇨ ②     · Ā Ⓝ ⇨ ②     ·  A＝⟦M⟧B == ⊤  →→  F ◦ A == F ◦ B
-- ∀ f : (Ⓝ ⇨ ②) ⇨ Ⓝ . ∃ m : Ⓝ . ∀ α : Ⓝ ⇨ ② . ∀ β : Ⓝ ⇨ ② .   α ＝⟦m⟧ β     →     f α ＝ f β

Theorem : Principle[UC] is-realizable
Theorem = (⋆ , e) , prf
 where
  e : U (((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace) ⇒ (ℕSpace ⊗ ((ℕSpace ⇒ 𝟚Space) ⇒ (ℕSpace ⇒ 𝟚Space) ⇒ 𝟙Space ⇒ 𝟙Space)))
  e = g , cts-g
   where
    g : Map (ℕSpace ⇒ 𝟚Space) ℕSpace → ℕ × Map (ℕSpace ⇒ 𝟚Space) ((ℕSpace ⇒ 𝟚Space) ⇒ 𝟙Space ⇒ 𝟙Space)
    g f = pr₁ fan f , g₀ , cts-g₀
     where
      g₀ : Map ℕSpace 𝟚Space → Map (ℕSpace ⇒ 𝟚Space) (𝟙Space ⇒ 𝟙Space)
      g₀ α = g₁ , cts-g₁
       where
        g₁ : Map ℕSpace 𝟚Space → Map 𝟙Space 𝟙Space
        g₁ β = (λ _ → ⋆) , (λ _ _ → ⋆)
        cts-g₁ : continuous (ℕSpace ⇒ 𝟚Space) (𝟙Space ⇒ 𝟙Space) g₁
        cts-g₁ _ _ _ _ _ _ = ⋆
      cts-g₀ : continuous (ℕSpace ⇒ 𝟚Space) ((ℕSpace ⇒ 𝟚Space) ⇒ 𝟙Space ⇒ 𝟙Space) g₀
      cts-g₀ _ _ _ _ _ _ _ _ _ _ = ⋆
    cts-g : continuous ((ℕSpace ⇒ 𝟚Space) ⇒ ℕSpace)
                       (ℕSpace ⊗ ((ℕSpace ⇒ 𝟚Space) ⇒ (ℕSpace ⇒ 𝟚Space) ⇒ 𝟙Space ⇒ 𝟙Space)) g
    cts-g p pP = pr₂ fan p pP , (λ _ _ _ _ _ _ _ _ _ _ _ _ → ⋆)
  prf : Principle[UC] is-realized-by (⋆ , e)
  prf f = prf'
   where
    m : ℕ
    m = pr₁ (pr₁ e f)
    prf' : ∀(α β : Map ℕSpace 𝟚Space) →
           ∀(x : 𝟙) → (A＝⟦M⟧B == ⊤) is-realized-by (((((⋆ , f) , m) , α) , β) , x) →
           pr₁ f α ＝ pr₁ f β
   -- i.e. pr₁ ⟦ F ◦ A ⟧ ((((⋆ , f) , n) , α) , β) ＝ pr₁ ⟦ F ◦ B ⟧ ((((⋆ , f) , n) , α) , β)
    prf' α β ⋆ EM = fan-behaviour f α β em
     where
      ρ : U ⟦ Γ ⟧ᶜ
      ρ = ((((⋆ , f) , m) , α) , β)
      g : ℕ → 𝟚 → 𝟚
      g n b = pr₁ (pr₁ (pr₁ ⟦ LAM (LAM (MIN (EQ (A' ◦ ν₁) (B' ◦ ν₁)) ν₀)) ⟧ᵐ ρ) n) b
      lemma : (k : ℕ) → ℕ-induction ₁ g k ＝ ₁ → pr₁ α ＝⟦ k ⟧ pr₁ β
      lemma 0        refl = ＝⟦zero⟧
      lemma (succ k) esk  = ＝⟦succ⟧ IH claim₁
       where
        ek : ℕ-induction ₁ g k ＝ ₁
        ek = pr₂ (Lemma[min] (eq (pr₁ α k) (pr₁ β k)) (ℕ-induction ₁ g k)  esk)
        IH : pr₁ α ＝⟦ k ⟧ pr₁ β
        IH = lemma k ek
        claim₀ : eq (pr₁ α k) (pr₁ β k) ＝ ₁
        claim₀ = pr₁ (Lemma[min] (eq (pr₁ α k) (pr₁ β k)) (ℕ-induction ₁ g k) esk)
        claim₁ : pr₁ α k ＝ pr₁ β k
        claim₁ = Lemma[eq] (pr₁ α k) (pr₁ β k) claim₀
      em : pr₁ α ＝⟦ m ⟧ pr₁ β
      em = lemma m EM

\end{code}

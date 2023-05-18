Brendan Hart 2019-2020

We define PCF types and terms, substitution as in PLFA, and the big step semantics.

\begin{code}

{-# OPTIONS --without-K --safe --exact-split --no-sized-types --no-guardedness --auto-inline #-}

open import UF.PropTrunc

module PCF.AbstractSyntax (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

open import MLTT.Spartan
open import Naturals.Properties hiding (pred-succ)

data Vec (X : 𝓤₀ ̇) : ℕ → 𝓤₀ ̇ where
  ⟨⟩ : Vec X zero
  _’_ : {n : ℕ} → Vec X n → X → Vec X (succ n)

data Fin : (n : ℕ) → 𝓤₀ ̇ where
  zero : ∀ {n} → Fin (succ n)
  succ : ∀ {n} → Fin n → Fin (succ n)

data type : 𝓤₀ ̇  where
  ι : type
  _⇒_ : type → type → type

Context : ℕ → 𝓤₀ ̇
Context = Vec type

data _∋_ : {n : ℕ} → Context n → type → 𝓤₀ ̇ where
  Z : ∀ {n : ℕ} {Γ : Context n} {σ : type} → (Γ ’ σ) ∋ σ
  S : ∀ {n : ℕ} {Γ : Context n} {σ τ : type}
    → Γ ∋ σ
    → (Γ ’ τ) ∋ σ

lookup : {n : ℕ} → Context n → Fin n → type
lookup (Γ ’ x) zero     = x
lookup (Γ ’ x) (succ n) = lookup Γ n

count : {n : ℕ} {Γ : Context n} → (f : Fin n) → Γ ∋ lookup Γ f
count {.(succ _)} {Γ ’ x} zero     = Z
count {.(succ _)} {Γ ’ x} (succ f) = S (count f)

infixr 1 _⇒_

data PCF : {n : ℕ} (Γ : Context n) (σ : type) → 𝓤₀ ̇ where
  Zero   : {n : ℕ} {Γ : Context n}
           → PCF Γ ι
  Succ   : {n : ℕ} {Γ : Context n}
           → PCF Γ ι
           → PCF Γ ι
  Pred   : {n : ℕ} {Γ : Context n}
           → PCF Γ ι
           → PCF Γ ι
  IfZero : {n : ℕ} {Γ : Context n}
           → PCF Γ ι
           → PCF Γ ι
           → PCF Γ ι
           → PCF Γ ι
  ƛ      : {n : ℕ} {Γ : Context n} {σ τ : type}
           → PCF (Γ ’ σ) τ
           → PCF Γ (σ ⇒ τ)
  _·_    : {n : ℕ} {Γ : Context n} {σ τ : type}
           → PCF Γ (σ ⇒ τ)
           → PCF Γ σ
           → PCF Γ τ
  v      : {n : ℕ} {Γ : Context n} {A : type}
           → Γ ∋ A
           → PCF Γ A
  Fix    : {n : ℕ} {Γ : Context n} {σ : type}
           → PCF Γ (σ ⇒ σ)
           → PCF Γ σ

infixl 1 _·_

ext : ∀ {m n} {Γ : Context m} {Δ : Context n}
      → (∀ {A} → Γ ∋ A → Δ ∋ A)
      → (∀ {σ A} → (Γ ’ σ) ∋ A → (Δ ’ σ) ∋ A)
ext f Z = Z
ext f (S t) = S (f t)

rename : ∀ {m n} {Γ : Context m} {Δ : Context n}
        → (∀ {A} → Γ ∋ A → Δ ∋ A)
        → (∀ {A} → PCF Γ A → PCF Δ A)
rename f Zero = Zero
rename f (Succ t) = Succ (rename f t)
rename f (Pred t) = Pred (rename f t)
rename f (IfZero t t₁ t₂) = IfZero (rename f t) (rename f t₁) (rename f t₂)
rename f (ƛ t) = ƛ (rename (ext f) t)
rename f (t · t₁) = (rename f t) · (rename f t₁)
rename f (v x) = v (f x)
rename f (Fix t) = Fix (rename f t)

exts : ∀ {m n} {Γ : Context m} {Δ : Context n}
     → (∀ {A} → Γ ∋ A → PCF Δ A)
     → (∀ {σ A} → (Γ ’ σ) ∋ A → PCF (Δ ’ σ) A)
exts f Z = v Z
exts f (S t) = rename (_∋_.S) (f t)

subst : ∀ {m n} {Γ : Context m} {Δ : Context n}
      → (∀ {A} → Γ ∋ A → PCF Δ A)
      → (∀ {A} → PCF Γ A → PCF Δ A)
subst f Zero = Zero
subst f (Succ t) = Succ (subst f t)
subst f (Pred t) = Pred (subst f t)
subst f (IfZero t t₁ t₂) = IfZero (subst f t) (subst f t₁) (subst f t₂)
subst f (ƛ t) = ƛ (subst (exts f) t)
subst f (t · t₁) = (subst f t) · (subst f t₁)
subst f (v x) = f x
subst f (Fix t) = Fix (subst f t)

extend-with : {n : ℕ} {m : ℕ} {Γ : Context n} {Δ : Context m}
              {A : type} (N : PCF Δ A)
            → (∀ {A} → Γ ∋ A → PCF Δ A)
            → (∀ {B} → (Γ ’ A) ∋ B → PCF Δ B)
extend-with N f Z = N
extend-with N f (S x) = f x

replace-first : {n : ℕ}
                (A : type)
                (Γ : Context n)
                (N : PCF Γ A)
              → ∀ {B} → (Γ ’ A) ∋ B → PCF Γ B
replace-first A Γ N Z     = N
replace-first A Γ N (S t) = v t

_[_] : {n : ℕ} {Γ : Context n} {σ A : type}
     → PCF (Γ ’ A) σ
     → PCF Γ A
     → PCF Γ σ
_[_] {n} {Γ} {σ} {A} M N = subst (replace-first A Γ N) M


ℕ-to-ι : ∀ {n} {Γ : Context n} → ℕ → PCF Γ ι
ℕ-to-ι zero     = Zero
ℕ-to-ι (succ n) = Succ (ℕ-to-ι n)

peano-axiom-for-PCF : ∀ {n Γ k} → ℕ-to-ι {n} {Γ} zero ≠ ℕ-to-ι (succ k)
peano-axiom-for-PCF ()

data _⇓'_ : ∀ {n : ℕ} {Γ : Context n} {σ : type} → PCF Γ σ → PCF Γ σ → 𝓤₀ ̇ where
  var-id    : {n : ℕ} {Γ : Context n} {A : type}
              {i : Γ ∋ A}
              → (v i) ⇓' (v i)
  ƛ-id      : {n : ℕ} {Γ : Context n} {σ τ : type}
              {t : PCF (Γ ’ σ) τ}
              → ƛ t ⇓' ƛ t
  zero-id   : {n : ℕ} {Γ : Context n}
              → ℕ-to-ι {n} {Γ} zero ⇓' ℕ-to-ι {n} {Γ} zero
  pred-zero : {n : ℕ} {Γ : Context n}
              {M : PCF Γ ι}
              → M ⇓' ℕ-to-ι {n} {Γ} zero
              → Pred M ⇓' ℕ-to-ι {n} {Γ} zero
  pred-succ : {n : ℕ} {Γ : Context n}
              {M : PCF Γ ι}
              {k : ℕ}
              → M ⇓' ℕ-to-ι {n} {Γ} (succ k)
              → Pred M ⇓' ℕ-to-ι {n} {Γ} k
  succ-arg  : {n : ℕ} {Γ : Context n}
              {M : PCF Γ ι}
              {k : ℕ}
              → M ⇓' ℕ-to-ι {n} {Γ} k
              → Succ M ⇓' ℕ-to-ι {n} {Γ} (succ k)
  IfZero-zero    : {n : ℕ} {Γ : Context n}
              {M : PCF Γ ι} {M₁ : PCF Γ ι} {M₂ : PCF Γ ι}
              {V : PCF Γ ι}
              → M ⇓' ℕ-to-ι {n} {Γ} zero
              → M₁ ⇓' V
              → IfZero M M₁ M₂ ⇓' V
  IfZero-succ    : {n : ℕ} {Γ : Context n}
              {M : PCF Γ ι} {M₁ : PCF Γ ι} {M₂ : PCF Γ ι}
              {V : PCF Γ ι}
              {k : ℕ}
              → M ⇓' ℕ-to-ι {n} {Γ} (succ k)
              → M₂ ⇓' V
              → IfZero M M₁ M₂ ⇓' V
  Fix-step  : {n : ℕ} {Γ : Context n} {σ : type} {M : PCF Γ (σ ⇒ σ)} {V : PCF Γ σ}
              → (M · (Fix M)) ⇓' V
              → Fix M ⇓' V
  ·-step    : {n : ℕ} {Γ : Context n} {σ τ : type}
              {M : PCF Γ (σ ⇒ τ)} {E : PCF (Γ ’ σ) τ} {N : PCF Γ σ}
              {V : PCF Γ τ}
              → M ⇓' ƛ E
              → (E [ N ]) ⇓' V
              → (M · N) ⇓' V

_⇓_ : {n : ℕ} {Γ : Context n} {σ : type} → PCF Γ σ → PCF Γ σ → 𝓤₀ ̇
M ⇓ N = ∥ M ⇓' N ∥

data Value : {n : ℕ} {Γ : Context n} {σ : type} → PCF Γ σ → 𝓤₀ ̇ where
  zero-val : {n : ℕ} {Γ : Context n}
             → Value {n} {Γ} Zero
  succ-val : {n : ℕ} {Γ : Context n} {V : PCF Γ ι}
             → Value V
             → Value (Succ V)
  ƛ-val    : {n : ℕ} {Γ : Context n} {σ τ : type} {N : PCF (Γ ’ σ) τ}
             → Value (ƛ N)
  var-val  : {n : ℕ} {Γ : Context n} {σ : type}
             → (i : Γ ∋ σ)
             → Value (v i)

values-dont-reduce-further : {n : ℕ} {Γ : Context n} {σ : type}
                           → (M : PCF Γ σ)
                           → Value M
                           → (N : PCF Γ σ)
                           → M ⇓' N
                           → M ＝ N
values-dont-reduce-further .(v _) x .(v _) var-id = refl
values-dont-reduce-further .(ƛ _) x .(ƛ _) ƛ-id = refl
values-dont-reduce-further .Zero x .Zero zero-id = refl
values-dont-reduce-further .(Succ M) (succ-val x) .(Succ (ℕ-to-ι k))
                            (succ-arg {n} {Γ} {M} {k} r) = ap Succ ih
  where
    ih : M ＝ ℕ-to-ι k
    ih = values-dont-reduce-further M x (ℕ-to-ι k) r

⇓-reduces-to-val : {n : ℕ} {Γ : Context n} {σ : type}
                   (M N : PCF Γ σ)
                 → M ⇓' N
                 → Value N
⇓-reduces-to-val (v i) (v i) var-id = var-val i
⇓-reduces-to-val .(ƛ _) .(ƛ _) ƛ-id = ƛ-val
⇓-reduces-to-val .Zero .Zero zero-id = zero-val
⇓-reduces-to-val (Pred M) .Zero (pred-zero p) = ⇓-reduces-to-val M Zero p
⇓-reduces-to-val (Pred M) (N) (pred-succ {_} {_} {_} {k} p) = lemma IH
 where
  IH : Value (Succ (ℕ-to-ι k))
  IH = ⇓-reduces-to-val M (Succ (ℕ-to-ι k)) p

  lemma : ∀ {n} {Γ} {N} → Value {n} {Γ} (Succ N) → Value N
  lemma (succ-val t) = t
⇓-reduces-to-val (Succ M) (Succ N) (succ-arg p) = succ-val (⇓-reduces-to-val M N p)
⇓-reduces-to-val (IfZero M M₁ M₂) N (IfZero-zero p p₁) = ⇓-reduces-to-val M₁ N p₁
⇓-reduces-to-val (IfZero M M₁ M₂) N (IfZero-succ p p₁) = ⇓-reduces-to-val M₂ N p₁
⇓-reduces-to-val (Fix M) N (Fix-step p) = ⇓-reduces-to-val (M · Fix M) N p
⇓-reduces-to-val (L · R) N (·-step {_} {_} {_} {_} {_} {E} p p₁) =
 ⇓-reduces-to-val (E [ R ]) N p₁

⇓-cant-reduce-further : {n : ℕ} {Γ : Context n} {σ : type}
                      → (M N L : PCF Γ σ)
                      → M ⇓' N
                      → N ⇓' L
                      → N ＝ L
⇓-cant-reduce-further M N L step₁ step₂ = values-dont-reduce-further N (⇓-reduces-to-val M N step₁) L step₂

⇓-deterministic : {n : ℕ} {Γ : Context n} {σ : type}
                → {M N L : PCF Γ σ}
                → M ⇓' N
                → M ⇓' L
                → N ＝ L
⇓-deterministic var-id var-id = refl
⇓-deterministic ƛ-id ƛ-id = refl
⇓-deterministic zero-id zero-id = refl
⇓-deterministic (pred-zero step₁) (pred-zero step₂) = refl
⇓-deterministic (pred-zero step₁) (pred-succ {_} {_} {_} {k} step₂) = 𝟘-elim (peano-axiom-for-PCF IH)
 where
  IH : ℕ-to-ι zero ＝ ℕ-to-ι (succ k)
  IH = ⇓-deterministic step₁ step₂
⇓-deterministic (pred-succ {_} {_} {_} {k} step₁) (pred-zero step₂) = 𝟘-elim (peano-axiom-for-PCF (IH ⁻¹))
 where
  IH : ℕ-to-ι (succ k) ＝ ℕ-to-ι zero
  IH = ⇓-deterministic step₁ step₂
⇓-deterministic (pred-succ step₁) (pred-succ step₂) = succ-removal (⇓-deterministic step₁ step₂)
 where
  succ-removal : ∀ {M N} → Succ M ＝ Succ N → M ＝ N
  succ-removal refl = refl
⇓-deterministic (succ-arg step₁) (succ-arg step₂) = ap Succ (⇓-deterministic step₁ step₂)
⇓-deterministic (IfZero-zero step₁ step₃) (IfZero-zero step₂ step₄) = ⇓-deterministic step₃ step₄
⇓-deterministic (IfZero-zero step₁ step₃) (IfZero-succ {_} {_} {_} {_} {_} {_} {k} step₂ step₄) = 𝟘-elim (peano-axiom-for-PCF ih)
 where
  ih : ℕ-to-ι zero ＝ ℕ-to-ι (succ k)
  ih = ⇓-deterministic step₁ step₂
⇓-deterministic (IfZero-succ {_} {_} {_} {_} {_} {_} {k} step₁ step₃) (IfZero-zero step₂ step₄) = 𝟘-elim (peano-axiom-for-PCF (IH ⁻¹))
 where
  IH : ℕ-to-ι (succ k) ＝ ℕ-to-ι zero
  IH = ⇓-deterministic step₁ step₂
⇓-deterministic (IfZero-succ step₁ step₃) (IfZero-succ step₂ step₄) = ⇓-deterministic step₃ step₄
⇓-deterministic (Fix-step step₁) (Fix-step step₂) = ⇓-deterministic step₁ step₂
⇓-deterministic (·-step {_} {_} {_} {_} {_} {E} {N} {L} step₁ step₃) (·-step {_} {_} {_} {_} {_} {E₁} {N} {L₁} step₂ step₄) = γ
 where
   IH : ƛ E ＝ ƛ E₁
   IH = ⇓-deterministic step₁ step₂

   ƛ-removal-＝ : ∀ {A B} → ƛ A ＝ ƛ B → A ＝ B
   ƛ-removal-＝ refl = refl

   transported-step : (E [ N ]) ⇓' L₁
   transported-step = transport (λ - → (- [ N ]) ⇓' L₁) (ƛ-removal-＝ IH ⁻¹) step₄

   γ : L ＝ L₁
   γ = ⇓-deterministic step₃ transported-step

\end{code}

Chuangjie Xu 2015 (ported to TypeTopology in 2025)

This module develops the basic order theory of the natural numbers needed in
the C-space formalization. It introduces the relations `≤` and `<`, proves a
collection of elementary lemmas about them, and records a few auxiliary
constructions such as maxima and least witnesses.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

module C-Spaces.Preliminaries.Naturals.Order where

open import MLTT.Plus-Properties
open import MLTT.Spartan renaming (_+_ to _⊎_)
open import UF.Subsingletons
open import Naturals.Addition
open import Naturals.Properties

\end{code}

Orders on natural numbers

\begin{code}

infix 30 _≤_
infix 30 _<_
infix 30 _≮_

data _≤_ : ℕ → ℕ → Set where
 ≤-zero : ∀{n : ℕ} → 0 ≤ n
 ≤-succ : ∀{m n : ℕ} → m ≤ n → succ m ≤ succ n

≤-is-prop : {n m : ℕ} → is-prop (n ≤ m)
≤-is-prop  ≤-zero     ≤-zero    = refl
≤-is-prop (≤-succ r) (≤-succ s) = ap ≤-succ (≤-is-prop r s)

_<_ : ℕ → ℕ → Set
m < n = succ m ≤ n

_≮_ : ℕ → ℕ → Set
m ≮ n = ¬ (m < n)

≤-refl : {n : ℕ} → n ≤ n
≤-refl {0}      = ≤-zero
≤-refl {succ n} = ≤-succ ≤-refl

≤-trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤-trans ≤-zero     v          = ≤-zero
≤-trans (≤-succ u) (≤-succ v) = ≤-succ (≤-trans u v)

≤-r-succ : {n m : ℕ} → n ≤ m → n ≤ succ m
≤-r-succ ≤-zero     = ≤-zero
≤-r-succ (≤-succ r) = ≤-succ (≤-r-succ r)

Lemma[n≤n+1] : ∀(n : ℕ) → n ≤ succ n
Lemma[n≤n+1] 0        = ≤-zero
Lemma[n≤n+1] (succ n) = ≤-succ (Lemma[n≤n+1] n)

Lemma[m+1≤n+1→m≤n] : ∀{m n : ℕ} → succ m ≤ succ n → m ≤ n
Lemma[m+1≤n+1→m≤n] (≤-succ r) = r

Lemma[n≤m+1→n≤m+n＝m+1] : {n m : ℕ} → n ≤ succ m → (n ≤ m) ⊎ (n ＝ succ m)
Lemma[n≤m+1→n≤m+n＝m+1] {0}      {m}      r = inl ≤-zero
Lemma[n≤m+1→n≤m+n＝m+1] {succ 0} {0}      r = inr refl
Lemma[n≤m+1→n≤m+n＝m+1] {succ (succ n)} {0} (≤-succ ())
Lemma[n≤m+1→n≤m+n＝m+1] {succ n} {succ m} (≤-succ r) = +functor c₀ c₁ IH
 where
  c₀ : n ≤ m → succ n ≤ succ m
  c₀ = ≤-succ

  c₁ : n ＝ succ m → succ n ＝ succ (succ m)
  c₁ = ap succ

  IH : (n ≤ m) ⊎ (n ＝ succ m)
  IH = Lemma[n≤m+1→n≤m+n＝m+1] {n} {m} r

Lemma[n≰m→m<n] : {n m : ℕ} → ¬(n ≤ m) → m < n
Lemma[n≰m→m<n] {0}      {m}      f = 𝟘-elim (f ≤-zero)
Lemma[n≰m→m<n] {succ n} {0}      f = ≤-succ ≤-zero
Lemma[n≰m→m<n] {succ n} {succ m} f = ≤-succ (Lemma[n≰m→m<n] (f ∘ ≤-succ))

Lemma[m≮n→n≤m] : ∀{m n : ℕ} → m ≮ n → n ≤ m
Lemma[m≮n→n≤m] {m}      {0}      f = ≤-zero
Lemma[m≮n→n≤m] {0}      {succ n} f = 𝟘-elim (f (≤-succ ≤-zero))
Lemma[m≮n→n≤m] {succ m} {succ n} f = ≤-succ (Lemma[m≮n→n≤m] (f ∘ ≤-succ))

Lemma[m≤n∧n≤m→m=n] : ∀{m n : ℕ} → m ≤ n → n ≤ m → m ＝ n
Lemma[m≤n∧n≤m→m=n] {0}      {0}      ≤-zero     ≤-zero      = refl
Lemma[m≤n∧n≤m→m=n] {0}      {succ n} ≤-zero     ()
Lemma[m≤n∧n≤m→m=n] {succ m} {0}      ()         ≤-zero
Lemma[m≤n∧n≤m→m=n] {succ m} {succ n} (≤-succ r) (≤-succ r') = ap succ (Lemma[m≤n∧n≤m→m=n] r r')

Lemma[m<n→m≠n] : ∀{m n : ℕ} → m < n → m ≠ n
Lemma[m<n→m≠n] {0}      {0}      ()
Lemma[m<n→m≠n] {0}      {succ n} r          = λ ()
Lemma[m<n→m≠n] {succ m} {0}      r          = λ ()
Lemma[m<n→m≠n] {succ m} {succ n} (≤-succ r) = λ e → Lemma[m<n→m≠n] r (succ-lc e)

Lemma[a≤a+b] : ∀(a b : ℕ) → a ≤ a + b
Lemma[a≤a+b] a 0 = ≤-refl
Lemma[a≤a+b] a (succ b) = ≤-trans (Lemma[a≤a+b] a b) (Lemma[n≤n+1] (a + b))

Lemma[a≤b→a+c≤b+c] : ∀(a b c : ℕ) → a ≤ b → a + c ≤ b + c
Lemma[a≤b→a+c≤b+c] a b 0        r = r
Lemma[a≤b→a+c≤b+c] a b (succ c) r = ≤-succ (Lemma[a≤b→a+c≤b+c] a b c r)

Lemma[a<b→a+c<b+c] : ∀(a b c : ℕ) → a < b → a + c < b + c
Lemma[a<b→a+c<b+c] a b c r = transport (λ n → n ≤ b + c) (lemma a c) (Lemma[a≤b→a+c≤b+c] (succ a) b c r)
 where
  lemma : ∀(n m : ℕ) → (succ n) + m ＝ succ (n + m)
  lemma n 0 = refl
  lemma n (succ m) = ap succ (lemma n m)

Lemma[n+1+m=n+m+1] : ∀(n m : ℕ) → succ n + m ＝ n + succ m
Lemma[n+1+m=n+m+1] n 0 = refl
Lemma[n+1+m=n+m+1] n (succ m) = ap succ (Lemma[n+1+m=n+m+1] n m)

Lemma[≤-Σ] : ∀(a b : ℕ) → a ≤ b → Σ \(c : ℕ) → a + c ＝ b
Lemma[≤-Σ] 0 b ≤-zero = b , zero-left-neutral b
Lemma[≤-Σ] (succ a) 0 ()
Lemma[≤-Σ] (succ a) (succ b) (≤-succ r) = c , eq
 where
  c : ℕ
  c = pr₁ (Lemma[≤-Σ] a b r)
  eq' : a + c ＝ b
  eq' = pr₂ (Lemma[≤-Σ] a b r)
  eq : succ a + c ＝ succ b
  eq = (Lemma[n+1+m=n+m+1] a c) ∙ (ap succ eq')

CoV-induction : {P : ℕ → Set}
              → (∀ n → (∀ m → m < n → P m) → P n)
              → ∀ n → P n
CoV-induction {P} step n = step n (claim n)
 where
  Q : ℕ → Set
  Q n = ∀ m → succ m ≤ n → P m

  qbase : Q 0
  qbase m ()

  qstep : ∀ n → Q n → Q(succ n)
  qstep n qn m (≤-succ r) = step m (λ k u → qn k (≤-trans u r))

  claim : ∀ n → Q n
  claim = ℕ-induction qbase qstep

\end{code}

Maximum

\begin{code}

max : ℕ → ℕ → ℕ
max 0 m = m
max n 0 = n
max (succ n) (succ m) = succ (max n m)

max-spec₀ : (n m : ℕ) → n ≤ max n m
max-spec₀ 0        m        = ≤-zero
max-spec₀ (succ n) 0        = ≤-refl
max-spec₀ (succ n) (succ m) = ≤-succ (max-spec₀ n m)

max-spec₁ : (n m : ℕ) → m ≤ max n m
max-spec₁ 0        m        = ≤-refl
max-spec₁ (succ n) 0        = ≤-zero
max-spec₁ (succ n) (succ m) = ≤-succ (max-spec₁ n m)

\end{code}

The type of "there exists a least number n such that P n"

\begin{code}

Σ-min : (ℕ → Set) → Set
Σ-min P = Σ \(n : ℕ) → (P n) × (∀(n' : ℕ) → P n' → n ≤ n')

re-pair : {P : ℕ → Set} → Σ-min P → Σ P
re-pair (n , p , _) = (n , p)

Σ-min-＝ : {P : ℕ → Set}{w₀ w₁ : Σ-min P} → w₀ ＝ w₁ → re-pair w₀ ＝ re-pair w₁
Σ-min-＝ refl = refl

\end{code}

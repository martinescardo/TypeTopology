Chuangjie Xu, 2015

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-} --

module ContinuityAxiom.Preliminaries where

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import UF.Subsingletons

\end{code}

Less-than relation.

\begin{code}

infix 30 _≤_
infix 30 _<_

data _≤_ : ℕ → ℕ → Set where
 ≤-zero : ∀{n : ℕ} → 0 ≤ n
 ≤-succ : ∀{m n : ℕ} → m ≤ n → succ m ≤ succ n

≤-is-prop : {n m : ℕ} → is-prop (n ≤ m)
≤-is-prop  ≤-zero     ≤-zero    = refl
≤-is-prop (≤-succ r) (≤-succ s) = ap ≤-succ (≤-is-prop r s)

_<_ : ℕ → ℕ → Set
m < n = succ m ≤ n

≤-refl : {n : ℕ} → n ≤ n
≤-refl {0}      = ≤-zero
≤-refl {succ n} = ≤-succ ≤-refl

≤-trans : {a b c : ℕ} → a ≤ b → b ≤ c → a ≤ c
≤-trans ≤-zero     v          = ≤-zero
≤-trans (≤-succ u) (≤-succ v) = ≤-succ (≤-trans u v)

≤-r-succ : {n m : ℕ} → n ≤ m → n ≤ succ m
≤-r-succ ≤-zero     = ≤-zero
≤-r-succ (≤-succ r) = ≤-succ (≤-r-succ r)

is-zero : ℕ → Set
is-zero 0        = 𝟙
is-zero (succ n) = 𝟘

is-zero-monotonicity : (m n : ℕ) → m ≤ n → is-zero n → is-zero m
is-zero-monotonicity m n ≤-zero     q = ⋆
is-zero-monotonicity m n (≤-succ r) q = 𝟘-elim q

successors-are-not-below-zero : (m : ℕ) → ¬ (succ m ≤ 0)
successors-are-not-below-zero m p = is-zero-monotonicity (succ m) 0 p ⋆

Lemma[n≤m+1→n≤m+n＝m+1] : {n m : ℕ} → n ≤ succ m → (n ≤ m) + (n ＝ succ m)
Lemma[n≤m+1→n≤m+n＝m+1] {0}      {m}      r = inl ≤-zero
Lemma[n≤m+1→n≤m+n＝m+1] {succ 0} {0}      r = inr refl
Lemma[n≤m+1→n≤m+n＝m+1] {succ (succ n)} {0} (≤-succ r) =
 𝟘-elim (successors-are-not-below-zero n r)
Lemma[n≤m+1→n≤m+n＝m+1] {succ n} {succ m} (≤-succ r) = +functor c₀ c₁ IH
 where
  c₀ : n ≤ m → succ n ≤ succ m
  c₀ = ≤-succ

  c₁ : n ＝ succ m → succ n ＝ succ (succ m)
  c₁ = ap succ

  IH : (n ≤ m) + (n ＝ succ m)
  IH = Lemma[n≤m+1→n≤m+n＝m+1] {n} {m} r

Lemma[n≰m→m<n] : {n m : ℕ} → ¬(n ≤ m) → m < n
Lemma[n≰m→m<n] {0}      {m}      f = 𝟘-elim (f ≤-zero)
Lemma[n≰m→m<n] {succ n} {0}      f = ≤-succ ≤-zero
Lemma[n≰m→m<n] {succ n} {succ m} f = ≤-succ (Lemma[n≰m→m<n] (f ∘ ≤-succ))

Lemma[m≤n∧n≤m→m=n] : ∀{m n : ℕ} → m ≤ n → n ≤ m → m ＝ n
Lemma[m≤n∧n≤m→m=n] {0}      {0}      ≤-zero     ≤-zero      = refl
Lemma[m≤n∧n≤m→m=n] {0}      {succ n} ≤-zero     r =
 𝟘-elim (successors-are-not-below-zero n r)
Lemma[m≤n∧n≤m→m=n] {succ m} {0}      r          ≤-zero =
 𝟘-elim (successors-are-not-below-zero m r)
Lemma[m≤n∧n≤m→m=n] {succ m} {succ n} (≤-succ r) (≤-succ r') = ap succ (Lemma[m≤n∧n≤m→m=n] r r')

CoV-induction : {P : ℕ → Set}
              → (∀ n → (∀ m → m < n → P m) → P n)
              → ∀ n → P n
CoV-induction {P} step n = step n (claim n)
 where
  Q : ℕ → Set
  Q n = ∀ m → succ m ≤ n → P m

  qbase : Q 0
  qbase m r = 𝟘-elim (successors-are-not-below-zero m r)

  qstep : ∀ n → Q n → Q(succ n)
  qstep n qn m (≤-succ r) = step m (λ k u → qn k (≤-trans u r))

  claim : ∀ n → Q n
  claim = ℕ-induction qbase qstep

\end{code}

Binary sequences

\begin{code}

₂ℕ : Type
₂ℕ = ℕ → 𝟚

0̄ : ₂ℕ
0̄ i = ₀
1̄ : ₂ℕ
1̄ i = ₁

infixr 50 _∷_

data ₂Fin : ℕ → Set where
 ⟨⟩ : ₂Fin 0
 _∷_ : {n : ℕ} → 𝟚 → ₂Fin n → ₂Fin (succ n)

take : (m : ℕ) → ₂ℕ → ₂Fin m
take 0 α = ⟨⟩
take (succ n) α = α 0 ∷ take n (α ∘ succ)

drop : ℕ → ₂ℕ → ₂ℕ
drop 0 α = α
drop (succ m) α = drop m (α ∘ succ)

cons : {m : ℕ} → ₂Fin m → ₂ℕ → ₂ℕ
cons ⟨⟩      α          = α
cons (h ∷ _) α 0        = h
cons (_ ∷ t) α (succ i) = cons t α i

Lemma[₂Fin-decidability] : (n : ℕ) → (Y : ₂Fin n → Set)
                         → (∀ s → is-decidable (Y s)) → is-decidable (∀ s → Y s)
Lemma[₂Fin-decidability] 0 Y decY = +functor c₀ c₁ (decY ⟨⟩)
 where
  c₀ : Y ⟨⟩ → ∀ s → Y s
  c₀ y ⟨⟩ = y

  c₁ : ¬ (Y ⟨⟩) → ¬ (∀ s → Y s)
  c₁ f g = f (g ⟨⟩)
Lemma[₂Fin-decidability] (succ n) Y decY = cases c₀ c₁ IH₀
 where
  Y₀ : ₂Fin n → Set
  Y₀ s = Y (₀ ∷ s)

  decY₀ : ∀ s → is-decidable (Y₀ s)
  decY₀ s = decY (₀ ∷ s)

  IH₀ : is-decidable (∀ s → Y₀ s)
  IH₀ = Lemma[₂Fin-decidability] n Y₀ decY₀

  Y₁ : ₂Fin n → Set
  Y₁ s = Y (₁ ∷ s)

  decY₁ : ∀ s → is-decidable (Y₁ s)
  decY₁ s = decY (₁ ∷ s)

  IH₁ : is-decidable (∀ s → Y₁ s)
  IH₁ = Lemma[₂Fin-decidability] n Y₁ decY₁

  c₀ : (∀ s → Y₀ s) → is-decidable (∀ s → Y s)
  c₀ y₀ = +functor sc₀ sc₁ IH₁
   where
    sc₀ : (∀ s → Y₁ s) → ∀ s → Y s
    sc₀ y₁ (₀ ∷ s) = y₀ s
    sc₀ y₁ (₁ ∷ s) = y₁ s

    sc₁ : ¬ (∀ s → Y₁ s) → ¬ (∀ s → Y s)
    sc₁ f₁ ys = f₁ (λ s → ys (₁ ∷ s))
  c₁ : ¬ (∀ s → Y₀ s) → is-decidable (∀ s → Y s)
  c₁ f₀ = inr (λ ys → f₀ (λ s → ys (₀ ∷ s)))

\end{code}

"Agree with" relation over infinite sequences, which is an equivalence
relation and a deciable type:

\begin{code}

infixl 10 _＝⟦_⟧_

data _＝⟦_⟧_ {X : Type} : (ℕ → X) → ℕ → (ℕ → X) → Set where
 ＝⟦zero⟧ : {α β : ℕ → X} → α ＝⟦ 0 ⟧ β
 ＝⟦succ⟧ : {α β : ℕ → X}{n : ℕ} → α ＝⟦ n ⟧ β → α n ＝ β n → α ＝⟦ succ n ⟧ β

＝⟦⟧-sym : {n : ℕ}{α β : ₂ℕ} → α ＝⟦ n ⟧ β → β ＝⟦ n ⟧ α
＝⟦⟧-sym {0}      ＝⟦zero⟧        = ＝⟦zero⟧
＝⟦⟧-sym {succ n} (＝⟦succ⟧ en e) = ＝⟦succ⟧ (＝⟦⟧-sym en) (e ⁻¹)

＝⟦⟧-trans : {n : ℕ}{α₀ α₁ α𝟚 : ₂ℕ} → α₀ ＝⟦ n ⟧ α₁ → α₁ ＝⟦ n ⟧ α𝟚 → α₀ ＝⟦ n ⟧ α𝟚
＝⟦⟧-trans {0}      ＝⟦zero⟧        ＝⟦zero⟧          = ＝⟦zero⟧
＝⟦⟧-trans {succ n} (＝⟦succ⟧ en e) (＝⟦succ⟧ en' e') = ＝⟦succ⟧ (＝⟦⟧-trans en en') (e ∙ e')

Lemma[＝⟦]-cons-take] : {α β : ₂ℕ} → ∀(n : ℕ) → α ＝⟦ n ⟧ cons (take n α) β
Lemma[＝⟦]-cons-take] {α} {β} n = lemma₁ n n ≤-refl
 where
  lemma₀ : ∀(α β : ₂ℕ)(m k : ℕ) → succ m ≤ k → α m ＝ cons (take k α) β m
  lemma₀ α β m        0        r = 𝟘-elim (successors-are-not-below-zero m r)
  lemma₀ α β 0        (succ k) r          = refl
  lemma₀ α β (succ m) (succ k) (≤-succ r) = lemma₀ (α ∘ succ) β m k r
  lemma₁ : ∀(m k : ℕ) → m ≤ k → α ＝⟦ m ⟧ cons (take k α) β
  lemma₁ 0        k        ≤-zero     = ＝⟦zero⟧
  lemma₁ (succ m) 0        r = 𝟘-elim (successors-are-not-below-zero m r)
  lemma₁ (succ m) (succ k) (≤-succ r) = ＝⟦succ⟧ (lemma₁ m (succ k) (≤-r-succ r))
                                                (lemma₀ α β m (succ k) (≤-succ r))

Lemma[＝⟦]-＝⟦]-take] : {α β γ : ₂ℕ} → ∀(n : ℕ) → α ＝⟦ n ⟧ β → β ＝⟦ n ⟧ cons (take n α) γ
Lemma[＝⟦]-＝⟦]-take] n en = ＝⟦⟧-trans (＝⟦⟧-sym en) (Lemma[＝⟦]-cons-take] n)

Lemma[cons-take-0] : {α β : ₂ℕ} → ∀(n : ℕ) → β 0 ＝ cons (take n α) β n
Lemma[cons-take-0]  0       = refl
Lemma[cons-take-0] (succ n) = Lemma[cons-take-0] n

Lemma[cons-＝⟦]-≤] : {n m : ℕ}{α β : ₂ℕ} → (s : ₂Fin n) → m ≤ n → cons s α ＝⟦ m ⟧ cons s β
Lemma[cons-＝⟦]-≤] _ ≤-zero     = ＝⟦zero⟧
Lemma[cons-＝⟦]-≤] s (≤-succ r) = ＝⟦succ⟧ (Lemma[cons-＝⟦]-≤] s (≤-r-succ r)) (lemma s r)
 where
  lemma : {n m : ℕ}{α β : ₂ℕ} → (s : ₂Fin (succ n)) → m ≤ n → cons s α m ＝ cons s β m
  lemma (b ∷ s) ≤-zero     = refl
  lemma (b ∷ s) (≤-succ r) = lemma s r

\end{code}

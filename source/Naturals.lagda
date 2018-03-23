Martin Escardo 2011.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Naturals where

open import SpartanMLTT
open import DiscreteAndSeparated

data ℕ : Set where 
  zero : ℕ              
  succ : ℕ → ℕ       

{-# BUILTIN NATURAL ℕ #-}

rec : ∀ {U} {X : U ̇} → X → (X → X) → (ℕ → X)
rec x f zero = x
rec x f (succ n) = f(rec x f n)

induction : ∀ {U} {A : ℕ → U ̇} → A 0 → ((k : ℕ) → A k → A(succ k)) → (n : ℕ) → A n 
induction base step 0 = base
induction base step (succ n) = step n (induction base step n)

a-peano-axiom : {n : ℕ} → succ n ≢ 0
a-peano-axiom ()

pred : ℕ → ℕ
pred 0 = 0
pred (succ n) = n

succ-injective : {i j : ℕ} → succ i ≡ succ j → i ≡ j
succ-injective = ap pred

ℕ-discrete : discrete ℕ 
ℕ-discrete 0 0 = inl refl 
ℕ-discrete 0 (succ n) = inr (λ())
ℕ-discrete (succ m) 0 = inr (λ())
ℕ-discrete (succ m) (succ n) =  step(ℕ-discrete m n)
  where 
   step : (m ≡ n) + (m ≢ n) → (succ m ≡ succ n) + (succ m ≢ succ n) 
   step (inl r) = inl(ap succ r)
   step (inr f) = inr(λ s → f(succ-injective s)) 

open import Two
open import DecidableAndDetachable

≡-indicator :  (m : ℕ) → Σ \(p : ℕ → 𝟚) → (n : ℕ) → (p n ≡ ₀ → m ≢ n) × (p n ≡ ₁ → m ≡ n)
≡-indicator m = co-characteristic-function (ℕ-discrete m)

χ≡ : ℕ → ℕ → 𝟚
χ≡ m = pr₁ (≡-indicator m)

χ≡-spec : (m n : ℕ) → (χ≡ m n ≡ ₀ → m ≢ n) × (χ≡ m n ≡ ₁ → m ≡ n)
χ≡-spec m = pr₂ (≡-indicator m)

_≡[ℕ]_ : ℕ → ℕ → U₀ ̇
m ≡[ℕ] n = (χ≡ m n) ≡ ₁

infix  30 _≡[ℕ]_

≡-agrees-with-≡[ℕ] : (m n : ℕ) → m ≡ n ⇔ m ≡[ℕ] n
≡-agrees-with-≡[ℕ] m n = (λ r → Lemma[b≢₀→b≡₁] (λ s → pr₁(χ≡-spec m n) s r)) , pr₂(χ≡-spec m n)

≢-indicator :  (m : ℕ) → Σ \(p : ℕ → 𝟚) → (n : ℕ) → (p n ≡ ₀ → m ≡ n) × (p n ≡ ₁ → m ≢ n)
≢-indicator m = indicator(ℕ-discrete m)

χ≢ : ℕ → ℕ → 𝟚
χ≢ m = pr₁ (≢-indicator m)

χ≢-spec : (m n : ℕ) → (χ≢ m n ≡ ₀ → m ≡ n) × (χ≢ m n ≡ ₁ → m ≢ n)
χ≢-spec m = pr₂ (≢-indicator m)

_≠_ : ℕ → ℕ → U₀ ̇
m ≠ n = (χ≢ m n) ≡ ₁

infix  30 _≠_

≠-agrees-with-≢ : (m n : ℕ) → m ≠ n ⇔ m ≢ n
≠-agrees-with-≢ m n = pr₂(χ≢-spec m n) , (λ d → Lemma[b≢₀→b≡₁] (contrapositive(pr₁(χ≢-spec m n)) d))

\end{code}

Sometimes the following injection is useful:

\begin{code}

open import Two

number : 𝟚 → ℕ
number ₀ = 0
number ₁ = 1

\end{code}

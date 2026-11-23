Andrew Sneap, 2023.

\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import MLTT.Spartan renaming (_^_ to _^^_ ; _+_ to _∔_)
open import Naturals.Addition
open import Naturals.Properties
open import Naturals.Multiplication
open import UF.Base

module Naturals.Exponentiation where

_^_ : ℕ → ℕ → ℕ
a ^ b = ((a *_) ^^ b) 1

infixl 33 _^_

2^ : ℕ → ℕ
2^ = 2 ^_

zero-base : (a : ℕ) → a ^ 0 ＝ 1
zero-base a = refl

prod-of-powers : (n a b : ℕ) → (n ^ a) * (n ^ b) ＝ n ^ (a + b)
prod-of-powers n a 0        = refl
prod-of-powers n a (succ b) = I
 where
  I : (n ^ a) * (n ^ succ b) ＝ (n ^ (a + succ b))
  I = (n ^ a) * (n ^ succ b)  ＝⟨refl⟩
      (n ^ a) * (n * (n ^ b)) ＝⟨ i    ⟩
      (n ^ a) * n * (n ^ b)   ＝⟨ ii   ⟩
      n * n ^ a * n ^ b       ＝⟨ iii  ⟩
      n * (n ^ a * n ^ b)     ＝⟨ iv   ⟩
      n ^ (a + succ b)         ∎
   where
    i   = mult-associativity (n ^ a) n (n ^ b) ⁻¹
    ii  = ap (_* (n ^ b)) (mult-commutativity (n ^ a) n)
    iii = mult-associativity n (n ^ a) (n ^ b)
    iv  = ap (n *_) (prod-of-powers n a b)

power-of-power : (n a b : ℕ) → (n ^ a) ^ b ＝ n ^ (a * b)
power-of-power n a 0        = refl
power-of-power n a (succ b) = I
 where
  IH : n ^ a ^ b ＝ n ^ (a * b)
  IH = power-of-power n a b
  I : n ^ a ^ succ b ＝ n ^ (a * succ b)
  I = n ^ a ^ succ b       ＝⟨ refl                       ⟩
      n ^ a * (n ^ a) ^ b ＝⟨ ap (n ^ a *_) IH          ⟩
      n ^ a * n ^ (a * b)  ＝⟨ prod-of-powers n a (a * b) ⟩
      n ^ (a + a * b)       ＝⟨ refl                       ⟩
      n ^ (a * succ b)      ∎

exponents-not-zero : (n : ℕ) → ¬ (2^ n ＝ 0)
exponents-not-zero 0        e = positive-not-zero 0 e
exponents-not-zero (succ n) e = exponents-not-zero n I
 where
  I : 2^ n ＝ 0
  I = mult-left-cancellable (2^ n) 0 1 e

\end{code}

Added 11 October 2025 by Fredrik Nordvall Forsberg.

\begin{code}

open import Naturals.Order
open import Notation.Order

exponential-positive-if-base-positive : (n m : ℕ) → 0 < n → 0 < n ^ m
exponential-positive-if-base-positive n zero _ = ⋆
exponential-positive-if-base-positive zero (succ m) l = 𝟘-elim l
exponential-positive-if-base-positive n@(succ n') (succ m) l = II
 where
  IH : 0 < (n ^ m)
  IH = exponential-positive-if-base-positive n m l

  I : 0 < (n ^ m) * n
  I = less-than-pos-mult 0 (n ^ m) n' IH

  II : 0 < n * (n ^ m)
  II = transport (0 <_) (mult-commutativity (n ^ m) n) I

exponent-smaller-than-exponential-for-base-at-least-two : (n k : ℕ)
                                                        → 2 ≤ k
                                                        → n ≤ (k ^ n)
exponent-smaller-than-exponential-for-base-at-least-two zero k _ = ⋆
exponent-smaller-than-exponential-for-base-at-least-two
 (succ n) zero        l = 𝟘-elim l
exponent-smaller-than-exponential-for-base-at-least-two
 (succ n) (succ zero) l = 𝟘-elim l
exponent-smaller-than-exponential-for-base-at-least-two
 (succ n) k@(succ (succ k')) l = ≤-<-trans n (1 * k ^ n) (k * (k ^ n)) I III
  where
   IH : n ≤ (k ^ n)
   IH = exponent-smaller-than-exponential-for-base-at-least-two n k l

   I : n ≤ 1 * k ^ n
   I = transport⁻¹ (n ≤_) (mult-left-id (k ^ n)) IH

   II : 0 < k ^ n
   II = exponential-positive-if-base-positive k n ⋆

   III : 1 * (k ^ n) < k * (k ^ n)
   III = multiplication-preserves-strict-order' 1 k (k ^ n) ⋆ II

\end{code}

Added by Theo Hepburn on 21 November 2026.

Exponentiation distributes over multiplication.

In the base case, we have on the left hand side:

(n * m) ^ 0 = 1

and on the right hand side:

(n ^ 0) * (m ^ 0) = 1 * 1
                  = 1

For the inductive step, we have on the left hand side:

(n * m) ^ (k + 1) = n * m * (n * m) ^ k
                  = n * m * (n ^ k) * (m ^ k) (by the inductive hypothesis)
                  = (n * n ^ k) * (m * m ^ k)
                  = (n * (k + 1)) + (m * (k + 1))

\begin{code}

^-over-* : (n m k : ℕ) → (n * m) ^ k  ＝ (n ^ k) * (m ^ k)
^-over-* n m zero = refl
^-over-* n m (succ k) =
 n * m * (n * m) ^ k       ＝⟨ I ⟩
 (n * m) * (n ^ k * m ^ k) ＝⟨ II ⟩
 n * (m * (n ^ k * m ^ k)) ＝⟨ III ⟩
 n * ((m * n ^ k) * m ^ k) ＝⟨ IV ⟩
 n * (m * n ^ k) * m ^ k   ＝⟨ V ⟩
 n * (n ^ k * m) * m ^ k   ＝⟨ VI ⟩
 (n * n ^ k) * m * m ^ k   ＝⟨ VII ⟩
 n * n ^ k * (m * m ^ k) ∎
  where
   I = ap (λ z → n * m * z) ((^-over-* n m k))

   II = mult-associativity n m (n ^ k * m ^ k)

   III = ap (λ z → n * z) (mult-associativity m (n ^ k) (m ^ k) ⁻¹) 

   IV = mult-associativity n (m * n ^ k) (m ^ k) ⁻¹

   V = ap (λ z → n * z * m ^ k) (mult-commutativity m (n ^ k))

   VI = ap (λ z → z * m ^ k) (mult-associativity n (n ^ k) m ⁻¹)

   VII = mult-associativity (n * n ^ k) m (m ^ k)

\end{code}

Proofs regarding exponentation and ordering

We prove that 1ᵏ ＝ 1 for all k.

In the base case, we have 1 ^ 0 on the left hand side, which is just 1.

For the inductive step, we have on the left hand side:

1 * (1 ^ 0) = 1 * 1 (by the inductive hypothesis)
            = 1

\begin{code}

exponentiation-of-one : (k : ℕ) → 1 ^ k ＝ 1
exponentiation-of-one zero = refl
exponentiation-of-one (succ k)
 = 1 * (1 ^ k) ＝⟨ ap (λ x → 1 * x) (exponentiation-of-one k) ⟩
   1 * 1       ＝⟨ refl ⟩
   1 ∎

\end{code}

We prove that 0ᵏ ＝ 0 for all k > 0.

Let k = k' + 1

We do this by showing that, for any k' ≥ 0,
0 ^ (k' + 1) = 0 * (0 ^ k') = 0 by `zero-left-base`.

\begin{code}

exponentiation-of-zero : (k : ℕ) → k > 0 → 0 ^ k ＝ 0
exponentiation-of-zero zero ()
exponentiation-of-zero (succ k) k>0 = zero-left-base (0 ^ k)

\end{code}

We prove that if k > 0, k ^ n ≤ k ^ (n + 1)

If k = 0, this is invalid.

Otherwise:

k ^ n' ＝ 1 * (k ^ n') by `mult-left-id`
       ≤  k * (k ^ n') by `multiplication-preserves-order`, as 1 ≤ k
       ＝ k ^ (n' + 1)

\begin{code}

exponentiation-succ-≤ : (k n : ℕ) → k > 0 → k ^ n ≤ k ^ (succ n)
exponentiation-succ-≤ zero n ()
exponentiation-succ-≤ k@(succ _) n k>0 = transport (_≤ k * k ^ n) γ₁ γ₂
 where
  γ₁ : 1 * (k ^ n) ＝ k ^ n
  γ₁ = (mult-left-id (k ^ n))

  γ₂ : 1 * (k ^ n) ≤ k * (k ^ n)
  γ₂ = multiplication-preserves-order 1 k (k ^ n) ⋆

\end{code}

We prove that if m ≤ n, we have m ^ k ≤ n ^ k for any k.

For the base case k = 0, we have m ^ 0 ＝ 1 by definition on the left hand side,
and n ^ 0 ＝ 1 by definition on the right hand side.

For the inductive hypothesis, let k = k' + 1

On the left hand side, we have m ^ (k + 1) ＝ m * m ^ k

On the right hand side, we have n ^ (k + 1) ＝ n * n ^ k

Since we have m ≤ n and m ^ k ≤ n ^ k by the inductive hypothesis, by
`≤-multiplying` we prove that m * m ^ k ≤ n * n ^ k.

\begin{code}

exponentiation-preserves-order-right : (m n k : ℕ) → m ≤ n → (m ^ k) ≤ (n ^ k)
exponentiation-preserves-order-right m n 0 l = ⋆
exponentiation-preserves-order-right m n (succ k) l
 = ≤-multiplying m n (m ^ k) (n ^ k) l γ
 where
  γ : (m ^ k) ≤ (n ^ k)
  γ = exponentiation-preserves-order-right m n k l

\end{code}

We then prove that if m ≤ n, then kᵐ ≤ kⁿ if k ≠ 0, m ≠ 0 or n ＝ 0.

\begin{code}

exponentiation-preserves-order-left : (k m n : ℕ)
                                    → (k ≠ 0) ∔ (m ≠ 0) ∔ (n ＝ 0)
                                    → m ≤ n
                                    → (k ^ m) ≤ (k ^ n)

\end{code}

We first rule out invalid cases.

\begin{code}

exponentiation-preserves-order-left zero m n (inl k≠0) l
 = 𝟘-elim (k≠0 refl)
exponentiation-preserves-order-left zero zero n (inr (inl m≠0)) l
 = 𝟘-elim (m≠0 refl)
exponentiation-preserves-order-left zero zero (succ n) (inr (inr ())) _
exponentiation-preserves-order-left zero (succ m) zero (inr y) ()
exponentiation-preserves-order-left zero (succ m) (succ n) (inr (inr ())) y
exponentiation-preserves-order-left (succ k) (succ m) zero x ()

\end{code}

Holds when n = 0 and k = 0. m must equal 0 here as m ≤ 0.

On the left hand side we have 0 ^ 0 ＝ 1 and on the right hand side we have
0 ^ 0 ＝ 1. 1 ≤ 1 so this case holds.

\begin{code}

exponentiation-preserves-order-left zero zero zero (inr (inr n＝0)) l = ⋆

\end{code}

Holds when k ≠ 0, m ＝ 0, and n ＝ 0. m must equal 0 here as m ≤ 0.

Both sides are 0 ^ k, and 0 ^ k ≤ 0 ^ k.

\begin{code}

exponentiation-preserves-order-left k@(succ _) zero zero _ l = ⋆

\end{code}

Holds when k ＝ 0, m ≠ 0, and n ≠ 0.

When k ＝ 0, we have 0 ^ m on the left hand side, which
by `exponentiation-of-zero` equals 0, as m ≥ 0.

When k ＝ 0, we have 0 ^ n on the right hand side, which
by `exponentiation-of-zero` equals 0, as n ≥ 0.

So we have 0 on both sides, and 0 ≤ 0 and ≤-refl.

\begin{code}

exponentiation-preserves-order-left zero (succ m) (succ n) (inr (inl m≠0)) l
 = transport₂ _≤_ γ₁ γ₂ γ₃ 
 where
  γ₁ : 0 ＝ 0 ^ succ m
  γ₁ = (exponentiation-of-zero (succ m) ⋆)⁻¹ 

  γ₂ : 0 ＝ 0 ^ succ n
  γ₂ = (exponentiation-of-zero (succ n) ⋆)⁻¹

  γ₃ : 0 ≤ 0
  γ₃ = ≤-refl 0

\end{code}

Holds when k ≠ 0, m = 0, and n ≠ 0

Let n = n' + 1.

On the left hand side, we have k ^ m ＝ 1 by definition.

We have 1 ≤ k ^ n' by the inductive hypothesis.

and k ^ n' ≤ (k ^ (n' + 1)) by `exponentiation-succ-≤` since k > 0 because k ≠ 0

So k ^ m ≤ (k ^ (n' + 1)) by transitivity.

\begin{code}

exponentiation-preserves-order-left k@(succ _) zero (succ n) _ k≠0
 = ≤-trans 1 (k ^ n) (k ^ succ n) γ (exponentiation-succ-≤ k n k≠0)
 where
  γ : 1 ≤ (k ^ n)
  γ = exponentiation-preserves-order-left k zero n (inl (λ ())) k≠0

\end{code}

Holds when k ≠ 0, m ≠ 0, and n ≠ 0

m = m' + 1, and n = n' + 1.

On the left hand side, we have k ^ (m' + 1) ＝ k * k ^ m'.

On the right hand side, we have k ^ (n' + 1) ­＝ k * k ^ n'.

By the inductive hypothesis, we have k ^ m' ≤ k ^ n'.

So by `multiplication-preserves-order-left`, we have k * k ^ m' ≤ k * k ^ n'.

\begin{code}

exponentiation-preserves-order-left k@(succ _) (succ m) (succ n) _ l = γ₂
 where
  γ₁ : k ^ m ≤ k ^ n
  γ₁ = exponentiation-preserves-order-left k m n (inl (λ ())) l

  γ₂ : (k * k ^ m) ≤ (k * k ^ n)
  γ₂ = multiplication-preserves-order-left k (k ^ m) (k ^ n) γ₁

\end{code}

We then show that if we have m ≤ n and x ≤ y, we have m ^ x ≤ n ^ y,
when m ≠ 0, x ≠ 0, or y ＝ 0.

This holds as (m ^ x) ≤ (m ^ y) by `exponentiation-preserves-order-left`,
and (m ^ y) ≤ (n ^ y) by `exponentiation-preserves-order-right`, and so by
transitivity we have m ^ x ≤ n ^ y.

\begin{code}

≤-exponentiating : (m n x y : ℕ)
                 → (m ≠ 0) ∔ (x ≠ 0) ∔ (y ＝ 0)
                 → m ≤ n → x ≤ y
                 → m ^ x ≤ n ^ y
≤-exponentiating m n x y (inl m≠0) l₁ l₂
 = ≤-trans (m ^ x) (m ^ y) (n ^ y) γ₁ γ₂
 where
  γ₁ : (m ^ x) ≤ (m ^ y)
  γ₁ = exponentiation-preserves-order-left m x y (inl m≠0) l₂

  γ₂ : (m ^ y) ≤ (n ^ y)
  γ₂ = exponentiation-preserves-order-right m n y l₁
≤-exponentiating m n x y (inr (inl x≠0)) l₁ l₂
 = ≤-trans (m ^ x) (m ^ y) (n ^ y) γ₁ γ₂
 where
  γ₁ : (m ^ x) ≤ (m ^ y)
  γ₁ = exponentiation-preserves-order-left m x y (inr (inl x≠0)) l₂

  γ₂ : (m ^ y) ≤ (n ^ y)
  γ₂ = exponentiation-preserves-order-right m n y l₁

\end{code}

Invalid cases are ruled out.

\begin{code}

≤-exponentiating m n zero zero (inr (inr y＝0)) l₁ l₂ = ⋆
≤-exponentiating m n (succ _) zero (inr (inr _)) _ ()
≤-exponentiating m n zero (succ _) (inr (inr ())) _ _
≤-exponentiating m n (succ _) (succ _) (inr (inr ())) _ _

\end{code}

We show that if we have x ≤ y and m ≠ 0, x ≠ 0, or y ＝ 0, we have
a * (n ^ x) + b * (n ^ y) ≤ (a + b) * (n ^ y)
for any natural numbers a and b.

This allows us to impose an upper bound of a monomial on a binomial
when we can show that one exponent is ≤ another.

Since we have x ≤ y and the m ≠ 0, x ≠ 0, or y ＝ 0 trichotomy, we
have that n ^ x ≤ n ^ y by `exponentiation-preserves-order-left`.

We then use `absorb-≤-variable` to prove the full result.

\begin{code}

exponent-addition : (a b x y n : ℕ)
                  → (n ≠ 0) ∔ (x ≠ 0) ∔ (y ＝ 0)
                  → x ≤ y
                  → a * (n ^ x) + b * (n ^ y) ≤ (a + b) * (n ^ y)
exponent-addition a b x y n trich x≤y
 = absorb-≤-variable a b (n ^ x) (n ^ y) γ
  where
   γ : n ^ x ≤ n ^ y
   γ = exponentiation-preserves-order-left n x y trich x≤y

\end{code}

End of addition
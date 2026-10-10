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

Theo Hepburn, started February 2025

Contains a proof that exponentiation distributes over
multiplication.

\begin{code}

^-over-* : (n m k : ℕ) → (n * m) ^ k  ＝ (n ^ k) * (m ^ k)
^-over-* n m zero = refl
^-over-* n m (succ k)
 = n * m * (n * m) ^ k ＝⟨ ap (λ z → n * m * z) ((^-over-* n m k)) ⟩
   (n * m) * (n ^ k * m ^ k) ＝⟨ mult-associativity n m (n ^ k * m ^ k) ⟩
   n * (m * (n ^ k * m ^ k)) ＝⟨ ap (λ z → n * z)
                                 (mult-associativity m (n ^ k) (m ^ k) ⁻¹) ⟩
   n * ((m * n ^ k) * m ^ k) ＝⟨ mult-associativity n
                                  (m * n ^ k) (m ^ k) ⁻¹ ⟩
   n * (m * n ^ k) * m ^ k ＝⟨ ap (λ z → n * z * m ^ k)
                                 (mult-commutativity m (n ^ k)) ⟩
   n * (n ^ k * m) * m ^ k ＝⟨ ap (λ z → z * m ^ k)
                                 (mult-associativity n (n ^ k) m ⁻¹) ⟩
   (n * n ^ k) * m * m ^ k ＝⟨ mult-associativity (n * n ^ k) m (m ^ k) ⟩
   n * n ^ k * (m * m ^ k) ∎

\end{code}

Proofs regarding exponentation and ordering

We prove that 1ᵏ ＝ 1 for all k and that 0ᵏ ＝ 0 for all k > 0.
We then prove that if m ≤ n, then kᵐ ≤ kⁿ if k ≠ 0 or m ≠ 0 and n ≠ 0.

\begin{code}

exponentiation-of-one : (k : ℕ) → 1 ^ k ＝ 1
exponentiation-of-one zero = refl
exponentiation-of-one (succ k)
 = 1 * (1 ^ k) ＝⟨ ap (λ x → 1 * x) (exponentiation-of-one k) ⟩
   1 * 1 ＝⟨ refl ⟩
   1 ∎

exponentiation-of-zero : (k : ℕ) → 0 ^ (succ k) ＝ 0
exponentiation-of-zero k = zero-left-base (0 ^ k)

exponentiation-preserves-order-right : (m n k : ℕ) → m ≤ n → (m ^ k) ≤ (n ^ k)
exponentiation-preserves-order-right m n 0 l = ⋆
exponentiation-preserves-order-right m n (succ k) l
 = ≤-multiplying m n (m ^ k) (n ^ k) l γ
 where
  γ : (m ^ k) ≤ (n ^ k)
  γ = exponentiation-preserves-order-right m n k l

exponentiation-preserves-order-left : (k m n : ℕ)
                                    → (k ≠ 0) ∔ (m ≠ 0) ∔ (n ＝ 0)
                                    → m ≤ n → (k ^ m) ≤ (k ^ n)
exponentiation-preserves-order-left zero m n (inl k≠0) l
 = 𝟘-elim (k≠0 refl)
exponentiation-preserves-order-left zero zero n (inr (inl m≠0)) l
 = 𝟘-elim (m≠0 refl)
exponentiation-preserves-order-left zero (succ m) (succ n) (inr (inl m≠0)) l
 = transport₂ _≤_ γ₁ γ₂ γ₃ 
 where
  γ₁ : 0 ＝ 0 ^ succ m
  γ₁ = (exponentiation-of-zero  m)⁻¹ 

  γ₂ : 0 ＝ 0 ^ succ n
  γ₂ = (exponentiation-of-zero n)⁻¹

  γ₃ : 0 ≤ 0
  γ₃ = ≤-refl 0
exponentiation-preserves-order-left zero zero (succ n) (inr (inr ())) _
exponentiation-preserves-order-left zero (succ m) zero (inr y) ()
exponentiation-preserves-order-left zero (succ m) (succ n) (inr (inr ())) y
exponentiation-preserves-order-left (succ k) (succ m) zero x ()
exponentiation-preserves-order-left zero zero zero (inr (inr n＝0)) l = ⋆
exponentiation-preserves-order-left (succ k) zero zero _ l = ⋆
exponentiation-preserves-order-left (succ k) zero (succ n) _ l
 = ≤-trans 1 (succ k ^ n) (succ k ^ succ n) γ₁ γ₄ 
 where
  γ₁ : 1 ≤ (succ k ^ n)
  γ₁ = exponentiation-preserves-order-left (succ k) zero n (inl (λ ())) l

  γ₂ : 1 * (succ k ^ n) ≤ (succ k) * (succ k ^ n)
  γ₂ = multiplication-preserves-order 1 (succ k) (succ k ^ n) ⋆

  γ₃ : 1 * (succ k ^ n) ＝ succ k ^ n
  γ₃ = (mult-left-id (succ k ^ n))

  γ₄ : (succ k ^ n) ≤ (succ k) * (succ k ^ n)
  γ₄ = transport (_≤ (succ k) * (succ k ^ n)) γ₃ γ₂
exponentiation-preserves-order-left (succ k) (succ m) (succ n) _ l = γ₂
 where
  γ₁ : (succ k) ^ m ≤ (succ k) ^ n
  γ₁ = exponentiation-preserves-order-left (succ k) m n (inl (λ ())) l

  γ₂ : (succ k * (succ k) ^ m) ≤ (succ k * (succ k) ^ n)
  γ₂ = multiplication-preserves-order-left
       (succ k) ((succ k) ^ m) ((succ k) ^ n) γ₁

≤-exponentiating : (m n x y : ℕ) → (m ≠ 0) ∔ (x ≠ 0) ∔ (y ＝ 0)
                 → m ≤ n → x ≤ y → m ^ x ≤ n ^ y
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
≤-exponentiating m n zero zero (inr (inr y＝0)) l₁ l₂ = ⋆
≤-exponentiating m n (succ _) zero (inr (inr _)) _ ()
≤-exponentiating m n zero (succ _) (inr (inr ())) _ _
≤-exponentiating m n (succ _) (succ _) (inr (inr ())) _ _

exponent-addition : (a b x y n : ℕ) → (n ≠ 0) ∔ (x ≠ 0) ∔ (y ＝ 0) → x ≤ y
                    → a * (n ^ x) + b * (n ^ y) ≤ (a + b) * (n ^ y)
exponent-addition zero b x y n c l = transport₂ _≤_ γ₁ γ₂ γ₃
 where
  γ₁ : b * (n ^ y) ＝ (0 * (n ^ x)) + (b * (n ^ y))
  γ₁ = b * (n ^ y) ＝⟨ (zero-left-neutral (b * (n ^ y)))⁻¹ ⟩
       0 + b * (n ^ y) ＝⟨ ap (λ x → x + b * (n ^ y))
                           (zero-left-base (n ^ x))⁻¹ ⟩
       (0 * (n ^ x) + b * (n ^ y)) ∎

  γ₂ : b * (n ^ y) ＝ (0 + b) * (n ^ y)
  γ₂ = ap (λ x → x * (n ^ y)) (zero-left-neutral b)⁻¹

  γ₃ : b * (n ^ y) ≤ b * (n ^ y)
  γ₃ = ≤-refl (b * (n ^ y))
exponent-addition a@(succ _) zero x y n c l = transport₂ _≤_ γ₁ γ₂ γ₄
 where
  γ₁ : a * (n ^ x) ＝ a * (n ^ x) + 0 * (n ^ y)
  γ₁ = a * (n ^ x) ＝⟨ refl ⟩
       a * (n ^ x) + 0 ＝⟨ ap (λ z → a * (n ^ x) + z)
                           (zero-left-base (n ^ y))⁻¹ ⟩
       (a * (n ^ x) + 0 * (n ^ y)) ∎

  γ₂ : a * (n ^ y) ＝ (a + 0) * (n ^ y)
  γ₂ = refl

  γ₃ : (n ^ x) ≤ (n ^ y)
  γ₃ = exponentiation-preserves-order-left n x y c l

  γ₄ : a * (n ^ x) ≤ a * (n ^ y)
  γ₄ = multiplication-preserves-order-left a (n ^ x) (n ^ y) γ₃
exponent-addition (succ a) (succ b) x y n c l
 = transport₂ _≤_ ((γ₂)⁻¹) ((γ₃)⁻¹) γ₅
 where
  γ₁ : a * (n ^ x) + b * (n ^ y) ≤ (a + b) * n ^ y
  γ₁ = exponent-addition a b x y n c l

  γ₂ : (succ a) * (n ^ x) + (succ b) * (n ^ y)
     ＝ (a * (n ^ x) + b * (n ^ y)) + ((n ^ x) + (n ^ y))
  γ₂ = (succ a) * (n ^ x) + (succ b) * (n ^ y) ＝⟨ i  ⟩
       (n ^ x) * (succ a) + (succ b) * (n ^ y) ＝⟨ ii ⟩
       (n ^ x) * (succ a) + (n ^ y) * (succ b) ＝⟨ iii ⟩
       (n ^ x) + (n ^ x) * a + (n ^ y) * (succ b) ＝⟨ iv ⟩
       (n ^ x) + (n ^ x) * a + ((n ^ y) + (n ^ y) * b) ＝⟨ v ⟩
       (n ^ x) + (n ^ x) * a + (n ^ y) + (n ^ y) * b ＝⟨ vi ⟩
       (n ^ x) * a + (n ^ x) + (n ^ y) + (n ^ y) * b ＝⟨ vii ⟩
       (n ^ x) * a + ((n ^ x) + (n ^ y)) + (n ^ y) * b ＝⟨ viii ⟩
       (n ^ x) * a + (((n ^ x) + (n ^ y)) + (n ^ y) * b) ＝⟨ ix ⟩
       (n ^ x) * a + ((n ^ y) * b + ((n ^ x) + (n ^ y))) ＝⟨ x' ⟩
       ((n ^ x) * a + (n ^ y) * b) + ((n ^ x) + (n ^ y)) ＝⟨ xi ⟩
       (a * (n ^ x) + (n ^ y) * b) + ((n ^ x) + (n ^ y)) ＝⟨ xii  ⟩
       ((a * (n ^ x) + b * (n ^ y)) + ((n ^ x) + (n ^ y))) ∎
   where
    i : (succ a) * (n ^ x) + (succ b) * (n ^ y)
      ＝ (n ^ x) * (succ a) + (succ b) * (n ^ y)
    i = ap (λ z → z + (succ b) * (n ^ y))
        (mult-commutativity (succ a) (n ^ x))

    ii : (n ^ x) * (succ a) + (succ b) * (n ^ y)
       ＝ (n ^ x) * (succ a) + (n ^ y) * (succ b)
    ii = ap (λ z → (n ^ x) * (succ a) + z)
         (mult-commutativity (succ b) (n ^ y))

    iii : (n ^ x) * (succ a) + (n ^ y) * (succ b)
        ＝ (n ^ x) + (n ^ x) * a + (n ^ y) * (succ b)
    iii = refl

    iv : (n ^ x) + (n ^ x) * a + (n ^ y) * (succ b)
       ＝ (n ^ x) + (n ^ x) * a + ((n ^ y) + (n ^ y) * b)
    iv = refl

    v : (n ^ x) + (n ^ x) * a + ((n ^ y) + (n ^ y) * b)
      ＝ (n ^ x) + (n ^ x) * a + (n ^ y) + (n ^ y) * b
    v = (addition-associativity ((n ^ x) + (n ^ x) * a) (n ^ y)
        ((n ^ y) * b))⁻¹

    vi : (n ^ x) + (n ^ x) * a + (n ^ y) + (n ^ y) * b
       ＝ (n ^ x) * a + (n ^ x) + (n ^ y) + (n ^ y) * b
    vi = ap (λ z → z + (n ^ y) + (n ^ y) * b)
         (addition-commutativity (n ^ x) ((n ^ x) * a))

    vii : (n ^ x) * a + (n ^ x) + (n ^ y) + (n ^ y) * b
        ＝ (n ^ x) * a + ((n ^ x) + (n ^ y)) + (n ^ y) * b
    vii = ap (λ z → z + (n ^ y) * b)
          (addition-associativity ((n ^ x) * a) (n ^ x) (n ^ y))

    viii : (n ^ x) * a + ((n ^ x) + (n ^ y)) + (n ^ y) * b
         ＝ (n ^ x) * a + (((n ^ x) + (n ^ y)) + (n ^ y) * b)
    viii = addition-associativity ((n ^ x) * a)
           ((n ^ x) + (n ^ y)) ((n ^ y) * b)

    ix : (n ^ x) * a + (((n ^ x) + (n ^ y)) + (n ^ y) * b)
       ＝ (n ^ x) * a + ((n ^ y) * b + ((n ^ x) + (n ^ y)))
    ix = ap (λ z → (n ^ x) * a + z)
         (addition-commutativity ((n ^ x) + (n ^ y)) ((n ^ y) * b))

    x' : (n ^ x) * a + ((n ^ y) * b + ((n ^ x) + (n ^ y)))
       ＝ ((n ^ x) * a + (n ^ y) * b) + ((n ^ x) + (n ^ y))
    x' = (addition-associativity ((n ^ x) * a) ((n ^ y) * b)
         ((n ^ x) + (n ^ y)))⁻¹

    xi : ((n ^ x) * a + (n ^ y) * b) + ((n ^ x) + (n ^ y))
       ＝ (a * (n ^ x) + (n ^ y) * b) + ((n ^ x) + (n ^ y))
    xi = ap (λ z → z + (n ^ y) * b + ((n ^ x) + (n ^ y)))
         (mult-commutativity (n ^ x) a)

    xii : (a * (n ^ x) + (n ^ y) * b) + ((n ^ x) + (n ^ y))
        ＝ (a * (n ^ x) + b * (n ^ y)) + ((n ^ x) + (n ^ y))
    xii = ap (λ z → a * (n ^ x) + z + ((n ^ x) + (n ^ y)))
          (mult-commutativity (n ^ y) b)

  γ₃ : ((succ a) + (succ b)) * (n ^ y)
     ＝ ((a + b) * (n ^ y)) + ((n ^ y) + (n ^ y))
  γ₃ = ((succ a) + (succ b)) * (n ^ y) ＝⟨ refl ⟩
       succ (succ a + b) * (n ^ y) ＝⟨ ap (λ z → succ z * (n ^ y))
                                       (succ-left a b) ⟩
       succ (succ (a + b)) * (n ^ y)
       ＝⟨ mult-commutativity (succ (succ (a + b))) (n ^ y) ⟩
       (n ^ y) * succ (succ (a + b)) ＝⟨ refl ⟩
       (n ^ y) + ((n ^ y) + (n ^ y) * (a + b))
       ＝⟨ (addition-associativity (n ^ y) (n ^ y)
                                                   ((n ^ y) * (a + b)))⁻¹ ⟩
       ((n ^ y) + (n ^ y)) + (n ^ y) * (a + b)
       ＝⟨ ap (((n ^ y) + (n ^ y)) +_)
       (mult-commutativity
       (n ^ y) (a + b)) ⟩
       ((n ^ y) + (n ^ y)) + (a + b) * (n ^ y)
       ＝⟨ addition-commutativity ((n ^ y) + (n ^ y))
       ((a + b) * (n ^ y)) ⟩
       (((a + b) * (n ^ y)) + ((n ^ y) + (n ^ y))) ∎

  γ₄ : (n ^ x) + (n ^ y) ≤ (n ^ y) + (n ^ y)
  γ₄ = ≤-adding (n ^ x) (n ^ y) (n ^ y) (n ^ y)
       (exponentiation-preserves-order-left n x y c l) (≤-refl (n ^ y))

  γ₅ : (a * (n ^ x) + b * (n ^ y)) + ((n ^ x) + (n ^ y))
     ≤ ((a + b) * (n ^ y)) + ((n ^ y) + (n ^ y))
  γ₅ = ≤-adding (a * (n ^ x) + b * (n ^ y))
       ((a + b) * (n ^ y)) ((n ^ x) + (n ^ y)) ((n ^ y) + (n ^ y)) γ₁ γ₄

\end{code}

A special case of the above for simplifying terms of form
b + a * n to (b + a) * n when reasoning about inequalities.

\begin{code}

simplify-constant : (a b n : ℕ) → n ≠ 0 → b + a * n ≤ (b + a) * n
simplify-constant a b zero l = 𝟘-elim (l refl)
simplify-constant a b (succ n) l = transport₂ _≤_ γ₁ γ₂ γ₃
 where
  γ₁ : b * (succ n ^ 0) + a * (succ n ^ 1) ＝ b + a * (succ n)
  γ₁ = refl

  γ₂ : (b + a) * (succ n ^ 1) ＝ (b + a) * (succ n)
  γ₂ = refl

  γ₃ : b * (succ n ^ 0) + a * (succ n ^ 1) ≤ (b + a) * (succ n ^ 1)
  γ₃ = exponent-addition b a 0 1 (succ n) (inl (λ ())) ⋆

\end{code}

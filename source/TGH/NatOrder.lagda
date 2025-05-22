Theo Hepburn, started on 8th October 2024

Contains proofs regarding natural number ordering beyond those provided in
Naturals.Order.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TGH.NatOrder where

open import MLTT.Spartan renaming (_+_ to _∔_) hiding (_^_)

open import Naturals.Addition renaming
 (addition-commutativity to +-comm ; addition-associativity to +-assoc)
open import Naturals.Multiplication renaming (mult-commutativity to *-comm)
open import Naturals.Exponentiation renaming (_ℕ^_ to _^_)
open import Naturals.Properties
open import Naturals.Order
open import Notation.Order
open import UF.Base

multiplication-preserves-order-left : (k m n : ℕ) → m ≤ n → k * m ≤ k * n
multiplication-preserves-order-left k m n l = transport₂ _≤_ γ₁ γ₂ γ₃
 where
  γ₁ : m * k ＝ k * m
  γ₁ = *-comm m k

  γ₂ : n * k ＝ k * n
  γ₂ = *-comm n k

  γ₃ : m * k ≤ n * k
  γ₃ = multiplication-preserves-order m n k l

≤-multiplying : (m n x y : ℕ) → m ≤ n → x ≤ y → m * x ≤ n * y
≤-multiplying m n x y l₁ l₂ = ≤-trans (m * x) (n * x) (n * y) γ₁ γ₂
 where
  γ₁ : m * x ≤ n * x
  γ₁ = multiplication-preserves-order m n x l₁ 

  γ₂ : n * x ≤ n * y
  γ₂ = multiplication-preserves-order-left n x y l₂

exponentiation-preserves-order-right : (m n k : ℕ) → m ≤ n → (m ^ k) ≤ (n ^ k)
exponentiation-preserves-order-right m n 0 l = ⋆
exponentiation-preserves-order-right m n (succ k) l
 = ≤-multiplying m n (m ^ k) (n ^ k) l γ
 where
  γ : (m ^ k) ≤ (n ^ k)
  γ = exponentiation-preserves-order-right m n k l

\end{code}

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

exponentiation-preserves-order-left : (k m n : ℕ) → (k ≠ 0) ∔ (m ≠ 0) ∔ (n ＝ 0)
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

exponent-addition : (a b x y n : ℕ) → (n ≠ 0) ∔ (x ≠ 0) ∔ (y ＝ 0) → x ≤ y
                    → a * (n ^ x) + b * (n ^ y) ≤ (a + b) * (n ^ y)
exponent-addition zero b x y n c l = transport₂ _≤_ γ₁ γ₂ γ₃
 where
  γ₁ : b * (n ^ y) ＝ (0 * (n ^ x)) + (b * (n ^ y))
  γ₁ = b * (n ^ y) ＝⟨ (zero-left-neutral (b * (n ^ y)))⁻¹ ⟩
       0 + b * (n ^ y) ＝⟨ ap (λ x → x + b * (n ^ y))
                           (zero-left-base (n ^ x))⁻¹ ⟩
       0 * (n ^ x) + b * (n ^ y) ∎

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
       a * (n ^ x) + 0 * (n ^ y) ∎

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
       (a * (n ^ x) + b * (n ^ y)) + ((n ^ x) + (n ^ y)) ∎
   where
    i : (succ a) * (n ^ x) + (succ b) * (n ^ y)
      ＝ (n ^ x) * (succ a) + (succ b) * (n ^ y)
    i = ap (λ z → z + (succ b) * (n ^ y)) (*-comm (succ a) (n ^ x))

    ii : (n ^ x) * (succ a) + (succ b) * (n ^ y)
       ＝ (n ^ x) * (succ a) + (n ^ y) * (succ b)
    ii = ap (λ z → (n ^ x) * (succ a) + z) (*-comm (succ b) (n ^ y))

    iii : (n ^ x) * (succ a) + (n ^ y) * (succ b)
        ＝ (n ^ x) + (n ^ x) * a + (n ^ y) * (succ b)
    iii = refl

    iv : (n ^ x) + (n ^ x) * a + (n ^ y) * (succ b)
       ＝ (n ^ x) + (n ^ x) * a + ((n ^ y) + (n ^ y) * b)
    iv = refl

    v : (n ^ x) + (n ^ x) * a + ((n ^ y) + (n ^ y) * b)
      ＝ (n ^ x) + (n ^ x) * a + (n ^ y) + (n ^ y) * b
    v = (+-assoc ((n ^ x) + (n ^ x) * a) (n ^ y) ((n ^ y) * b))⁻¹

    vi : (n ^ x) + (n ^ x) * a + (n ^ y) + (n ^ y) * b
       ＝ (n ^ x) * a + (n ^ x) + (n ^ y) + (n ^ y) * b
    vi = ap (λ z → z + (n ^ y) + (n ^ y) * b) (+-comm (n ^ x) ((n ^ x) * a))

    vii : (n ^ x) * a + (n ^ x) + (n ^ y) + (n ^ y) * b
        ＝ (n ^ x) * a + ((n ^ x) + (n ^ y)) + (n ^ y) * b
    vii = ap (λ z → z + (n ^ y) * b) (+-assoc ((n ^ x) * a) (n ^ x) (n ^ y))

    viii : (n ^ x) * a + ((n ^ x) + (n ^ y)) + (n ^ y) * b
         ＝ (n ^ x) * a + (((n ^ x) + (n ^ y)) + (n ^ y) * b)
    viii = +-assoc ((n ^ x) * a) ((n ^ x) + (n ^ y)) ((n ^ y) * b)

    ix : (n ^ x) * a + (((n ^ x) + (n ^ y)) + (n ^ y) * b)
       ＝ (n ^ x) * a + ((n ^ y) * b + ((n ^ x) + (n ^ y)))
    ix = ap (λ z → (n ^ x) * a + z) (+-comm ((n ^ x) + (n ^ y)) ((n ^ y) * b))

    x' : (n ^ x) * a + ((n ^ y) * b + ((n ^ x) + (n ^ y)))
       ＝ ((n ^ x) * a + (n ^ y) * b) + ((n ^ x) + (n ^ y))
    x' = (+-assoc ((n ^ x) * a) ((n ^ y) * b) ((n ^ x) + (n ^ y)))⁻¹

    xi : ((n ^ x) * a + (n ^ y) * b) + ((n ^ x) + (n ^ y))
       ＝ (a * (n ^ x) + (n ^ y) * b) + ((n ^ x) + (n ^ y))
    xi = ap (λ z → z + (n ^ y) * b + ((n ^ x) + (n ^ y))) (*-comm (n ^ x) a)

    xii : (a * (n ^ x) + (n ^ y) * b) + ((n ^ x) + (n ^ y))
        ＝ (a * (n ^ x) + b * (n ^ y)) + ((n ^ x) + (n ^ y))
    xii = ap (λ z → a * (n ^ x) + z + ((n ^ x) + (n ^ y))) (*-comm (n ^ y) b)

  γ₃ : ((succ a) + (succ b)) * (n ^ y)
     ＝ ((a + b) * (n ^ y)) + ((n ^ y) + (n ^ y))
  γ₃ = ((succ a) + (succ b)) * (n ^ y) ＝⟨ refl ⟩
       succ (succ a + b) * (n ^ y) ＝⟨ ap (λ z → succ z * (n ^ y))
                                       (succ-left a b) ⟩
       succ (succ (a + b)) * (n ^ y) ＝⟨ *-comm (succ (succ (a + b))) (n ^ y) ⟩
       (n ^ y) * succ (succ (a + b)) ＝⟨ refl ⟩
       (n ^ y) + ((n ^ y) + (n ^ y) * (a + b)) ＝⟨ (+-assoc (n ^ y) (n ^ y)
                                                   ((n ^ y) * (a + b)))⁻¹ ⟩
       ((n ^ y) + (n ^ y)) + (n ^ y) * (a + b) ＝⟨ ap ((n ^ y) + (n ^ y) +_)
                                                   (*-comm (n ^ y) (a + b)) ⟩
       ((n ^ y) + (n ^ y)) + (a + b) * (n ^ y) ＝⟨ +-comm ((n ^ y) + (n ^ y))
                                                   ((a + b) * (n ^ y)) ⟩
       ((a + b) * (n ^ y)) + ((n ^ y) + (n ^ y)) ∎

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

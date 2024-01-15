{-# OPTIONS --safe --without-K #-}

module InfinitePigeon.Addition where

-- The following was implemented by Martin Escardo and his student
-- Chuangje Xu as part of his Individual Study module on Agda and
-- Curry-Howard isomorphism (UG student in Computer Science,
-- Birmingham, UK, academic year 2010-2011). We also did
-- multiplication and its properties, and other things, but this is
-- not included here.

open import InfinitePigeon.Equality
open import InfinitePigeon.Logic
open import InfinitePigeon.LogicalFacts
open import InfinitePigeon.Naturals

infixl 30 _+_

_+_ : ℕ → ℕ → ℕ
n + 0 = n
n + (succ m) = succ(n + m)


n-plus-zero-equals-n : ∀(n : ℕ) → n + 0 ≡ n
n-plus-zero-equals-n n = reflexivity


zero-plus-n-equals-n : ∀(n : ℕ) → 0 + n ≡ n
zero-plus-n-equals-n = induction base step
  where base : 0 + 0 ≡ 0
        base = reflexivity

        step : ∀(n : ℕ) → 0 + n ≡ n → 0 + succ n ≡ succ n
        step n IH = goal
          where lemma₀ : 0 + succ n ≡ succ (0 + n)
                lemma₀ = reflexivity

                lemma₁ : succ (0 + n) ≡ succ n
                lemma₁ = compositionality succ IH

                goal : 0 + succ n ≡ succ n
                goal = transitivity lemma₀ lemma₁


addition-associativity : ∀(l n m : ℕ) → (l + n) + m ≡ l + (n + m)
addition-associativity l n = induction base step
  where base : (l + n) + 0 ≡ l + (n + 0)
        base = goal
          where lemma₀ : (l + n) + 0 ≡ l + n
                lemma₀ = reflexivity

                lemma₁ : l + n ≡ l + (n + 0)
                lemma₁ = reflexivity

                goal : (l + n) + 0 ≡ l + (n + 0)
                goal = transitivity lemma₀ lemma₁

        step : ∀(m : ℕ) → (l + n) + m ≡ l + (n + m) →
                          (l + n) + succ m ≡ l + (n + succ m)
        step m IH = goal
          where lemma₀ : (l + n) + succ m ≡ succ ((l + n) + m)
                lemma₀ = reflexivity

                lemma₁ : succ ((l + n) + m) ≡ succ (l + (n + m))
                lemma₁ = compositionality succ IH

                lemma₂ : succ (l + (n + m)) ≡ l + succ (n + m)
                lemma₂ = reflexivity

                lemma₃ : l + succ (n + m) ≡ l + (n + succ m)
                lemma₃ = reflexivity

                goal : (l + n) + succ m ≡ l + (n + succ m)
                goal = transitivity lemma₀ (transitivity lemma₁
                      (transitivity lemma₂ lemma₃))

addition-commutativity : ∀(n m : ℕ) → n + m ≡ m + n
addition-commutativity n = induction base step
  where base : n + 0 ≡ 0 + n
        base = transitivity (n-plus-zero-equals-n n)
                            (symmetry (zero-plus-n-equals-n n))

        step : ∀(m : ℕ) → n + m ≡ m + n → n + succ m ≡ succ m + n
        step m IH = goal
          where lemma₀ : ∀(k : ℕ) → succ k ≡ 1 + k
                lemma₀ = induction base₀ step₀
                  where base₀ : succ 0 ≡ 1 + 0
                        base₀ = reflexivity

                        step₀ : ∀(k : ℕ) → succ k ≡ 1 + k →
                                           succ (succ k) ≡ 1 + (succ k)
                        step₀ k IH' = goal₀
                          where lemma₀' : 1 + (succ k) ≡ succ (1 + k)
                                lemma₀' = reflexivity

                                lemma₁' : succ (1 + k) ≡ succ (succ k)
                                lemma₁' = compositionality succ (symmetry IH')

                                goal₀ : succ (succ k) ≡ 1 + (succ k)
                                goal₀ = symmetry (transitivity lemma₀' lemma₁')

                lemma₁ : n + succ m ≡ succ (n + m)
                lemma₁ = reflexivity

                lemma₂ : succ (n + m) ≡ succ (m + n)
                lemma₂ = compositionality succ IH

                lemma₃ : succ (m + n) ≡ 1 + (m + n)
                lemma₃ = lemma₀ (m + n)

                lemma₄ : 1 + (m + n) ≡ (1 + m) + n
                lemma₄ = symmetry (addition-associativity 1 m n)

                lemma₅ : (1 + m) + n ≡ succ m + n
                lemma₅ = compositionality (λ x → x + n) (symmetry (lemma₀ m))

                goal : n + succ m ≡ succ m + n
                goal = transitivity lemma₁ (transitivity lemma₂
                      (transitivity lemma₃ (transitivity lemma₄ lemma₅)))


trivial-addition-rearrangement : ∀(x y z : ℕ) → x + y + z ≡ x + z + y
trivial-addition-rearrangement x y z =
      transitivity
        (addition-associativity x y z)
        (transitivity
           (compositionality (λ t → x + t) (addition-commutativity y z))
           (symmetry (addition-associativity x z y)))

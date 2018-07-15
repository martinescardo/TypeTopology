\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module NaturalsAddition where

open import SpartanMLTT hiding (_+_)

infixl 31 _+_

_+_ : ℕ → ℕ → ℕ
n + 0 = n
n + (succ m) = succ(n + m)


n-plus-zero-equals-n : (n : ℕ) → n + 0 ≡ n
n-plus-zero-equals-n n = refl

zero-plus-n-equals-n : (n : ℕ) → 0 + n ≡ n
zero-plus-n-equals-n = induction base step
  where base : 0 + 0 ≡ 0
        base = refl

        step : (n : ℕ) → 0 + n ≡ n → 0 + succ n ≡ succ n
        step n IH = goal
          where lemma₀ : 0 + succ n ≡ succ (0 + n)
                lemma₀ = refl

                lemma₁ : succ (0 + n) ≡ succ n
                lemma₁ = ap succ IH

                goal : 0 + succ n ≡ succ n
                goal = lemma₀ ∙ lemma₁


addition-associativity : (l n m : ℕ) → (l + n) + m ≡ l + (n + m)
addition-associativity l n = induction base step
  where base : (l + n) + 0 ≡ l + (n + 0)
        base = goal
          where lemma₀ : (l + n) + 0 ≡ l + n
                lemma₀ = refl

                lemma₁ : l + n ≡ l + (n + 0)
                lemma₁ = refl

                goal : (l + n) + 0 ≡ l + (n + 0)
                goal = lemma₀ ∙ lemma₁

        step : (m : ℕ) → (l + n) + m ≡ l + (n + m) →
                          (l + n) + succ m ≡ l + (n + succ m)
        step m IH = goal
          where lemma₀ : (l + n) + succ m ≡ succ ((l + n) + m)
                lemma₀ = refl

                lemma₁ : succ ((l + n) + m) ≡ succ (l + (n + m))
                lemma₁ = ap succ IH

                lemma𝟚 : succ (l + (n + m)) ≡ l + succ (n + m)
                lemma𝟚 = refl

                lemma₃ : l + succ (n + m) ≡ l + (n + succ m)
                lemma₃ = refl

                goal : (l + n) + succ m ≡ l + (n + succ m)
                goal = lemma₀ ∙ lemma₁ ∙ lemma𝟚 ∙ lemma₃

addition-commutativity : (n m : ℕ) → n + m ≡ m + n
addition-commutativity n = induction base step
  where base : n + 0 ≡ 0 + n
        base = n-plus-zero-equals-n n ∙ (zero-plus-n-equals-n n)⁻¹

        step : (m : ℕ) → n + m ≡ m + n → n + succ m ≡ succ m + n
        step m IH = goal
          where lemma₀ : (k : ℕ) → succ k ≡ 1 + k
                lemma₀ = induction base₀ step₀
                  where base₀ : succ 0 ≡ 1 + 0
                        base₀ = refl

                        step₀ : (k : ℕ) → succ k ≡ 1 + k →
                                           succ (succ k) ≡ 1 + (succ k)
                        step₀ k IH' = goal₀
                          where lemma₀' : 1 + (succ k) ≡ succ (1 + k)
                                lemma₀' = refl

                                lemma₁' : succ (1 + k) ≡ succ (succ k)
                                lemma₁' = ap succ (IH' ⁻¹)

                                goal₀ : succ (succ k) ≡ 1 + (succ k)
                                goal₀ = (lemma₀' ∙ lemma₁')⁻¹

                lemma₁ : n + succ m ≡ succ (n + m)
                lemma₁ = refl

                lemma₂ : succ (n + m) ≡ succ (m + n)
                lemma₂ = ap succ IH

                lemma₃ : succ (m + n) ≡ 1 + (m + n)
                lemma₃ = lemma₀ (m + n)

                lemma₄ : 1 + (m + n) ≡ (1 + m) + n
                lemma₄ = (addition-associativity 1 m n)⁻¹

                lemma₅ : (1 + m) + n ≡ succ m + n
                lemma₅ = ap (λ - → - + n) ((lemma₀ m)⁻¹)

                goal : n + succ m ≡ succ m + n
                goal = lemma₁ ∙ lemma₂ ∙ lemma₃ ∙ lemma₄ ∙ lemma₅


trivial-addition-rearrangement : (x y z : ℕ) → x + y + z ≡ x + z + y
trivial-addition-rearrangement x y z =
        addition-associativity x y z ∙ ap (λ - → x + -) (addition-commutativity y z) ∙ (addition-associativity x z y)⁻¹

\end{code}

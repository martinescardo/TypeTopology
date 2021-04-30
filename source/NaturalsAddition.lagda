Chuangjie Xu 2011, with changes by Martin Escardo later.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module NaturalsAddition where

open import SpartanMLTT hiding (_+_)

infixl 31 _+_

_+_ : ℕ → ℕ → ℕ
n + 0 = n
n + (succ m) = succ (n + m)


zero-right-neutral : (n : ℕ) → n + 0 ≡ n
zero-right-neutral n = refl

zero-left-neutral : (n : ℕ) → 0 + n ≡ n
zero-left-neutral = induction base step
  where
   base : 0 + 0 ≡ 0
   base = refl

   step : (n : ℕ) → 0 + n ≡ n → 0 + succ n ≡ succ n
   step n IH = 0 + succ n   ≡⟨ refl ⟩
               succ (0 + n) ≡⟨ ap succ IH ⟩
               succ n       ∎

addition-associativity : (l n m : ℕ) → (l + n) + m ≡ l + (n + m)
addition-associativity l n = induction base step
  where
   base : (l + n) + 0 ≡ l + (n + 0)
   base = (l + n) + 0  ≡⟨ refl ⟩
           l + n       ≡⟨ refl ⟩
           l + (n + 0) ∎

   step : (m : ℕ) → (l + n) + m ≡ l + (n + m)
                  → (l + n) + succ m ≡ l + (n + succ m)
   step m IH = (l + n) + succ m   ≡⟨ refl ⟩
               succ ((l + n) + m) ≡⟨ ap succ IH ⟩
               succ (l + (n + m)) ≡⟨ refl ⟩
               l + succ (n + m)   ≡⟨ refl ⟩
               l + (n + succ m)   ∎

addition-commutativity : (n m : ℕ) → n + m ≡ m + n
addition-commutativity n = induction base step
  where
   base : n + 0 ≡ 0 + n
   base = n + 0 ≡⟨ zero-right-neutral n ⟩
          n     ≡⟨ (zero-left-neutral n)⁻¹ ⟩
          0 + n ∎

   step : (m : ℕ) → n + m ≡ m + n → n + succ m ≡ succ m + n
   step m IH = n + succ m   ≡⟨ refl ⟩
               succ (n + m) ≡⟨ ap succ IH ⟩
               succ (m + n) ≡⟨ lemma₀ (m + n) ⟩
               1 + (m + n)  ≡⟨ (addition-associativity 1 m n)⁻¹ ⟩
               (1 + m) + n  ≡⟨ ap (_+ n) ((lemma₀ m)⁻¹) ⟩
               succ m + n   ∎
     where
      lemma₀ : (k : ℕ) → succ k ≡ 1 + k
      lemma₀ = induction base₀ step₀
        where
         base₀ : succ 0 ≡ 1 + 0
         base₀ = refl

         step₀ : (k : ℕ) → succ k ≡ 1 + k → succ (succ k) ≡ 1 + succ k
         step₀ k IH = succ (succ k) ≡⟨ ap succ IH ⟩
                      succ (1 + k)  ≡⟨ refl ⟩
                      1 + succ k    ∎

trivial-addition-rearrangement : (x y z : ℕ) → x + y + z ≡ x + z + y
trivial-addition-rearrangement x y z =
  (x + y) + z ≡⟨ addition-associativity x y z ⟩
  x + (y + z) ≡⟨ ap (x +_) (addition-commutativity y z) ⟩
  x + (z + y) ≡⟨ (addition-associativity x z y)⁻¹ ⟩
  (x + z) + y ∎

\end{code}

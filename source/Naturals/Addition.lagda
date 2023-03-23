Chuangjie Xu 2011, with changes by Martin Escardo later.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module Naturals.Addition where

open import MLTT.Spartan hiding (_+_)
open import Naturals.Properties

infixl 31 _+_

_+_ : ℕ → ℕ → ℕ
n + 0 = n
n + (succ m) = succ (n + m)

{-# BUILTIN NATPLUS _+_ #-}

zero-right-neutral : (n : ℕ) → n + 0 ＝ n
zero-right-neutral n = refl

zero-left-neutral : (n : ℕ) → 0 + n ＝ n
zero-left-neutral = induction base step
  where
   base : 0 + 0 ＝ 0
   base = refl

   step : (n : ℕ) → 0 + n ＝ n → 0 + succ n ＝ succ n
   step n IH = 0 + succ n   ＝⟨ refl ⟩
               succ (0 + n) ＝⟨ ap succ IH ⟩
               succ n       ∎

addition-associativity : (l n m : ℕ) → (l + n) + m ＝ l + (n + m)
addition-associativity l n = induction base step
  where
   base : (l + n) + 0 ＝ l + (n + 0)
   base = (l + n) + 0  ＝⟨ refl ⟩
           l + n       ＝⟨ refl ⟩
           l + (n + 0) ∎

   step : (m : ℕ) → (l + n) + m ＝ l + (n + m)
                  → (l + n) + succ m ＝ l + (n + succ m)
   step m IH = (l + n) + succ m   ＝⟨ refl ⟩
               succ ((l + n) + m) ＝⟨ ap succ IH ⟩
               succ (l + (n + m)) ＝⟨ refl ⟩
               l + succ (n + m)   ＝⟨ refl ⟩
               l + (n + succ m)   ∎

addition-commutativity : (n m : ℕ) → n + m ＝ m + n
addition-commutativity n = induction base step
  where
   base : n + 0 ＝ 0 + n
   base = n + 0 ＝⟨ zero-right-neutral n ⟩
          n     ＝⟨ (zero-left-neutral n)⁻¹ ⟩
          0 + n ∎

   step : (m : ℕ) → n + m ＝ m + n → n + succ m ＝ succ m + n
   step m IH = n + succ m   ＝⟨ refl ⟩
               succ (n + m) ＝⟨ ap succ IH ⟩
               succ (m + n) ＝⟨ lemma₀ (m + n) ⟩
               1 + (m + n)  ＝⟨ (addition-associativity 1 m n)⁻¹ ⟩
               (1 + m) + n  ＝⟨ ap (_+ n) ((lemma₀ m)⁻¹) ⟩
               succ m + n   ∎
     where
      lemma₀ : (k : ℕ) → succ k ＝ 1 + k
      lemma₀ = induction base₀ step₀
        where
         base₀ : succ 0 ＝ 1 + 0
         base₀ = refl

         step₀ : (k : ℕ) → succ k ＝ 1 + k → succ (succ k) ＝ 1 + succ k
         step₀ k IH = succ (succ k) ＝⟨ ap succ IH ⟩
                      succ (1 + k)  ＝⟨ refl ⟩
                      1 + succ k    ∎

trivial-addition-rearrangement : (x y z : ℕ) → x + y + z ＝ x + z + y
trivial-addition-rearrangement x y z =
  (x + y) + z ＝⟨ addition-associativity x y z ⟩
  x + (y + z) ＝⟨ ap (x +_) (addition-commutativity y z) ⟩
  x + (z + y) ＝⟨ (addition-associativity x z y)⁻¹ ⟩
  (x + z) + y ∎

\end{code}

Added 12/05/2020 by Andrew Sneap.

Some more simple properties of addition. The proofs all use induction,
apart from addition-right-cancellable which follows from
addition-left-cancellable and commutativity of addition.

\begin{code}

succ-right : (x y : ℕ) → x + succ y ＝ succ (x + y)
succ-right x y = refl

succ-left : (x y : ℕ) → succ x + y ＝ succ (x + y)
succ-left x = induction base step
  where
    base : succ x + 0 ＝ succ (x + 0)
    base = succ x + 0   ＝⟨ refl         ⟩
           succ x       ＝⟨ ap succ refl ⟩
           succ (x + 0) ∎

    step : (k : ℕ) → succ x + k ＝ succ (x + k) → succ x + succ k ＝ succ (x + succ k)
    step k IH = succ x + succ k     ＝⟨ refl ⟩
                succ (succ x + k)   ＝⟨ ap succ IH ⟩
                succ (succ (x + k)) ＝⟨ refl ⟩
                succ (x + succ k)   ∎

addition-left-cancellable : (x y z : ℕ) → z + x ＝ z + y → x ＝ y
addition-left-cancellable x y = induction base step
 where
  base : 0 + x ＝ 0 + y → x ＝ y
  base h = x      ＝⟨ zero-left-neutral x ⁻¹ ⟩
           0 + x  ＝⟨ h                      ⟩
           0 + y  ＝⟨ zero-left-neutral y    ⟩
           y ∎

  step : (k : ℕ)
       → (k + x      ＝ k + y      → x ＝ y)
       → (succ k + x ＝ succ k + y → x ＝ y)
  step k IH r = IH (succ-lc (lemma₁ r))
   where
    lemma₁ : succ k + x ＝ succ k + y → succ (k + x) ＝ succ (k + y)
    lemma₁ r = succ (k + x)           ＝⟨ succ-left k x ⁻¹ ⟩
               succ k + x             ＝⟨ r                ⟩
               succ k + y             ＝⟨ succ-left k y    ⟩
               succ (k + y) ∎


addition-right-cancellable : (x y z : ℕ) → x + z ＝ y + z → x ＝ y
addition-right-cancellable x y z r = addition-left-cancellable x y z lemma₀
 where
  lemma₀ : z + x ＝ z + y
  lemma₀ = z + x      ＝⟨ addition-commutativity z x ⟩
           x + z      ＝⟨ r                          ⟩
           y + z      ＝⟨ addition-commutativity y z ⟩
           z + y ∎

\end{code}

We also have that if the sum of two numbers are zero, then the right
argument is zero. The left argument is zero, which can be proved using
commutativity of addition. This function is needed in the HCF file.

\begin{code}

sum-to-zero-gives-zero : (x y : ℕ) → x + y ＝ 0 → y ＝ 0
sum-to-zero-gives-zero x 0        e = refl
sum-to-zero-gives-zero x (succ y) e = have positive-not-zero (x + y) which-contradicts e

\end{code}

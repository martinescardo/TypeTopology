Andrew Sneap - 27th April 2021

In this file I prove some common properties of Naturals Numbers and addition of Natural Numbers

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import NaturalsAddition --TypeTopology
open import NaturalNumbers-Properties --TypeTopology

module MoreNaturalProperties where

open NaturalsAddition

addition-right-succ : (x y : ℕ) → x + succ y ≡ succ (x + y)
addition-right-succ x y = refl

succ-left : (x y : ℕ) → succ x + y ≡ succ (x + y)
succ-left x = induction base step 
  where
    base : succ x + 0 ≡ succ (x + 0)
    base = succ x + 0   ≡⟨ refl         ⟩
           succ x       ≡⟨ ap succ refl ⟩ 
           succ (x + 0) ∎

    step : (k : ℕ) → succ x + k ≡ succ (x + k) → succ x + succ k ≡ succ (x + succ k)
    step k IH = succ x + succ k     ≡⟨ refl ⟩
                succ (succ x + k)   ≡⟨ ap succ IH ⟩
                succ (succ (x + k)) ≡⟨ refl ⟩
                succ (x + succ k)   ∎

+-comm : (x n : ℕ) → x + n ≡ n + x
+-comm x = induction base step
  where
    base : x + 0 ≡ 0 + x
    base = zero-left-neutral x ⁻¹

    step : (k : ℕ) → x + k ≡ k + x → x + succ k ≡ succ k + x
    step k IH = x + succ k    ≡⟨ refl ⟩
                succ (x + k)  ≡⟨ ap succ IH ⟩
                succ (k + x)  ≡⟨ succ-left k x ⁻¹ ⟩
                succ k + x ∎

addition-left-cancellable : (x y z : ℕ) → z + x ≡ z + y → x ≡ y
addition-left-cancellable x y = induction base step
 where
  base : 0 + x ≡ 0 + y → x ≡ y
  base h = x      ≡⟨ zero-left-neutral x ⁻¹ ⟩
           0 + x  ≡⟨ h                      ⟩
           0 + y  ≡⟨ zero-left-neutral y    ⟩
           y ∎

  step : (k : ℕ)
       → (k + x      ≡ k + y      → x ≡ y)
       → (succ k + x ≡ succ k + y → x ≡ y)
  step k IH r = IH (succ-lc (lemma₁ r))
   where
    lemma₁ : succ k + x ≡ succ k + y → succ (k + x) ≡ succ (k + y)
    lemma₁ r = succ (k + x)           ≡⟨ succ-left k x ⁻¹ ⟩
               succ k + x             ≡⟨ r                         ⟩
               succ k + y             ≡⟨ succ-left k y    ⟩
               succ (k + y) ∎        


addition-right-cancellable : (x y z : ℕ) → x + z ≡ y + z → x ≡ y
addition-right-cancellable x y z r = addition-left-cancellable x y z lemma₀
 where
  lemma₀ : z + x ≡ z + y
  lemma₀ = z + x      ≡⟨ addition-commutativity z x ⟩
           x + z      ≡⟨ r                          ⟩
           y + z      ≡⟨ addition-commutativity y z ⟩ 
           z + y ∎

sum-to-zero-gives-zero : (x y : ℕ) → x + y ≡ 0 → y ≡ 0
sum-to-zero-gives-zero x 0        e = refl
sum-to-zero-gives-zero x (succ y) e = have positive-not-zero (x + y) which-contradicts e

succ-pred : (x : ℕ) → succ (pred (succ x)) ≡ succ x
succ-pred x = refl

succ-pred' : (x : ℕ) → ¬ (x ≡ 0) → succ (pred x) ≡ x
succ-pred' zero     nz = 𝟘-elim (nz refl)
succ-pred' (succ n) _ = refl

pred-succ : (x : ℕ) → pred (succ (succ x)) ≡ succ x
pred-succ x = refl

\end{code}

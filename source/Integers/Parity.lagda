\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Integers.Abs
open import Integers.Addition
open import Integers.Type
open import Integers.Multiplication
open import Integers.Negation
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Parity
open import Naturals.Properties
open import UF.Subsingletons

module Integers.Parity where

ℤeven ℤodd : ℤ → 𝓤₀ ̇
ℤeven z = even (abs z)
ℤodd  z = odd (abs z)

ℤeven-not-odd : (n : ℤ) → ℤeven n → ¬ ℤodd n
ℤeven-not-odd n = even-not-odd (abs n)

ℤodd-not-even : (n : ℤ) → ℤodd n → ¬ ℤeven n
ℤodd-not-even n = odd-not-even (abs n)

ℤzero-not-odd : (n : ℤ) → ℤodd n → ¬ (n ＝ pos 0)
ℤzero-not-odd (pos 0)        on e = on
ℤzero-not-odd (pos (succ n)) on e = positive-not-zero n (pos-lc e)

ℤeven-is-prop : (n : ℤ) → is-prop (ℤeven n)
ℤeven-is-prop n = even-is-prop (abs n)

ℤodd-is-prop : (n : ℤ) → is-prop (ℤodd n)
ℤodd-is-prop n = odd-is-prop (abs n)

ℤeven-or-odd : (n : ℤ) → ℤeven n ∔ ℤodd n
ℤeven-or-odd (pos 0)            = inl ⋆
ℤeven-or-odd (pos (succ x))     = ℤeven-or-odd (negsucc x)
ℤeven-or-odd (negsucc 0)        = inr ⋆
ℤeven-or-odd (negsucc (succ x)) = ℤeven-or-odd (pos x)

ℤeven-or-odd-is-prop : (n : ℤ) → is-prop (ℤeven n ∔ ℤodd n)
ℤeven-or-odd-is-prop n = even-or-odd-is-prop (abs n)

ℤsucc-even-is-odd : (n : ℤ) → ℤeven n → ℤodd (succℤ n)
ℤsucc-even-is-odd (pos x)            = succ-even-is-odd (abs (pos x))
ℤsucc-even-is-odd (negsucc 0)        = id
ℤsucc-even-is-odd (negsucc (succ x)) = id

ℤpred-even-is-odd : (n : ℤ) → ℤeven n → ℤodd (predℤ n)
ℤpred-even-is-odd (pos 0)        = id
ℤpred-even-is-odd (pos (succ x)) = id
ℤpred-even-is-odd (negsucc x)    = id

ℤsucc-odd-is-even : (n : ℤ) → ℤodd n → ℤeven (succℤ n)
ℤsucc-odd-is-even (pos x)            = succ-odd-is-even (abs (pos x))
ℤsucc-odd-is-even (negsucc 0)        = id
ℤsucc-odd-is-even (negsucc (succ x)) = id

ℤpred-odd-is-even : (n : ℤ) → ℤodd n → ℤeven (predℤ n)
ℤpred-odd-is-even (pos 0)        = id
ℤpred-odd-is-even (pos (succ x)) = id
ℤpred-odd-is-even (negsucc x)    = id

ℤodd-succ-succ : (n : ℤ) → ℤodd n → ℤodd (succℤ (succℤ n))
ℤodd-succ-succ (pos x)                   = odd-succ-succ (abs (pos x))
ℤodd-succ-succ (negsucc 0)               = id
ℤodd-succ-succ (negsucc 1)               = id
ℤodd-succ-succ (negsucc (succ (succ x))) = id

ℤodd-pred-pred : (n : ℤ) → ℤodd n → ℤodd (predℤ (predℤ n))
ℤodd-pred-pred (pos 0)               = id
ℤodd-pred-pred (pos 1)               = id
ℤodd-pred-pred (pos (succ (succ x))) = id
ℤodd-pred-pred (negsucc x)           = id

ℤodd-succ-succ' : (n : ℤ) → ℤodd (succℤ (succℤ n)) → ℤodd n
ℤodd-succ-succ' (pos x)                   = odd-succ-succ' (abs (pos x))
ℤodd-succ-succ' (negsucc 0)               = id
ℤodd-succ-succ' (negsucc 1)               = id
ℤodd-succ-succ' (negsucc (succ (succ x))) = id

ℤodd-pred-pred' : (n : ℤ) → ℤodd (predℤ (predℤ n)) → ℤodd n
ℤodd-pred-pred' (pos 0)               = id
ℤodd-pred-pred' (pos 1)               = id
ℤodd-pred-pred' (pos (succ (succ x))) = id
ℤodd-pred-pred' (negsucc x)           = id

ℤeven-succ-succ : (n : ℤ) → ℤeven n → ℤeven (succℤ (succℤ n))
ℤeven-succ-succ (pos x)                   = even-succ-succ (abs (pos x))
ℤeven-succ-succ (negsucc 0)               = id
ℤeven-succ-succ (negsucc 1)               = id
ℤeven-succ-succ (negsucc (succ (succ x))) = id

ℤeven-pred-pred : (n : ℤ) → ℤeven n → ℤeven (predℤ (predℤ n))
ℤeven-pred-pred (pos 0)               = id
ℤeven-pred-pred (pos 1)               = id
ℤeven-pred-pred (pos (succ (succ x))) = id
ℤeven-pred-pred (negsucc x)           = id

ℤeven-succ-succ' : (n : ℤ) → ℤeven (succℤ (succℤ n)) → ℤeven n
ℤeven-succ-succ' (pos x)                   = even-succ-succ' (abs (pos x))
ℤeven-succ-succ' (negsucc 0)               = id
ℤeven-succ-succ' (negsucc 1)               = id
ℤeven-succ-succ' (negsucc (succ (succ x))) = id

ℤeven-pred-pred' : (n : ℤ) → ℤeven (predℤ (predℤ n)) → ℤeven n
ℤeven-pred-pred' (pos 0)               = id
ℤeven-pred-pred' (pos 1)               = id
ℤeven-pred-pred' (pos (succ (succ x))) = id
ℤeven-pred-pred' (negsucc x)           = id

ℤeven*even : (n m : ℤ) → ℤeven n → ℤeven m → ℤeven (n * m)
ℤeven*even n m en em = transport even I II
 where
  I : abs n ℕ* abs m ＝ abs (n * m)
  I = abs-over-mult n m ⁻¹
  II : even (abs n ℕ* abs m)
  II = even*even (abs n) (abs m) en em

ℤodd*odd : (n m : ℤ) → ℤodd n → ℤodd m → ℤodd (n * m)
ℤodd*odd n m on om = transport odd I II
 where
  I : abs n ℕ* abs m ＝ abs (n * m)
  I = abs-over-mult n m ⁻¹
  II : odd (abs n ℕ* abs m)
  II = odd*odd (abs n) (abs m) on om

ℤeven*odd : (n m : ℤ) → ℤeven n → ℤodd m → ℤeven (n * m)
ℤeven*odd n m en om = transport even I II
 where
  I : abs n ℕ* abs m ＝ abs (n * m)
  I = (abs-over-mult n m ⁻¹)
  II : even (abs n ℕ* abs m)
  II = (even*odd (abs n) (abs m) en om)

ℤodd*even : (n m : ℤ) → ℤodd n → ℤeven m → ℤeven (n * m)
ℤodd*even n m on em = transport ℤeven (ℤ*-comm m n) (ℤeven*odd m n em on)

ℤeven-neg : (n : ℤ) → ℤeven n → ℤeven (- n)
ℤeven-neg n = transport even (abs-removes-neg-sign n)

ℤodd-neg : (n : ℤ) → ℤodd n → ℤodd (- n)
ℤodd-neg n = transport odd (abs-removes-neg-sign n)

ℤeven+even : (n m : ℤ) → ℤeven n → ℤeven m → ℤeven (n + m)
ℤeven+even n (pos 0)                   en em = en
ℤeven+even n (pos 1)                   en em = 𝟘-elim em
ℤeven+even n (pos (succ (succ m)))     en em = ℤeven-succ-succ (n + pos m) (ℤeven+even n (pos m) en em)
ℤeven+even n (negsucc 0)               en em = 𝟘-elim em
ℤeven+even n (negsucc 1)               en em = ℤeven-pred-pred n en
ℤeven+even n (negsucc (succ (succ m))) en em = ℤeven-pred-pred (n + negsucc m) (ℤeven+even n (negsucc m) en em)

ℤeven+odd : (n m : ℤ) → ℤeven n → ℤodd m → ℤodd (n + m)
ℤeven+odd n (pos 0)                   on em = 𝟘-elim em
ℤeven+odd n (pos 1)                   on em = ℤsucc-even-is-odd n on
ℤeven+odd n (pos (succ (succ m)))     on em = ℤodd-succ-succ (n + pos m) (ℤeven+odd n (pos m) on em)
ℤeven+odd n (negsucc 0)               on em = ℤpred-even-is-odd n on
ℤeven+odd n (negsucc 1)               on em = 𝟘-elim em
ℤeven+odd n (negsucc (succ (succ m))) on em = ℤodd-pred-pred (n +negsucc m) (ℤeven+odd n (negsucc m) on em)

ℤodd+even : (n m : ℤ) → ℤodd n → ℤeven m → ℤodd (n + m)
ℤodd+even n m on em = transport ℤodd (ℤ+-comm m n) (ℤeven+odd m n em on)

ℤodd+odd : (n m : ℤ) → ℤodd n → ℤodd m → ℤeven (n + m)
ℤodd+odd n (pos 0)                   on om = 𝟘-elim om
ℤodd+odd n (pos 1)                   on om = ℤsucc-odd-is-even n on
ℤodd+odd n (pos (succ (succ m)))     on om = ℤeven-succ-succ (n + pos m) (ℤodd+odd n (pos m) on om)
ℤodd+odd n (negsucc 0)               on om = ℤpred-odd-is-even n on
ℤodd+odd n (negsucc 1)               on om = 𝟘-elim om
ℤodd+odd n (negsucc (succ (succ m))) on om = ℤeven-pred-pred (n + negsucc m) (ℤodd+odd n (negsucc m) on om)

evenℕ-to-ℤ : (n : ℕ) → even n → ℤeven (pos n)
evenℕ-to-ℤ n = id

evenℕ-to-ℤ' : (n : ℕ) → even n → ℤeven (- pos n)
evenℕ-to-ℤ' 0        = id
evenℕ-to-ℤ' (succ n) = id

ℤmultiple-of-two-even-lemma-pos : (n : ℤ) (k : ℕ) → n ＝ pos 2 * pos k → ℤeven n
ℤmultiple-of-two-even-lemma-pos (pos n) k e = induction base step k
 where
  base : even n
  base = multiple-of-two-even-lemma n k I
   where
    I : n ＝ 2 ℕ* k
    I = pos-lc (e ∙ pos-multiplication-equiv-to-ℕ 2 k)
  step : (k : ℕ) → even n → even n
  step k = id
ℤmultiple-of-two-even-lemma-pos (negsucc n) k e = 𝟘-elim (negsucc-not-pos (e ∙ pos-multiplication-equiv-to-ℕ 2 k))

ℤmultiple-of-two-even-lemma-neg : (n : ℤ) → (k : ℕ) → n ＝ pos 2 * negsucc k → ℤeven n
ℤmultiple-of-two-even-lemma-neg (pos n)     k e = 𝟘-elim (pos-not-negsucc (e ∙ pr₂ (pos-times-negative 1 k)))
ℤmultiple-of-two-even-lemma-neg (negsucc n) k e = induction base step k
 where
  base : even (succ n)
  base = II
   where
    I : - pos (succ n) ＝ - pos (2 ℕ* succ k)
    I = negsucc n              ＝⟨ e                                                ⟩
        pos 2 * negsucc k      ＝⟨ negation-dist-over-mult (pos 2) (pos (succ k))   ⟩
        - pos 2 * pos (succ k) ＝⟨ ap -_ (pos-multiplication-equiv-to-ℕ 2 (succ k)) ⟩
        - pos (2 ℕ* succ k)    ∎
    II : even (succ n)
    II = multiple-of-two-even-lemma (succ n) (succ k) (pos-lc (negatives-equal (pos (succ n)) (pos (2 ℕ* succ k)) I))
  step : (k : ℕ) → odd n → odd n
  step k = id

ℤmultiple-of-two-even-lemma : (n k : ℤ) → n ＝ pos 2 * k → ℤeven n
ℤmultiple-of-two-even-lemma n (pos k)     e = ℤmultiple-of-two-even-lemma-pos n k e
ℤmultiple-of-two-even-lemma n (negsucc k) e = ℤmultiple-of-two-even-lemma-neg n k e

ℤmultiple-of-two-even : (n : ℤ) → Σ k ꞉ ℤ , n ＝ pos 2 * k → ℤeven n
ℤmultiple-of-two-even n (k , e) = ℤmultiple-of-two-even-lemma n k e

ℤsucc-multiple-of-two-odd : (n k : ℤ) → n ＝ succℤ (pos 2 * k) → ℤodd n
ℤsucc-multiple-of-two-odd n k e = transport ℤodd (succpredℤ n) I
 where
  I : ℤodd (succℤ (predℤ n))
  I = ℤsucc-even-is-odd (predℤ n) (transport ℤeven (III ⁻¹) II)
   where
    II : ℤeven (pos 2 * k)
    II = ℤmultiple-of-two-even (pos 2 * k) (k , refl)
    III : predℤ n ＝ pos 2 * k
    III = predℤ n                    ＝⟨ ap predℤ e            ⟩
          predℤ (succℤ (pos 2 * k))  ＝⟨ predsuccℤ (pos 2 * k) ⟩
          pos 2 * k ∎

ℤeven-is-multiple-of-two : (n : ℤ) → ℤeven n → Σ k ꞉ ℤ , n ＝ pos 2 * k
ℤeven-is-multiple-of-two (pos n)     en = I (even-is-multiple-of-two n en)
 where
  I : Σ k ꞉ ℕ , n ＝ 2 ℕ* k → Σ k ꞉ ℤ , pos n ＝ pos 2 * k
  I (k , e) = (pos k) , (ap pos e ∙ pos-multiplication-equiv-to-ℕ 2 k ⁻¹)
ℤeven-is-multiple-of-two (negsucc n) en = I (even-is-multiple-of-two (succ n) en)
 where
  I : Σ k ꞉ ℕ , succ n ＝ 2 ℕ* k → Σ k ꞉ ℤ , negsucc n ＝ pos 2 * k
  I (0      , e) = 𝟘-elim (positive-not-zero n e)
  I (succ k , e) = - pos (succ k) , II
   where
    II : negsucc n ＝ pos 2 * (- pos (succ k))
    II = negsucc n                ＝⟨ refl                                                ⟩
         - pos (succ n)           ＝⟨ ap (λ z → - pos z) e                                ⟩
         - pos (2 ℕ* succ k)      ＝⟨ ap -_ (pos-multiplication-equiv-to-ℕ 2 (succ k) ⁻¹) ⟩
         - pos 2 * pos (succ k)   ＝⟨ negation-dist-over-mult (pos 2) (pos (succ k)) ⁻¹   ⟩
         pos 2 * (- pos (succ k)) ∎

ℤodd-is-succ-multiple-of-two : (n : ℤ) → ℤodd n → Σ k ꞉ ℤ , n ＝ succℤ (pos 2 * k)
ℤodd-is-succ-multiple-of-two n on = I (ℤeven-is-multiple-of-two (predℤ n) (ℤpred-odd-is-even n on))
 where
  I : Σ k ꞉ ℤ , predℤ n ＝ pos 2 * k → Σ k ꞉ ℤ , n ＝ succℤ (pos 2 * k)
  I (k , e) = k , II
   where
    II : n ＝ succℤ (pos 2 * k)
    II = n                 ＝⟨ succpredℤ n ⁻¹ ⟩
         succℤ (predℤ n)   ＝⟨ ap succℤ e     ⟩
         succℤ (pos 2 * k) ∎

ℤtimes-even-is-even : (m n : ℤ) → ℤeven m → ℤeven (m * n)
ℤtimes-even-is-even m n em = I (ℤeven-or-odd n)
 where
  I : ℤeven n ∔ ℤodd n → ℤeven (m * n)
  I (inl en) = ℤeven*even m n em en
  I (inr on) = ℤeven*odd m n em on

ℤtimes-even-is-even' : (m n : ℤ) → ℤeven n → ℤeven (m * n)
ℤtimes-even-is-even' m n en = transport ℤeven (ℤ*-comm n m) (ℤtimes-even-is-even n m en)

ℤeven-transport : (z : ℤ) → (ez : ℤeven z) (p : ℤeven z ∔ ℤodd z) → p ＝ inl ez
ℤeven-transport z ez (inl ez') = ap inl (ℤeven-is-prop z ez' ez)
ℤeven-transport z ez (inr oz)  = 𝟘-elim (ℤeven-not-odd z ez oz)

ℤodd-transport : (z : ℤ) → (oz : ℤodd z) (p : ℤeven z ∔ ℤodd z) → p ＝ inr oz
ℤodd-transport z oz (inl ez)  = 𝟘-elim (ℤeven-not-odd z ez oz)
ℤodd-transport z oz (inr oz') = ap inr (ℤodd-is-prop z oz' oz)

\end{code}

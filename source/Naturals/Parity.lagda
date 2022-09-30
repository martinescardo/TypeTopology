\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Naturals.Addition
open import Naturals.Multiplication
open import Naturals.Properties
open import UF.Subsingletons

module Naturals.Parity where

even odd : ℕ → 𝓤₀ ̇
even 0        = 𝟙
even (succ n) = odd n
odd 0         = 𝟘
odd (succ n)  = even n

even-not-odd : (n : ℕ) → even n → ¬ odd n
even-not-odd 0               even-n odd-n = odd-n
even-not-odd 1               even-n odd-n = even-n
even-not-odd (succ (succ n)) even-n odd-n = even-not-odd n even-n odd-n

odd-not-even : (n : ℕ) → odd n → ¬ even n
odd-not-even n odd-n even-n = even-not-odd n even-n odd-n

even-is-prop : (n : ℕ) → is-prop (even n)
even-is-prop 0               = 𝟙-is-prop
even-is-prop 1               = 𝟘-is-prop
even-is-prop (succ (succ n)) = even-is-prop n

odd-is-prop : (n : ℕ) → is-prop (odd n)
odd-is-prop 0               = 𝟘-is-prop
odd-is-prop 1               = 𝟙-is-prop
odd-is-prop (succ (succ n)) = odd-is-prop n

even-or-odd : (n : ℕ) → even n ∔ odd n
even-or-odd 0        = inl ⋆
even-or-odd (succ n) = I (even-or-odd n)
 where
  I : even n ∔ odd n → even (succ n) ∔ odd (succ n)
  I (inl even-n) = inr even-n
  I (inr odd-n)  = inl odd-n

even-or-odd-is-prop : (n : ℕ) → is-prop (even n ∔ odd n)
even-or-odd-is-prop n = +-is-prop (even-is-prop n) (odd-is-prop n) (even-not-odd n)

succ-odd-is-even : (n : ℕ) → even n → odd (succ n)
succ-odd-is-even n = id

succ-even-is-odd : (n : ℕ) → odd n → even (succ n)
succ-even-is-odd n = id

odd-succ-succ : (n : ℕ) → odd n → odd (succ (succ n))
odd-succ-succ n = id

odd-succ-succ' : (n : ℕ) → odd (succ (succ n)) → odd n
odd-succ-succ' n = id

even-succ-succ : (n : ℕ) → even n → even (succ (succ n))
even-succ-succ n = id

even-succ-succ' : (n : ℕ) → even (succ (succ n)) → even n
even-succ-succ' n = id

even+even : (n m : ℕ) → even n → even m → even (n + m)
even+even n 0               even-n even-m = even-n
even+even n 1               even-n even-m = 𝟘-elim even-m
even+even n (succ (succ m)) even-n even-m = even+even n m even-n even-m

even+odd : (n m : ℕ) → even n → odd m → odd (n + m)
even+odd n 0               even-n odd-m = 𝟘-elim odd-m
even+odd n 1               even-n odd-m = even-n
even+odd n (succ (succ m)) even-n odd-m = even+odd n m even-n odd-m

odd+even : (n m : ℕ) → odd n → even m → odd (n + m)
odd+even n m odd-n even-m = transport
                             odd
                              (addition-commutativity m n)
                               (even+odd m n even-m odd-n)

odd+odd : (n m : ℕ) → odd n → odd m → even (n + m)
odd+odd n 0               odd-n odd-m = 𝟘-elim odd-m
odd+odd n 1               odd-n odd-m = odd-n
odd+odd n (succ (succ m)) odd-n odd-m = odd+odd n m odd-n odd-m

even*even : (n m : ℕ) → even n → even m → even (n * m)
even*even n 0               even-n even-m = even-m
even*even n 1               even-n even-m = even-n
even*even n (succ (succ m)) even-n even-m = even+even n (n + n * m) even-n I
 where
  IH : even (n * m)
  IH = even*even n m even-n even-m 
  I : even (n + n * m)
  I = even+even n (n * m) even-n IH

odd*odd : (n m : ℕ) → odd n → odd m → odd (n * m)
odd*odd n 0               odd-n odd-m = odd-m
odd*odd n 1               odd-n odd-m = odd-n
odd*odd n (succ (succ m)) odd-n odd-m = odd+even n (n + n * m) odd-n I
 where
  IH : odd (n * m)
  IH = odd*odd n m odd-n odd-m

  I : even (n + n * m)
  I = odd+odd n (n * m) odd-n IH

even*odd : (n m : ℕ) → even n → odd m → even (n * m)
even*odd n 0               even-n odd-m = ⋆
even*odd n 1               even-n odd-m = even-n
even*odd n (succ (succ m)) even-n odd-m = even+even n (n + n * m) even-n I
 where
  IH : even (n * m)
  IH = even*odd n m even-n odd-m
  I : even (n + n * m)
  I = even+even n (n * m) even-n IH

odd*even : (n m : ℕ) → odd n → even m → even (n * m)
odd*even n m odd-n even-m = transport even (mult-commutativity m n) (even*odd m n even-m odd-n)

multiple-of-two-even-lemma : (n k : ℕ) → n ＝ 2 * k → even n
multiple-of-two-even-lemma n 0               e = transport even (e ⁻¹) ⋆
multiple-of-two-even-lemma n 1               e = transport even (e ⁻¹) ⋆
multiple-of-two-even-lemma n (succ (succ k)) e = transport even (e ⁻¹) III
 where
  I : even (2 * k)
  I = multiple-of-two-even-lemma (2 * k) k refl
  II : even (2 + 2 * k)
  II = even+even 2 (2 * k) ⋆ I
  III : even (2 + (2 + 2 * k))
  III = even+even 2 (2 + 2 * k) ⋆ II
  
multiple-of-two-even : (n : ℕ) → Σ k ꞉ ℕ , n ＝ 2 * k → even n
multiple-of-two-even n (k , e) = multiple-of-two-even-lemma n k e

succ-multiple-of-two-odd : (n k : ℕ) → n ＝ succ (2 * k) → odd n
succ-multiple-of-two-odd 0        k e = positive-not-zero (2 * k) (e ⁻¹)
succ-multiple-of-two-odd (succ n) k e = multiple-of-two-even n (k , (succ-lc e))

even-is-multiple-of-two : (n : ℕ) → even n → Σ k ꞉ ℕ , n ＝ 2 * k
even-is-multiple-of-two 0               even-0  = 0 , refl
even-is-multiple-of-two 1               even-1  = 𝟘-elim even-1
even-is-multiple-of-two (succ (succ n)) even-sn = II IH
 where
  IH : Σ k ꞉ ℕ , n ＝ 2 * k
  IH = even-is-multiple-of-two n even-sn

  II : Σ k ꞉ ℕ , n ＝ 2 * k → Σ k ꞉ ℕ , succ (succ n) ＝ 2 * k
  II (k , e) = (succ k) , I
   where
    I : succ (succ n) ＝ 2 * succ k
    I = succ (succ n) ＝⟨ addition-commutativity n 2 ⟩
        2 + n         ＝⟨ ap (2 +_) e                ⟩
        2 + 2 * k     ＝⟨ refl                       ⟩
        2 * succ k    ∎


odd-is-succ-multiple-of-two : (n : ℕ) → odd n → Σ k ꞉ ℕ , n ＝ succ (2 * k)
odd-is-succ-multiple-of-two 0        odd-n = 𝟘-elim odd-n
odd-is-succ-multiple-of-two (succ n) odd-sn = II I 
 where
  I : Σ k ꞉ ℕ , n ＝ 2 * k
  I = even-is-multiple-of-two n odd-sn

  II : Σ k ꞉ ℕ , n ＝ 2 * k → Σ k ꞉ ℕ , succ n ＝ succ (2 * k)
  II (k , e) = k , (ap succ e)

\end{code}

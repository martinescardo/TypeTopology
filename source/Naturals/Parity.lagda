\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Naturals.Addition
open import Naturals.Division
open import Naturals.Double
open import Naturals.Exponentiation
open import Naturals.Multiplication
open import Naturals.Properties
open import UF.Subsingletons


module Naturals.Parity where

even odd : ℕ → 𝓤₀ ̇
even 0        = 𝟙
even (succ n) = odd n
odd 0         = 𝟘
odd (succ n)  = even n

zero-not-odd : (n : ℕ) → odd n → ¬ (n ＝ 0)
zero-not-odd 0        on e = on
zero-not-odd (succ n) on e = positive-not-zero n e

even-is-prop : (n : ℕ) → is-prop (even n)
even-is-prop 0               = 𝟙-is-prop
even-is-prop 1               = 𝟘-is-prop
even-is-prop (succ (succ n)) = even-is-prop n

odd-is-prop : (n : ℕ) → is-prop (odd n)
odd-is-prop 0               = 𝟘-is-prop
odd-is-prop 1               = 𝟙-is-prop
odd-is-prop (succ (succ n)) = odd-is-prop n

even-not-odd : (n : ℕ) → even n → ¬ odd n
even-not-odd 0               even-n odd-n = odd-n
even-not-odd 1               even-n odd-n = even-n
even-not-odd (succ (succ n)) even-n odd-n = even-not-odd n even-n odd-n

odd-not-even : (n : ℕ) → odd n → ¬ even n
odd-not-even n odd-n even-n = even-not-odd n even-n odd-n

even-or-odd : (n : ℕ) → even n ∔ odd n
even-or-odd 0               = inl ⋆
even-or-odd 1               = inr ⋆
even-or-odd (succ (succ n)) = even-or-odd n

even-or-odd-is-prop : (n : ℕ) → is-prop (even n ∔ odd n)
even-or-odd-is-prop n =  γ
 where
  γ : is-prop (even n ∔ odd n)
  γ = +-is-prop (even-is-prop n) (odd-is-prop n) (even-not-odd n)

succ-even-is-odd : (n : ℕ) → even n → odd (succ n)
succ-even-is-odd n = id

succ-odd-is-even : (n : ℕ) → odd n → even (succ n)
succ-odd-is-even n = id

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
odd*even n m odd-n even-m = γ
 where
  γ : even (n * m)
  γ = transport even (mult-commutativity m n) (even*odd m n even-m odd-n)

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

times-even-is-even : (m n  : ℕ) → even m → even (m * n)
times-even-is-even m n em = I (even-or-odd n)
 where
  I : even n ∔ odd n → even (m * n)
  I (inl en) = even*even m n em en
  I (inr on) = even*odd m n em on

times-even-is-even' : (m n  : ℕ) → even n → even (m * n)
times-even-is-even' m n en = γ
 where
  γ : even (m * n)
  γ = transport even (mult-commutativity n m) (times-even-is-even n m en)

only-odd-divides-odd : (d n : ℕ) → odd n → d ∣ n → odd d
only-odd-divides-odd d n on (k , e) = I (even-or-odd d) (even-or-odd k)
 where
  I : even d ∔ odd d → even k ∔ odd k → odd d
  I (inr od) _        = od
  I (inl ed) (inl ek) = 𝟘-elim γ
   where
    en : even n
    en = transport even e (even*even d k ed ek)

    γ : 𝟘
    γ = even-not-odd n en on

  I (inl ed) (inr ok) = 𝟘-elim γ
   where
    en : even n
    en = transport even e (even*odd d k ed ok)

    γ : 𝟘
    γ = even-not-odd n en on

2-exponents-even : (n : ℕ) → even (2^ (succ n))
2-exponents-even 0        = ⋆    -- 2 even
2-exponents-even (succ n) = even*even 2 (2^ (succ n)) ⋆ (2-exponents-even n)

odd-factors-of-2-exponents : (d n : ℕ) → d ∣ 2^ n → odd d → d ＝ 1
odd-factors-of-2-exponents d 0        (k , e) od = left-factor-one d k e
odd-factors-of-2-exponents d (succ n) (k , e) od = Cases (even-or-odd k) γ₁ γ₂
 where
  I : even (2^ (succ n))
  I = 2-exponents-even n

  γ₁ : even k → d ＝ 1
  γ₁ ek = II (even-is-multiple-of-two k ek)
   where
    II : Σ k' ꞉ ℕ , k ＝ 2 * k' → d ＝ 1
    II (k' , e') = odd-factors-of-2-exponents d n γ₃ od
     where
      III : 2 * (d * k') ＝ 2 * 2^ n
      III = 2 * (d * k') ＝⟨ mult-commutativity 2 (d * k')       ⟩
            d * k' * 2   ＝⟨ mult-associativity d k' 2           ⟩
            d * (k' * 2) ＝⟨ ap (d *_) (mult-commutativity k' 2) ⟩
            d * (2 * k') ＝⟨ ap (d *_) (e' ⁻¹)                   ⟩
            d * k        ＝⟨ e                                   ⟩
            2 * 2^ n     ∎

      IV : d * k' ＝ 2^ n
      IV = mult-left-cancellable (d * k') (2^ n) 1 III

      γ₃ : d ∣ 2^ n
      γ₃ = k' , IV

  γ₂ : odd k → d ＝ 1
  γ₂ ok = 𝟘-elim (even-not-odd (2^ (succ n)) I II)
   where
    II : odd (2^ (succ n))
    II = transport odd e (odd*odd d k od ok)

factors-of-2-exponents : (d n : ℕ) → d ∣ 2^ n → (d ＝ 1) ∔ even d
factors-of-2-exponents d n d|2^n = I (even-or-odd d)
 where
  I : even d ∔ odd d → (d ＝ 1) ∔ even d
  I (inl ed) = inr ed
  I (inr od) = inl (odd-factors-of-2-exponents d n d|2^n od)

odd-power-of-two-coprime : (d x n : ℕ) → odd x → d ∣ x → d ∣ 2^ n → d ∣ 1
odd-power-of-two-coprime d x n ox d|x d|2^n = Cases α γ₁ γ₂
 where
  α : (d ＝ 1) ∔ even d
  α = factors-of-2-exponents d n d|2^n

  od : odd d
  od = only-odd-divides-odd d x ox d|x

  γ₁ : d ＝ 1 → d ∣ 1
  γ₁ e = 1 , e

  γ₂ : even d → d ∣ 1
  γ₂ ed = 𝟘-elim (odd-not-even d od ed)

even-transport : (z : ℕ) → (ez : even z) (p : even z ∔ odd z) → p ＝ inl ez
even-transport z ez (inl ez') = ap inl (even-is-prop z ez' ez)
even-transport z ez (inr oz)  = 𝟘-elim (even-not-odd z ez oz)

odd-transport : (z : ℕ) → (oz : odd z) (p : even z ∔ odd z) → p ＝ inr oz
odd-transport z oz (inl ez)  = 𝟘-elim (even-not-odd z ez oz)
odd-transport z oz (inr oz') = ap inr (odd-is-prop z oz' oz)

\end{code}

Sometimes the following definitions and constructions are useful:

\begin{code}

is-even' is-odd' : ℕ → 𝓤₀ ̇
is-even' n = Σ k ꞉ ℕ ,  double k ＝ n
is-odd'  n = Σ k ꞉ ℕ , sdouble k ＝ n

even-or-odd' : (n : ℕ) → is-even' n ∔ is-odd' n
even-or-odd' 0        = inl (0 , refl)
even-or-odd' (succ n) =
 Cases (even-or-odd' n)
  (λ ((k , e) : is-even' n)
              → inr (k , ap succ e))
  (λ ((k , e) : is-odd' n)
              → inl (succ k , ap succ e))

even-not-odd' : (n k : ℕ) → ¬ (double n ＝ sdouble k)
even-not-odd' 0        k e = zero-not-positive (double k) e
even-not-odd' (succ n) k e = even-not-odd' k n ((succ-lc e)⁻¹)

not-even-and-odd' : (n : ℕ) → ¬ (is-even' n × is-odd' n)
not-even-and-odd' n ((k , e) , (k' , e')) =
 even-not-odd' k k'
  (double k   ＝⟨ e ⟩
   n          ＝⟨ e' ⁻¹ ⟩
   sdouble k' ∎)

\end{code}

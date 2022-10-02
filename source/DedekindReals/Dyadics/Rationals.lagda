\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import DedekindReals.Integers.Integers
open import DedekindReals.Integers.Multiplication
open import DedekindReals.Integers.Parity
open import DedekindReals.Rationals.Fractions hiding (_≈_)
open import DedekindReals.Rationals.Multiplication renaming (_*_ to _ℚ*_)
open import DedekindReals.Rationals.Rationals
open import Naturals.Division
open import Naturals.Exponents
open import Naturals.HCF
open import Naturals.Order
open import Naturals.Parity
open import Naturals.Properties
open import Notation.Order
open import UF.Base hiding (_≈_)
open import UF.Miscelanea
open import UF.Subsingletons
open import TypeTopology.DiscreteAndSeparated
open import TypeTopology.SigmaDiscreteAndTotallySeparated 


module DedekindReals.Dyadics.Rationals where

ℤ[1/2]-cond : (z : ℤ) (n : ℕ) → 𝓤₀ ̇
ℤ[1/2]-cond z n = (n ＝ 0) ∔ (n > 0 × ℤodd z)

ℤ[1/2]-cond-is-prop : (z : ℤ) (n : ℕ) → is-prop (ℤ[1/2]-cond z n)
ℤ[1/2]-cond-is-prop z n = +-is-prop ℕ-is-set (×-is-prop (<-is-prop-valued 0 n) (ℤodd-is-prop z)) I
 where
  I : n ＝ 0 → ¬ (0 < n × ℤodd z)
  I n＝0 (0<n , odd-z) = not-less-than-itself 0 (transport (0 <_) n＝0 0<n)

ℤ[1/2]-cond-is-discrete : ((z , n) : ℤ × ℕ) → is-discrete (ℤ[1/2]-cond z n)
ℤ[1/2]-cond-is-discrete (z , n) = +-is-discrete (λ x y → inl (ℕ-is-set x y))
                                   (×-is-discrete (λ x y → inl (<-is-prop-valued 0 n x y))
                                                  (λ x y → inl (ℤodd-is-prop z x y)))
ℤ[1/2] : 𝓤₀ ̇
ℤ[1/2] = Σ (z , n) ꞉ ℤ × ℕ , ℤ[1/2]-cond z n

ℤ[1/2]-is-discrete : is-discrete ℤ[1/2]
ℤ[1/2]-is-discrete = Σ-is-discrete (×-is-discrete ℤ-is-discrete ℕ-is-discrete) ℤ[1/2]-cond-is-discrete

ℤ[1/2]-is-set : is-set ℤ[1/2]
ℤ[1/2]-is-set = discrete-types-are-sets ℤ[1/2]-is-discrete

normalise-pos-lemma : (z : ℤ) (n : ℕ) → ℤ[1/2]
normalise-pos-lemma z 0        = (z , 0) , (inl refl)
normalise-pos-lemma z (succ n) = I (ℤeven-or-odd z)
 where
  I : ℤeven z ∔ ℤodd z → ℤ[1/2]
  I (inr oz) = (z , succ n) , (inr (⋆ , oz))
  I (inl ez) = II (ℤeven-is-multiple-of-two z ez)
   where
    II : Σ k ꞉ ℤ , z ＝ pos 2 * k → ℤ[1/2]
    II (k , e) = normalise-pos-lemma k n

normalise-pos : ℤ × ℕ → ℤ[1/2]
normalise-pos (z , n) = normalise-pos-lemma z n

normalise-neg-lemma : (z : ℤ) (n : ℕ) → ℤ[1/2]
normalise-neg-lemma z 0        = (z * pos 2 , 0) , (inl refl)
normalise-neg-lemma z (succ n) = normalise-neg-lemma (z * pos 2) n

normalise-neg : ℤ × ℕ → ℤ[1/2]
normalise-neg (z , n) = normalise-neg-lemma z n

normalise : ℤ × ℤ → ℤ[1/2]
normalise (z , pos n)     = normalise-pos (z , n)
normalise (z , negsucc n) = normalise-neg (z , n)

0ℤ[1/2] : ℤ[1/2]
0ℤ[1/2] = (pos 0 , 0) , (inl refl)

1ℤ[1/2] : ℤ[1/2]
1ℤ[1/2] = (pos 1 , 0) , (inl refl)

_≈'_ : (x y : ℤ × ℕ) → 𝓤₀ ̇
(x , n) ≈' (y , m) = x * pos (2^ m) ＝ y * pos (2^ n)

_≈_ : (x y : ℤ[1/2]) → 𝓤₀ ̇
(x , _) ≈ (y , _) = x ≈' y

ℤ[1/2]-lt-lemma : (x : ℤ) → (n : ℕ) → ℤodd x → is-in-lowest-terms (x , pred (2^ (succ n)))
ℤ[1/2]-lt-lemma x n ox = (1-divides-all (abs x) , 1-divides-all (succ (pred (2^ (succ n))))) , I
 where
  I : (d : ℕ) → is-common-divisor d (abs x) (succ (pred (2^ (succ n)))) → d ∣ 1
  I d icd-d = III II
   where
    II : is-common-divisor d (abs x) (2^ (succ n))
    II = transport (λ - → is-common-divisor d (abs x) -) (succ-pred' (2^ (succ n)) (exponents-not-zero (succ n))) icd-d
    III : is-common-divisor d (abs x) (2^ (succ n)) → d ∣ 1
    III (d|x , d|2^sn) = odd-power-of-two-coprime d (abs x) (succ n) ox d|x d|2^sn

ℤ[1/2]-to-ℚ : ℤ[1/2] → ℚ
ℤ[1/2]-to-ℚ ((x , n)      , inl n＝0)       = (x , 0) , (denom-zero-lt x)
ℤ[1/2]-to-ℚ ((x , 0)      , inr (0<n , ox)) = 𝟘-elim 0<n
ℤ[1/2]-to-ℚ ((x , succ n) , inr (0<n , ox)) = (x , pred (2^ (succ n))) , (ℤ[1/2]-lt-lemma x n ox)


{-
≈-to-＝-lemma : ((x , m) (y , n) : ℤ × ℕ)
              → (x , m) ≈' (y , n)
              → ℤ[1/2]-cond x m
              → ℤ[1/2]-cond y n
              → (x , m) ＝ (y , n)
≈-to-＝-lemma (x , m) (y , n) e (inl m＝0)       (inl n＝0)       = to-×-＝ I (m＝0 ∙ n＝0 ⁻¹)
 where
  I : x ＝ y
  I = x              ＝⟨ refl                                  ⟩
      x * pos (2^ 0) ＝⟨ ap (λ z → x * (pos (2^ z))) (n＝0 ⁻¹) ⟩
      x * pos (2^ n) ＝⟨ e                                     ⟩
      y * pos (2^ m) ＝⟨ ap (λ z → y * (pos (2^ z))) m＝0      ⟩
      y * pos (2^ 0) ＝⟨ refl                                  ⟩
      y              ∎
≈-to-＝-lemma (x , m) (y , n) e (inl m＝0)       (inr (n>0 , on)) = 𝟘-elim (ℤodd-not-even y on {!!})
 where
  I : ℤeven {!!}
  I = ℤmultiple-of-two-even {!!} {!!}
  II : y ＝ x * pos (2^ n)
  II = y              ＝⟨ refl                                ⟩
       y * pos (2^ 0) ＝⟨ ap (λ z → y * pos (2^ z)) (m＝0 ⁻¹) ⟩
       y * pos (2^ m) ＝⟨ e ⁻¹                                ⟩
       x * pos (2^ n) ∎
  III : ℤeven y
  III = transport ℤeven {!!} I
≈-to-＝-lemma (x , m) (y , n) e (inr (m>0 , om)) (inl n＝0)       = {!!}
≈-to-＝-lemma (x , m) (y , n) e (inr (m>0 , om)) (inr (n>0 , on)) = {!!}

≈-to-＝ : (x y : ℤ[1/2]) → x ≈ y → x ＝ y
≈-to-＝ ((x , n) , p) ((y , m) , q) eq =
 to-subtype-＝ (λ (x , n) → ℤ[1/2]-cond-is-prop x n) (≈-to-＝-lemma (x , n) (y , m) eq p q)
-}

\end{code}

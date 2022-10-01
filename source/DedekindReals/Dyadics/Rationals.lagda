\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import DedekindReals.Integers.Integers
open import DedekindReals.Integers.Multiplication
open import DedekindReals.Integers.Parity
open import Naturals.Parity
open import Naturals.Order
open import Notation.Order
open import UF.Base
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

\end{code}

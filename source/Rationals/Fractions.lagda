Andrew Sneap - November 2021

In this file I define the free rationals. They are rationals they may
not be in the lowest terms, with (a , b) : ℤ × ℕ were ℤ is the
numerator, and b represents a denominator of b+1, ruling out the
possibility of a zero-denominator.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Integers.Abs
open import Integers.HCF
open import Integers.Multiplication
open import Integers.Order
open import Integers.Type
open import Naturals.Division
open import Naturals.HCF
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Naturals.Properties
open import TypeTopology.SigmaDiscrete
open import UF.Base hiding (_≈_)
open import UF.DiscreteAndSeparated
open import UF.Sets
open import UF.Subsingletons

module Rationals.Fractions where

𝔽 : 𝓤₀ ̇
𝔽 = ℤ × ℕ

is-in-lowest-terms : 𝔽 → 𝓤₀ ̇
is-in-lowest-terms (x , y) = coprime' (abs x) (succ y)

is-in-lowest-terms' : 𝔽 → 𝓤₀ ̇
is-in-lowest-terms' (x , y) = coprime (abs x) (succ y)

denom-zero-lt : (x : ℤ) → is-in-lowest-terms (x , 0)
denom-zero-lt x = γ
 where
  I : (d : ℕ) → is-common-divisor d (abs x) 1 → d ∣ 1
  I d (_ , d-divides-1) = d-divides-1

  II : coprime (abs x) 1
  II = ((1-divides-all (abs x)) , 1-divides-all 1) , I

  γ : coprime' (abs x) 1
  γ = coprime-to-coprime' (abs x) 1 II

is-in-lowest-terms-is-prop : (q : 𝔽) → is-prop (is-in-lowest-terms q)
is-in-lowest-terms-is-prop (x , y) = coprime'-is-prop (abs x) (succ y)

𝔽-is-discrete : is-discrete 𝔽
𝔽-is-discrete = Σ-is-discrete ℤ-is-discrete (λ _ → ℕ-is-discrete)

𝔽-is-set : is-set 𝔽
𝔽-is-set = discrete-types-are-sets 𝔽-is-discrete

_≈_ : (p q : 𝔽) → 𝓤₀ ̇
(x , a) ≈ (y , b) = x * pos (succ b) ＝ y * pos (succ a)

≈-refl : (q : 𝔽) → q ≈ q
≈-refl q = refl

≈-sym : (p q : 𝔽) → p ≈ q → q ≈ p
≈-sym p q e = e ⁻¹

≈-trans : (p q r : 𝔽) → p ≈ q → q ≈ r → p ≈ r
≈-trans (x , a) (y , b) (z , c) e₁ e₂ = conclusion
 where
  a' = pos (succ a)
  b' = pos (succ b)
  c' = pos (succ c)

  I : b' * (x * c') ＝ b' * (z * a')
  I = b' * (x * c') ＝⟨ ℤ*-assoc b' x c' ⁻¹           ⟩
      b' * x * c'   ＝⟨ ap (_* c') (ℤ*-comm b' x)     ⟩
      x * b' * c'   ＝⟨ ap (_* c') e₁                 ⟩
      y * a' * c'   ＝⟨ ap (_* c') (ℤ*-comm y a')     ⟩
      a' * y * c'   ＝⟨ ℤ*-assoc a' y c'              ⟩
      a' * (y * c') ＝⟨ ap (a' *_) e₂                 ⟩
      a' * (z * b') ＝⟨ ℤ-mult-rearrangement' z b' a' ⟩
      b' * (z * a') ∎

  conclusion : (x , a) ≈ (z , c)
  conclusion = ℤ-mult-left-cancellable (x * c') (z * a') b' id I

equiv-with-lowest-terms-is-equal : (a b : 𝔽)
                                 → a ≈ b
                                 → is-in-lowest-terms a
                                 → is-in-lowest-terms b
                                 → a ＝ b
equiv-with-lowest-terms-is-equal (x , a) (y , b) e lt₁ lt₂ = γ
 where
  α : coprime (abs x) (succ a)
  α = coprime'-to-coprime (abs x) (succ a) lt₁

  β : coprime (abs y) (succ b)
  β = coprime'-to-coprime (abs y) (succ b) lt₂

  δ : abs x ℕ* succ b ＝ abs y ℕ* succ a
  δ = abs x ℕ* abs (pos (succ b)) ＝⟨ abs-over-mult x (pos (succ b)) ⁻¹ ⟩
      abs (x * pos (succ b))      ＝⟨ ap abs e                          ⟩
      abs (y * pos (succ a))      ＝⟨ abs-over-mult y (pos (succ a))    ⟩
      abs y ℕ* abs (pos (succ a)) ∎

  I : succ a ℕ* abs y ＝ abs x ℕ* succ b
  I = succ a ℕ* abs y ＝⟨ mult-commutativity (succ a) (abs y) ⟩
      abs y ℕ* succ a ＝⟨ δ ⁻¹                                ⟩
      abs x ℕ* succ b ∎

  II : (succ a) ∣ (abs x) ℕ* (succ b)
  II = abs y , I

  III : succ b ℕ* abs x ＝ abs y ℕ* succ a
  III = succ b ℕ* abs x ＝⟨ mult-commutativity (succ b) (abs x) ⟩
        abs x ℕ* succ b ＝⟨ δ                                   ⟩
        abs y ℕ* succ a ∎

  IV : succ b ∣ abs y ℕ* succ a
  IV = abs x , III

  V : coprime (succ a) (abs x)
  V = hcf-comm (abs x) (succ a) 1 α

  VI : coprime (succ b) (abs y)
  VI = hcf-comm (abs y) (succ b) 1 β

  a-divides-b : succ a ∣ succ b
  a-divides-b = coprime-with-division (succ a) (abs x) (succ b) V II

  b-divides-a : succ b ∣ succ a
  b-divides-a = coprime-with-division (succ b) (abs y) (succ a) VI IV

  γ₁ : a ＝ b
  γ₁ = succ-lc (∣-anti (succ a) (succ b) a-divides-b b-divides-a)

  e'' : x * pos (succ a) ＝ y * pos (succ a)
  e'' = x * pos (succ a) ＝⟨ ap (x *_) (ap pos (ap succ γ₁)) ⟩
        x * pos (succ b) ＝⟨ e                               ⟩
        y * pos (succ a) ∎

  γ₂ : x ＝ y
  γ₂ = ℤ-mult-right-cancellable x y (pos (succ a)) id e''

  γ : x , a ＝ y , b
  γ = to-×-＝ γ₂ γ₁

open import Notation.CanonicalMap

ℤ-to-𝔽 : ℤ → 𝔽
ℤ-to-𝔽 z = z , 0

instance
 canonical-map-ℤ-to-𝔽 : Canonical-Map ℤ 𝔽
 ι {{canonical-map-ℤ-to-𝔽}} = ℤ-to-𝔽

ℕ-to-𝔽 : ℕ → 𝔽
ℕ-to-𝔽 n = ι (ι n)

instance
 canonical-map-ℕ-to-𝔽 : Canonical-Map ℕ 𝔽
 ι {{canonical-map-ℕ-to-𝔽}} = ℕ-to-𝔽

\end{code}

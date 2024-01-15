Andrew Sneap - 19 April 2023 - 27 April 2023

This file defines various functions on real number, using the extension defined
in DedekindReals.Extension.

By the uniformly continuous extension theorem, it is also proved that these
functions are indeed extensions, and are uniformly continuous.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Abs
open import Rationals.Addition
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module DedekindReals.Functions
  (fe : Fun-Ext)
  (pe : Prop-Ext)
  (pt : propositional-truncations-exist)
 where

open PropositionalTruncation pt

open import DedekindReals.Properties fe pe pt
open import DedekindReals.Type fe pe pt
open import DedekindReals.Extension fe pe pt

\end{code}

The following examples extends the increment function on rationals to a function
on reals. The function which increments by one is clearly uniformly continuous
(and this is proved below). Hence we simply apply the extension, and by the
extension theorem we see that ℝ-incr agrees with ℚ-incr for every rational
input.

\begin{code}

ℚ-incr : ℚ → ℚ
ℚ-incr q = q + 1ℚ

ℚ-incr-uc : ℚ-is-uniformly-continuous ℚ-incr
ℚ-incr-uc (ε , 0<ε) = (ε , 0<ε) , γ
 where
  γ : (x x₀ : ℚ) → x ∈𝐁 (ε , 0<ε) ⦅ x₀ ⦆ → ℚ-incr x ∈𝐁 (ε , 0<ε) ⦅ ℚ-incr x₀ ⦆
  γ x x₀ (l₁ , l₂) = γ₁ , γ₂
   where
    I : x + 1ℚ < x₀ + ε + 1ℚ
    I = ℚ<-addition-preserves-order x (x₀ + ε) 1ℚ l₂

    II : x₀ - ε + 1ℚ < x + 1ℚ
    II = ℚ<-addition-preserves-order (x₀ - ε) x 1ℚ l₁

    γ₁ : x₀ + 1ℚ - ε < x + 1ℚ
    γ₁ = transport (_< x + 1ℚ) (ℚ+-rearrange x₀ (- ε) 1ℚ) II

    γ₂ : x + 1ℚ < x₀ + 1ℚ + ε
    γ₂ = transport (x + 1ℚ <_) (ℚ+-rearrange x₀ ε 1ℚ) I

ℝ-incr : ℝ → ℝ
ℝ-incr = extend ℚ-incr ℚ-incr-uc

ℝ-incr-agrees-with-ℚ-incr : (q : ℚ) → ℝ-incr (ι q) ＝ ι (ℚ-incr q)
ℝ-incr-agrees-with-ℚ-incr = extend-is-extension ℚ-incr ℚ-incr-uc

ℝ-incr-is-uc : ℝ-is-uniformly-continuous ℝ-incr
ℝ-incr-is-uc = extensions-uc ℚ-incr ℚ-incr-uc

ℚ-neg-is-uc : ℚ-is-uniformly-continuous (-_)
ℚ-neg-is-uc (ε , 0<ε) = (ε , 0<ε) , γ
 where
  γ : (x x₀ : ℚ) → x ∈𝐁 ε , 0<ε ⦅ x₀ ⦆ → (- x) ∈𝐁 ε , 0<ε ⦅ - x₀ ⦆
  γ x x₀ (l₁ , l₂) = l₃ , l₄
   where
    l₃ : (- x₀) - ε < - x
    l₃ = ℚ<-swap-right-add x x₀ ε l₂

    l₄ : - x < (- x₀) + ε
    l₄ = ℚ<-swap-left-neg x₀ ε x l₁

\end{code}

Also given is negation of reals, and the absolute value of reals.

\begin{code}

ℝ-_ : ℝ → ℝ
ℝ-_ = extend -_ ℚ-neg-is-uc

ℝ-neg-agrees-with-ℚ : (q : ℚ) → ℝ- (ι q) ＝ ι (- q)
ℝ-neg-agrees-with-ℚ = extend-is-extension -_ ℚ-neg-is-uc

ℝ-neg-is-uc : ℝ-is-uniformly-continuous ℝ-_
ℝ-neg-is-uc = extensions-uc -_ ℚ-neg-is-uc

abs-uc : ℚ-is-uniformly-continuous abs
abs-uc (ε , 0<ε) = (ε , 0<ε) , γ
 where
  γ : (x x₀ : ℚ) → x ∈𝐁 ε , 0<ε ⦅ x₀ ⦆ → abs x ∈𝐁 ε , 0<ε ⦅ abs x₀ ⦆
  γ x x₀ (l₁ , l₂) = γ' (ℚ-abs-inverse x) (ℚ-abs-inverse x₀)
   where
    I : (- x₀) - ε < - x
    I = ℚ<-swap-right-add x x₀ ε l₂

    II : - x < (- x₀) + ε
    II = ℚ<-swap-left-neg x₀ ε x l₁

    γ' : (abs x ＝ x) ∔ (abs x ＝ - x)
       → (abs x₀ ＝ x₀) ∔ (abs x₀ ＝ - x₀)
       → abs x ∈𝐁 ε , 0<ε ⦅ abs x₀ ⦆
    γ' (inl e₁) (inl e₂) = l₃ , l₄
     where
      l₃ : abs x₀ - ε < abs x
      l₃ = transport₂ (λ a b → a - ε < b) (e₂ ⁻¹) (e₁ ⁻¹) l₁

      l₄ : abs x < abs x₀ + ε
      l₄ = transport₂ (λ a b → b < a + ε) (e₂ ⁻¹) (e₁ ⁻¹) l₂

    γ' (inl e₁) (inr e₂) = l₃ , l₄
     where
      III : abs x₀ - ε < - abs x
      III = transport₂ (λ a b → a - ε < - b) (e₂ ⁻¹) (e₁ ⁻¹) I

      l₃ : abs x₀ - ε < abs x
      l₃ = ℚ<-≤-trans (abs x₀ - ε) (- abs x) (abs x) III (ℚ≤-abs-neg x)

      IV : abs x < x₀ + ε
      IV = transport (_< x₀ + ε) (e₁ ⁻¹) l₂

      V : x₀ + ε ≤ abs x₀ + ε
      V = ℚ≤-addition-preserves-order x₀ (abs x₀) ε (ℚ≤-abs-all x₀)

      l₄ : abs x <ℚ abs x₀ + ε
      l₄ = ℚ<-≤-trans (abs x) (x₀ + ε) (abs x₀ + ε) IV V

    γ' (inr e₁) (inl e₂) = l₃ , l₄
     where
      III : abs x₀ - ε < x
      III = transport (λ a → a - ε < x) (e₂ ⁻¹) l₁

      l₃ : abs x₀ - ε < abs x
      l₃ = ℚ<-≤-trans (abs x₀ - ε) x (abs x) III (ℚ≤-abs-all x)

      IV : abs x < (- abs x₀) + ε
      IV = transport₂ (λ a b → b < (- a) + ε) (e₂ ⁻¹) (e₁ ⁻¹) II

      V : (- abs x₀) + ε ≤ abs x₀ + ε
      V = ℚ≤-addition-preserves-order (- abs x₀) (abs x₀) ε (ℚ≤-abs-neg x₀)

      l₄ : abs x < abs x₀ + ε
      l₄ = ℚ<-≤-trans (abs x) ((- abs x₀) + ε) (abs x₀ + ε) IV V

    γ' (inr e₁) (inr e₂) = l₃ , l₄
     where
      l₃ : abs x₀ - ε < abs x
      l₃ = transport₂ (λ a b → a - ε < b) (e₂ ⁻¹) (e₁ ⁻¹) I

      l₄ : abs x < abs x₀ + ε
      l₄ = transport₂ (λ a b → b < a + ε) (e₂ ⁻¹) (e₁ ⁻¹) II

ℝ-abs : ℝ → ℝ
ℝ-abs = extend abs abs-uc

ℝ-abs-agrees-with-ℚ-abs : (q : ℚ) → ℝ-abs (ι q) ＝ ι (abs q)
ℝ-abs-agrees-with-ℚ-abs = extend-is-extension abs abs-uc

ℝ-abs-uc : ℝ-is-uniformly-continuous ℝ-abs
ℝ-abs-uc = extensions-uc abs abs-uc

\end{code}

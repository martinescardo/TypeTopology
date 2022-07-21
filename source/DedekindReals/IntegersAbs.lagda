Andrew Sneap

In this file I define absolute values of integers and some properties
of abs, along with positive and negative properties of integers.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan renaming (_+_ to _∔_) --TypeTopology

open import TypeTopology.DiscreteAndSeparated -- TypeTopology
open import Naturals.Properties --TypeTopology
open import UF.Miscelanea -- TypeTopology
open import UF.Subsingletons --TypeTopology
-- open import MLTT.Unit-Properties -- TypeTopology

open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import DedekindReals.IntegersMultiplication
open import DedekindReals.IntegersNegation
open import DedekindReals.IntegersAddition
open import DedekindReals.IntegersB

module DedekindReals.IntegersAbs where

absℤ : ℤ → ℤ
absℤ (pos x)     = pos x
absℤ (negsucc x) = pos (succ x)

abs-removes-neg-sign : (x : ℤ) → abs x ＝ abs (- x)
abs-removes-neg-sign (pos zero)     = refl
abs-removes-neg-sign (pos (succ x)) = refl
abs-removes-neg-sign (negsucc x)    = refl

absℤ-removes-neg-sign : (x : ℤ) → absℤ x ＝ absℤ (- x)
absℤ-removes-neg-sign (pos zero)     = refl
absℤ-removes-neg-sign (pos (succ x)) = refl
absℤ-removes-neg-sign (negsucc x)    = refl

abs-over-mult : (a b : ℤ) → abs (a * b) ＝ abs a ℕ* abs b
abs-over-mult (pos x) (pos b) = I
 where
  I : abs (pos x * pos b) ＝ abs (pos x) ℕ* abs (pos b)
  I = abs (pos x * pos b)        ＝⟨ ap abs (pos-multiplication-equiv-to-ℕ x b) ⟩
      abs (pos (x ℕ* b))         ＝⟨ refl ⟩
      abs (pos x) ℕ* abs (pos b) ∎
abs-over-mult (pos zero) (negsucc b) = I
 where
  I : abs (pos zero * negsucc b) ＝ abs (pos zero) ℕ* abs (negsucc b)
  I = abs (pos zero * negsucc b) ＝⟨ ap abs (ℤ-zero-left-base (negsucc b)) ⟩
      abs (pos 0)                ＝⟨ zero-left-base (abs (negsucc b)) ⁻¹ ⟩
      abs (pos zero) ℕ* abs (negsucc b) ∎
abs-over-mult (pos (succ x)) (negsucc b) = I
 where
  I : abs (pos (succ x) * negsucc b) ＝ abs (pos (succ x)) ℕ* abs (negsucc b)
  I = abs (pos (succ x) * negsucc b)           ＝⟨ ap abs (subtraction-dist-over-mult (pos (succ x)) (pos (succ b))) ⟩
      abs (- ((pos (succ x) * pos (succ b))))  ＝⟨ ap (λ z → (abs (- z))) (pos-multiplication-equiv-to-ℕ (succ x) (succ b)) ⟩
      abs (- pos (succ x ℕ* succ b))           ＝⟨ abs-removes-neg-sign ( pos (succ x ℕ* succ b)) ⁻¹ ⟩
      abs (pos (succ x ℕ* succ b))             ＝⟨ refl ⟩
      succ x ℕ* succ b                         ＝⟨ refl ⟩
      abs (pos (succ x)) ℕ* abs (negsucc b)    ∎
abs-over-mult (negsucc x) (pos b) = I
 where
  I : abs (negsucc x * pos b) ＝ abs (negsucc x) ℕ* abs (pos b)
  I = abs (negsucc x * pos b)        ＝⟨ ap abs (subtraction-dist-over-mult' (pos (succ x)) (pos b)) ⟩
      abs (- pos (succ x) * pos b)   ＝⟨ ap (λ z → abs (- z)) (pos-multiplication-equiv-to-ℕ (succ x) b) ⟩
      abs (- pos (succ x ℕ* b))      ＝⟨ abs-removes-neg-sign (pos (succ x ℕ* b)) ⁻¹ ⟩
      (succ x) ℕ* b                  ＝⟨ refl ⟩
      abs (negsucc x) ℕ* abs (pos b) ∎
abs-over-mult (negsucc x) (negsucc b) = I
 where
  I : abs (negsucc x * negsucc b) ＝ abs (negsucc x) ℕ* abs (negsucc b)
  I = abs (negsucc x * negsucc b)               ＝⟨ ap abs (subtraction-dist-over-mult (negsucc x) (pos (succ b))) ⟩
      abs (- negsucc x * pos (succ b) )         ＝⟨ ap (λ z → abs (- z)) (subtraction-dist-over-mult' (pos (succ x)) (pos (succ b))) ⟩
      abs (- (- pos (succ x) * pos (succ b)))   ＝⟨ ap abs (minus-minus-is-plus (pos (succ x) * pos (succ b))) ⟩
      abs (pos (succ x) * pos (succ b))         ＝⟨ ap abs (pos-multiplication-equiv-to-ℕ (succ x) (succ b)) ⟩
      (succ x) ℕ* (succ b)                      ＝⟨ refl ⟩
      abs (negsucc x) ℕ* abs (negsucc b)       ∎

pos-abs-is-equal : (x : ℕ) → absℤ (pos x) ＝ pos x
pos-abs-is-equal x = refl

abs-over-mult' : (x y : ℤ) → absℤ (x * y) ＝ absℤ x * absℤ y
abs-over-mult' (pos x) (pos y) = I
 where
  I : absℤ (pos x * pos y) ＝ absℤ (pos x) * absℤ (pos y)
  I = absℤ (pos x * pos y) ＝⟨ ap absℤ (pos-multiplication-equiv-to-ℕ x y) ⟩
      absℤ (pos (x ℕ* y))  ＝⟨ by-definition ⟩
      pos (x ℕ* y)         ＝⟨ pos-multiplication-equiv-to-ℕ x y ⁻¹ ⟩
      pos x * pos y        ＝⟨ by-definition ⟩
      absℤ (pos x) * absℤ (pos y) ∎
abs-over-mult' (pos x) (negsucc y) = I
 where
  I : absℤ (pos x * negsucc y) ＝ absℤ (pos x) * absℤ (negsucc y)
  I = absℤ (pos x * negsucc y)        ＝⟨ ap absℤ (subtraction-dist-over-mult (pos x) (pos (succ y))) ⟩
      absℤ (- pos x * pos (succ y))   ＝⟨ ap (λ z → absℤ (- z)) (pos-multiplication-equiv-to-ℕ x (succ y)) ⟩
      absℤ (- pos (x ℕ* succ y))      ＝⟨ absℤ-removes-neg-sign (pos (x ℕ* succ y)) ⁻¹ ⟩
      absℤ (pos (x ℕ* succ y))        ＝⟨ by-definition ⟩
      pos (x ℕ* succ y)               ＝⟨ pos-multiplication-equiv-to-ℕ x (succ y) ⁻¹ ⟩
      pos x * pos (succ y)            ＝⟨ by-definition ⟩
      absℤ (pos x) * absℤ (negsucc y) ∎
abs-over-mult' (negsucc x) (pos y) = I
 where
  I : absℤ (negsucc x * pos y) ＝ absℤ (negsucc x) * absℤ (pos y)
  I = absℤ (negsucc x * pos y)      ＝⟨ ap absℤ (ℤ*-comm (negsucc x) (pos y)) ⟩
      absℤ (pos y * negsucc x)      ＝⟨ ap absℤ (subtraction-dist-over-mult (pos y) (pos (succ x))) ⟩
      absℤ (- pos y * pos (succ x)) ＝⟨ ap (λ z → absℤ (- z)) (pos-multiplication-equiv-to-ℕ y (succ x)) ⟩
      absℤ (- pos (y ℕ* succ x))    ＝⟨ absℤ-removes-neg-sign (pos (y ℕ* succ x)) ⁻¹ ⟩
      absℤ (pos (y ℕ* succ x))      ＝⟨ by-definition ⟩
      pos (y ℕ* succ x)             ＝⟨ pos-multiplication-equiv-to-ℕ y (succ x) ⁻¹ ⟩
      pos y * pos (succ x)          ＝⟨ ℤ*-comm (pos y) (pos (succ x)) ⟩
      pos (succ x) * pos y          ＝⟨ by-definition ⟩ 
      absℤ (negsucc x) * absℤ (pos y) ∎
abs-over-mult' (negsucc x) (negsucc y) = I
 where
  I : absℤ (negsucc x * negsucc y) ＝ absℤ (negsucc x) * absℤ (negsucc y)
  I = absℤ (negsucc x * negsucc y)        ＝⟨ ap absℤ (minus-times-minus-is-positive (pos (succ x)) (pos (succ y))) ⟩
      absℤ (pos (succ x) * pos (succ y))  ＝⟨ ap absℤ (pos-multiplication-equiv-to-ℕ (succ x) (succ y)) ⟩
      absℤ (pos (succ x ℕ* succ y))       ＝⟨ by-definition ⟩
      pos (succ x ℕ* succ y)              ＝⟨ pos-multiplication-equiv-to-ℕ (succ x) (succ y) ⁻¹ ⟩
      pos (succ x) * pos (succ y)         ＝⟨ by-definition ⟩
      absℤ (negsucc x) * absℤ (negsucc y) ∎

gtz₀ : (x : ℤ) → (y : ℕ) → is-pos-succ x → is-pos-succ (pos y) → is-pos-succ (x + (pos y))
gtz₀ x = induction base step
 where
  base : is-pos-succ x
       → is-pos-succ (pos 0)
       → is-pos-succ (x + pos 0)
  base l r = 𝟘-elim r

  step : (k : ℕ)
       → (is-pos-succ x → is-pos-succ (pos k) → is-pos-succ (x + pos k))
       → is-pos-succ x
       → is-pos-succ (pos (succ k))
       → is-pos-succ (x + pos (succ k))
  step 0        IH l r = is-pos-succ-succℤ x l
  step (succ k) IH l r = is-pos-succ-succℤ (x + pos (succ k)) (IH l r)

is-pos-succ-trans : (x y : ℤ) → is-pos-succ x → is-pos-succ y → is-pos-succ (x + y)
is-pos-succ-trans x (pos y)         = gtz₀ x y
is-pos-succ-trans x (negsucc y) l r = 𝟘-elim r

gtzmt₀ : (x : ℤ) → (y : ℕ) → is-pos-succ x → is-pos-succ (pos y) → is-pos-succ (x * pos y)
gtzmt₀ x = induction base step
 where
  base : is-pos-succ x → is-pos-succ (pos 0) → is-pos-succ (x * pos 0)
  base l r = 𝟘-elim r

  step : (k : ℕ)
       → (is-pos-succ x → is-pos-succ (pos k) → is-pos-succ (x * pos k))
       → is-pos-succ x
       → is-pos-succ (pos (succ k))
       → is-pos-succ (x * pos (succ k))
  step zero IH l r = l
  step (succ k) IH l r = is-pos-succ-trans x (x * pos (succ k)) l (IH l r)

is-pos-succ-mult-trans : (x y : ℤ) → is-pos-succ x → is-pos-succ y → is-pos-succ (x * y)
is-pos-succ-mult-trans x (negsucc y) l r = 𝟘-elim r
is-pos-succ-mult-trans x (pos y)     l r = gtzmt₀ x y l r

{-
ℤ-not-equal-to-succ : (x : ℤ) → ¬ (x ＝ succℤ x)
ℤ-not-equal-to-succ = ℤ-induction base step₁ step₂
 where
  base : ¬ (pos 0 ＝ succℤ (pos 0))
  base e = pos-int-not-zero 0 (e ⁻¹)
  step₁ : (k : ℤ) → ¬ (k ＝ succℤ k) → ¬ (succℤ k ＝ succℤ (succℤ k))
  step₁ k IH e = IH II
   where
    I : predℤ (succℤ k) ＝ predℤ (succℤ (succℤ k))
    I = ap predℤ e
    II : k ＝ succℤ k
    II = k                       ＝⟨ predsuccℤ k ⁻¹ ⟩
         predℤ (succℤ k)         ＝⟨ I ⟩
         predℤ (succℤ (succℤ k)) ＝⟨ predsuccℤ (succℤ k) ⟩
         succℤ k ∎
  step₂ : (k : ℤ) → ¬ (succℤ k ＝ succℤ (succℤ k)) → ¬ (k ＝ succℤ k)
  step₂ k IH e = IH (ap succℤ e)
-}

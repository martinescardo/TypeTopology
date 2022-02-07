Andrew Sneap - 26th November 2021

In this file I define absolute values of integers and some properties of abs, along with positive and negative properties of integers.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import DiscreteAndSeparated -- TypeTopology
open import NaturalNumbers-Properties --TypeTopology
open import UF-Miscelanea -- TypeTopology
open import UF-Subsingletons --TypeTopology
open import Unit-Properties -- TypeTopology

open import NaturalsMultiplication renaming (_*_ to _ℕ*_)
open import IntegersMultiplication
open import IntegersNegation
open import IntegersAddition
open import IntegersB

module IntegersAbs where

abs : ℤ → ℕ
abs (pos x)     = x
abs (negsucc x) = succ x

absℤ : ℤ → ℤ
absℤ (pos x)     = pos x
absℤ (negsucc x) = pos (succ x)

pos-lc : {x y : ℕ} → pos x ≡ pos y → x ≡ y
pos-lc = ap abs

negsucc-lc : {x y : ℕ} → negsucc x ≡ negsucc y → x ≡ y
negsucc-lc {x} {y} p = succ-lc (ap abs p)

positive : ℤ → 𝓤₀ ̇
positive (pos x)     = 𝟙
positive (negsucc x) = 𝟘

negative : ℤ → 𝓤₀ ̇
negative (pos x)     = 𝟘
negative (negsucc x) = 𝟙

is-zero : ℤ → 𝓤₀ ̇
is-zero (pos 0)        = 𝟙
is-zero (pos (succ x)) = 𝟘
is-zero (negsucc x)    = 𝟘

not-zero : ℤ → 𝓤₀ ̇
not-zero z = ¬ (is-zero z)

greater-than-zero : ℤ → 𝓤₀ ̇
greater-than-zero (pos 0)        = 𝟘
greater-than-zero (pos (succ z)) = 𝟙
greater-than-zero (negsucc z)    = 𝟘

pos-not-negative : {x y : ℕ} → pos x ≢ negsucc y
pos-not-negative p = 𝟙-is-not-𝟘 (ap positive p)

neg-not-positive : {x y : ℕ} → negsucc x ≢ pos y
neg-not-positive p = pos-not-negative (p ⁻¹)

pos-int-not-zero : (x : ℕ) → pos (succ x) ≢ pos 0
pos-int-not-zero x p = positive-not-zero x (pos-lc p)

neg-int-not-zero : (x : ℕ) → negsucc x ≢ pos 0
neg-int-not-zero x p = positive-not-zero x (ap abs p)

ℤ-is-discrete : is-discrete ℤ
ℤ-is-discrete (pos x) (pos y) = f (ℕ-is-discrete x y)
  where
    f : (x ≡ y) ∔ ¬ (x ≡ y) → (pos x ≡ pos y) ∔ ¬ (pos x ≡ pos y)
    f (inl z) = inl (ap pos z)
    f (inr z) = inr (λ k → z (pos-lc k))
ℤ-is-discrete (pos x)     (negsucc y) = inr pos-not-negative
ℤ-is-discrete (negsucc x) (pos y)     = inr neg-not-positive
ℤ-is-discrete (negsucc x) (negsucc y) = f (ℕ-is-discrete x y)
  where
    f : (x ≡ y) ∔ ¬ (x ≡ y) → decidable (negsucc x ≡ negsucc y)
    f (inl z) = inl (ap negsucc z)
    f (inr z) = inr (λ k → z (negsucc-lc k) )

ℤ-is-set : is-set ℤ
ℤ-is-set = discrete-types-are-sets ℤ-is-discrete

abs-removes-neg-sign : (x : ℤ) → abs x ≡ abs (- x)
abs-removes-neg-sign (pos zero)     = refl
abs-removes-neg-sign (pos (succ x)) = refl
abs-removes-neg-sign (negsucc x)    = refl

absℤ-removes-neg-sign : (x : ℤ) → absℤ x ≡ absℤ (- x)
absℤ-removes-neg-sign (pos zero)     = refl
absℤ-removes-neg-sign (pos (succ x)) = refl
absℤ-removes-neg-sign (negsucc x)    = refl

abs-over-mult : (a b : ℤ) → abs (a * b) ≡ abs a ℕ* abs b
abs-over-mult (pos x) (pos b) = I
 where
  I : abs (pos x * pos b) ≡ abs (pos x) ℕ* abs (pos b)
  I = abs (pos x * pos b)        ≡⟨ ap abs (pos-multiplication-equiv-to-ℕ x b) ⟩
      abs (pos (x ℕ* b))         ≡⟨ refl ⟩
      abs (pos x) ℕ* abs (pos b) ∎
abs-over-mult (pos zero) (negsucc b) = I
 where
  I : abs (pos zero * negsucc b) ≡ abs (pos zero) ℕ* abs (negsucc b)
  I = abs (pos zero * negsucc b) ≡⟨ ap abs (ℤ-zero-left-is-zero (negsucc b)) ⟩
      abs (pos 0)                ≡⟨ zero-left-is-zero (abs (negsucc b)) ⁻¹ ⟩
      abs (pos zero) ℕ* abs (negsucc b) ∎
abs-over-mult (pos (succ x)) (negsucc b) = I
 where
  I : abs (pos (succ x) * negsucc b) ≡ abs (pos (succ x)) ℕ* abs (negsucc b)
  I = abs (pos (succ x) * negsucc b)           ≡⟨ ap abs (subtraction-dist-over-mult (pos (succ x)) (pos (succ b))) ⟩
      abs (- ((pos (succ x) * pos (succ b))))  ≡⟨ ap (λ z → (abs (- z))) (pos-multiplication-equiv-to-ℕ (succ x) (succ b)) ⟩
      abs (- pos (succ x ℕ* succ b))           ≡⟨ abs-removes-neg-sign ( pos (succ x ℕ* succ b)) ⁻¹ ⟩
      abs (pos (succ x ℕ* succ b))             ≡⟨ refl ⟩
      succ x ℕ* succ b                         ≡⟨ refl ⟩
      abs (pos (succ x)) ℕ* abs (negsucc b)    ∎
abs-over-mult (negsucc x) (pos b) = I
 where
  I : abs (negsucc x * pos b) ≡ abs (negsucc x) ℕ* abs (pos b)
  I = abs (negsucc x * pos b)        ≡⟨ ap abs (subtraction-dist-over-mult' (pos (succ x)) (pos b)) ⟩
      abs (- pos (succ x) * pos b)   ≡⟨ ap (λ z → abs (- z)) (pos-multiplication-equiv-to-ℕ (succ x) b) ⟩
      abs (- pos (succ x ℕ* b))      ≡⟨ abs-removes-neg-sign (pos (succ x ℕ* b)) ⁻¹ ⟩
      (succ x) ℕ* b                  ≡⟨ refl ⟩
      abs (negsucc x) ℕ* abs (pos b) ∎
abs-over-mult (negsucc x) (negsucc b) = I
 where
  I : abs (negsucc x * negsucc b) ≡ abs (negsucc x) ℕ* abs (negsucc b)
  I = abs (negsucc x * negsucc b)               ≡⟨ ap abs (subtraction-dist-over-mult (negsucc x) (pos (succ b))) ⟩
      abs (- negsucc x * pos (succ b) )         ≡⟨ ap (λ z → abs (- z)) (subtraction-dist-over-mult' (pos (succ x)) (pos (succ b))) ⟩
      abs (- (- pos (succ x) * pos (succ b)))   ≡⟨ ap abs (minus-minus-is-plus (pos (succ x) * pos (succ b))) ⟩
      abs (pos (succ x) * pos (succ b))         ≡⟨ ap abs (pos-multiplication-equiv-to-ℕ (succ x) (succ b)) ⟩
      (succ x) ℕ* (succ b)                      ≡⟨ refl ⟩
      abs (negsucc x) ℕ* abs (negsucc b)       ∎

pos-abs-is-equal : (x : ℕ) → absℤ (pos x) ≡ pos x
pos-abs-is-equal x = refl

abs-over-mult' : (x y : ℤ) → absℤ (x * y) ≡ absℤ x * absℤ y
abs-over-mult' (pos x) (pos y) = I
 where
  I : absℤ (pos x * pos y) ≡ absℤ (pos x) * absℤ (pos y)
  I = absℤ (pos x * pos y) ≡⟨ ap absℤ (pos-multiplication-equiv-to-ℕ x y) ⟩
      absℤ (pos (x ℕ* y))  ≡⟨ by-definition ⟩
      pos (x ℕ* y)         ≡⟨ pos-multiplication-equiv-to-ℕ x y ⁻¹ ⟩
      pos x * pos y        ≡⟨ by-definition ⟩
      absℤ (pos x) * absℤ (pos y) ∎
abs-over-mult' (pos x) (negsucc y) = I
 where
  I : absℤ (pos x * negsucc y) ≡ absℤ (pos x) * absℤ (negsucc y)
  I = absℤ (pos x * negsucc y)        ≡⟨ ap absℤ (subtraction-dist-over-mult (pos x) (pos (succ y))) ⟩
      absℤ (- pos x * pos (succ y))   ≡⟨ ap (λ z → absℤ (- z)) (pos-multiplication-equiv-to-ℕ x (succ y)) ⟩
      absℤ (- pos (x ℕ* succ y))      ≡⟨ absℤ-removes-neg-sign (pos (x ℕ* succ y)) ⁻¹ ⟩
      absℤ (pos (x ℕ* succ y))        ≡⟨ by-definition ⟩
      pos (x ℕ* succ y)               ≡⟨ pos-multiplication-equiv-to-ℕ x (succ y) ⁻¹ ⟩
      pos x * pos (succ y)            ≡⟨ by-definition ⟩
      absℤ (pos x) * absℤ (negsucc y) ∎
abs-over-mult' (negsucc x) (pos y) = I
 where
  I : absℤ (negsucc x * pos y) ≡ absℤ (negsucc x) * absℤ (pos y)
  I = absℤ (negsucc x * pos y)      ≡⟨ ap absℤ (ℤ*-comm (negsucc x) (pos y)) ⟩
      absℤ (pos y * negsucc x)      ≡⟨ ap absℤ (subtraction-dist-over-mult (pos y) (pos (succ x))) ⟩
      absℤ (- pos y * pos (succ x)) ≡⟨ ap (λ z → absℤ (- z)) (pos-multiplication-equiv-to-ℕ y (succ x)) ⟩
      absℤ (- pos (y ℕ* succ x))    ≡⟨ absℤ-removes-neg-sign (pos (y ℕ* succ x)) ⁻¹ ⟩
      absℤ (pos (y ℕ* succ x))      ≡⟨ by-definition ⟩
      pos (y ℕ* succ x)             ≡⟨ pos-multiplication-equiv-to-ℕ y (succ x) ⁻¹ ⟩
      pos y * pos (succ x)          ≡⟨ ℤ*-comm (pos y) (pos (succ x)) ⟩
      pos (succ x) * pos y          ≡⟨ by-definition ⟩ 
      absℤ (negsucc x) * absℤ (pos y) ∎
abs-over-mult' (negsucc x) (negsucc y) = I
 where
  I : absℤ (negsucc x * negsucc y) ≡ absℤ (negsucc x) * absℤ (negsucc y)
  I = absℤ (negsucc x * negsucc y)        ≡⟨ ap absℤ (minus-times-minus-is-positive (pos (succ x)) (pos (succ y))) ⟩
      absℤ (pos (succ x) * pos (succ y))  ≡⟨ ap absℤ (pos-multiplication-equiv-to-ℕ (succ x) (succ y)) ⟩
      absℤ (pos (succ x ℕ* succ y))       ≡⟨ by-definition ⟩
      pos (succ x ℕ* succ y)              ≡⟨ pos-multiplication-equiv-to-ℕ (succ x) (succ y) ⁻¹ ⟩
      pos (succ x) * pos (succ y)         ≡⟨ by-definition ⟩
      absℤ (negsucc x) * absℤ (negsucc y) ∎

succℤ-no-fp : (x : ℤ) → ¬ (x ≡ succℤ x)
succℤ-no-fp (pos x) e = succ-no-fp x (pos-lc e)
succℤ-no-fp (negsucc zero) e = pos-not-negative (e ⁻¹)
succℤ-no-fp (negsucc (succ x)) e = succ-no-fp x (negsucc-lc (e ⁻¹))

greater-than-zero-succℤ : (x : ℤ) → greater-than-zero x → greater-than-zero (succℤ x)
greater-than-zero-succℤ (pos 0)        g = 𝟘-elim g
greater-than-zero-succℤ (pos (succ x)) g = g
greater-than-zero-succℤ (negsucc x)    g = 𝟘-elim g

gtz₀ : (x : ℤ) → (y : ℕ) → greater-than-zero x → greater-than-zero (pos y) → greater-than-zero (x + (pos y))
gtz₀ x = induction base step
 where
  base : greater-than-zero x
       → greater-than-zero (pos 0)
       → greater-than-zero (x + pos 0)
  base l r = 𝟘-elim r

  step : (k : ℕ)
       → (greater-than-zero x → greater-than-zero (pos k) → greater-than-zero (x + pos k))
       → greater-than-zero x
       → greater-than-zero (pos (succ k))
       → greater-than-zero (x + pos (succ k))
  step 0        IH l r = greater-than-zero-succℤ x l
  step (succ k) IH l r = greater-than-zero-succℤ (x + pos (succ k)) (IH l r)

greater-than-zero-trans : (x y : ℤ) → greater-than-zero x → greater-than-zero y → greater-than-zero (x + y)
greater-than-zero-trans x (pos y)         = gtz₀ x y
greater-than-zero-trans x (negsucc y) l r = 𝟘-elim r

gtzmt₀ : (x : ℤ) → (y : ℕ) → greater-than-zero x → greater-than-zero (pos y) → greater-than-zero (x * pos y)
gtzmt₀ x = induction base step
 where
  base : greater-than-zero x → greater-than-zero (pos 0) → greater-than-zero (x * pos 0)
  base l r = 𝟘-elim r

  step : (k : ℕ)
       → (greater-than-zero x → greater-than-zero (pos k) → greater-than-zero (x * pos k))
       → greater-than-zero x
       → greater-than-zero (pos (succ k))
       → greater-than-zero (x * pos (succ k))
  step zero IH l r = l
  step (succ k) IH l r = greater-than-zero-trans x (x * pos (succ k)) l (IH l r)

greater-than-zero-mult-trans : (x y : ℤ) → greater-than-zero x → greater-than-zero y → greater-than-zero (x * y)
greater-than-zero-mult-trans x (negsucc y) l r = 𝟘-elim r
greater-than-zero-mult-trans x (pos y)     l r = gtzmt₀ x y l r


{-
ℤ-not-equal-to-succ : (x : ℤ) → ¬ (x ≡ succℤ x)
ℤ-not-equal-to-succ = ℤ-induction base step₁ step₂
 where
  base : ¬ (pos 0 ≡ succℤ (pos 0))
  base e = pos-int-not-zero 0 (e ⁻¹)
  step₁ : (k : ℤ) → ¬ (k ≡ succℤ k) → ¬ (succℤ k ≡ succℤ (succℤ k))
  step₁ k IH e = IH II
   where
    I : predℤ (succℤ k) ≡ predℤ (succℤ (succℤ k))
    I = ap predℤ e
    II : k ≡ succℤ k
    II = k                       ≡⟨ predsuccℤ k ⁻¹ ⟩
         predℤ (succℤ k)         ≡⟨ I ⟩
         predℤ (succℤ (succℤ k)) ≡⟨ predsuccℤ (succℤ k) ⟩
         succℤ k ∎
  step₂ : (k : ℤ) → ¬ (succℤ k ≡ succℤ (succℤ k)) → ¬ (k ≡ succℤ k)
  step₂ k IH e = IH (ap succℤ e)
-}

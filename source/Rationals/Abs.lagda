Andrew Sneap, 10 March 2022

In this file I define the absolute value for rational numbers,
and prove properties of the absolute value.

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import UF.FunExt
open import UF.Base hiding (_≈_)
open import UF.Subsingletons

open import Integers.Abs
open import Integers.Addition renaming (_+_ to _ℤ+_) hiding (_-_)
open import Integers.Type hiding (abs)
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Order
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Rationals.Fractions
open import Rationals.FractionsOperations renaming (abs to 𝔽-abs) renaming (-_ to 𝔽-_) hiding (_+_) hiding (_*_)
open import Rationals.Type
open import Rationals.Addition
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Multiplication

module Rationals.Abs where

abs : ℚ → ℚ
abs (q , _) = toℚ (𝔽-abs q)

ℚ-abs-zero : 0ℚ ＝ abs 0ℚ
ℚ-abs-zero = by-definition

toℚ-abs : Fun-Ext → (q : 𝔽) → abs (toℚ q) ＝ toℚ (𝔽-abs q)
toℚ-abs fe (x , a) = conclusion
 where
  rational-q : Σ ((x' , a') , lxp) ꞉ ℚ , Σ h ꞉ ℕ , (x ＝ pos (succ h) ℤ* x') × (succ a ＝ succ h ℕ* succ a')
  rational-q = toℚlemma (x , a)
  lx : ℚ
  lx = pr₁ rational-q
  x' : ℤ
  x' = pr₁ (pr₁ lx)
  a' : ℕ
  a' = pr₂ (pr₁ lx)
  lxp = pr₂ lx
  h = pr₁ (pr₂ (rational-q))
  e₁ : succ a ＝ succ h ℕ* succ a'
  e₁ = pr₂ (pr₂ (pr₂ rational-q))
  e₂ : x ＝ pos (succ h) ℤ* x'
  e₂ = pr₁ (pr₂ (pr₂ rational-q))

  sa = succ a
  psa = pos (succ a)
  sh = succ h
  psh = pos (succ h)
  sa' = succ a'
  psa' = pos (succ a')

  helper : 𝔽-abs (x' , a') ≈ 𝔽-abs (x , a) → toℚ (𝔽-abs (x' , a')) ＝ toℚ (𝔽-abs (x , a))
  helper = equiv→equality fe (𝔽-abs (x' , a')) (𝔽-abs (x , a))

  I : 𝔽-abs (x' , a') ≈ 𝔽-abs (x , a)
  I = ℤ-mult-left-cancellable (absℤ x' ℤ* psa) (absℤ x ℤ* psa') psh id II
   where
    II : psh ℤ* (absℤ x' ℤ* psa) ＝ psh ℤ* (absℤ x ℤ* psa')
    II = psh ℤ* (absℤ x' ℤ* psa)       ＝⟨ ℤ*-assoc psh (absℤ x') psa ⁻¹                             ⟩
         psh ℤ* absℤ x' ℤ* psa         ＝⟨ by-definition                                             ⟩
         absℤ psh ℤ* absℤ x' ℤ* psa    ＝⟨ ap (_ℤ* psa) (abs-over-mult' psh x' ⁻¹)                   ⟩
         absℤ (psh ℤ* x') ℤ* psa       ＝⟨ ap (λ z → absℤ z ℤ* psa) (e₂ ⁻¹)                          ⟩
         absℤ x ℤ* psa                 ＝⟨ ap (λ z → absℤ x ℤ* pos z) e₁                             ⟩
         absℤ x ℤ* pos (sh ℕ* sa')     ＝⟨ ap (absℤ x ℤ*_) (pos-multiplication-equiv-to-ℕ sh sa' ⁻¹) ⟩
         absℤ x ℤ* (psh ℤ* psa')       ＝⟨ ℤ-mult-rearrangement''' (absℤ x) psh psa'                 ⟩
         psh ℤ* (absℤ x ℤ* psa')       ∎

  conclusion : abs (toℚ (x , a)) ＝ toℚ (𝔽-abs (x , a))
  conclusion = helper I

abs-of-pos-is-pos : Fun-Ext → (p : ℚ) → 0ℚ ≤ p → abs p ＝ p
abs-of-pos-is-pos fe ((pos x , a) , α) l = I
 where
  I : abs ((pos x , a) , α) ＝ (pos x , a) , α
  I = abs ((pos x , a) , α)    ＝⟨ by-definition ⟩
      toℚ (𝔽-abs (pos x , a)) ＝⟨ by-definition ⟩
      toℚ (pos x , a)          ＝⟨ toℚ-to𝔽 fe ((pos x , a) , α) ⁻¹ ⟩
      ((pos x , a) , α) ∎
abs-of-pos-is-pos fe ((negsucc x , a) , α) l = 𝟘-elim (III II)
 where
  I : pos 0 ℤ* pos (succ a) ≤ negsucc x ℤ* pos 1
  I = l
  II : pos 0 ≤ negsucc x
  II = transport₂ _≤_ (ℤ-zero-left-base (pos (succ a))) (ℤ-zero-right-neutral (negsucc x)) I
  III : ¬ (pos 0 ≤ negsucc x)
  III (k , e) = pos-not-negsucc (ℤ-zero-left-neutral (pos k) ⁻¹ ∙ e)

abs-of-pos-is-pos' : Fun-Ext → (p : ℚ) → 0ℚ < p → abs p ＝ p
abs-of-pos-is-pos' fe p l = abs-of-pos-is-pos fe p (ℚ<-coarser-than-≤ 0ℚ p l)

ℚ-abs-neg-equals-pos : Fun-Ext → (q : ℚ) → abs q ＝ abs (- q)
ℚ-abs-neg-equals-pos fe (q , p) = conclusion
 where
  helper : 𝔽-abs q ≈ 𝔽-abs (𝔽- q) → toℚ (𝔽-abs q) ＝ toℚ (𝔽-abs (𝔽- q))
  helper = equiv→equality fe (𝔽-abs q) (𝔽-abs (𝔽- q))

  I : 𝔽-abs q ≈ 𝔽-abs (𝔽- q)
  I = 𝔽-abs-neg-equals-pos q

  conclusion : abs (q , p) ＝ abs (- (q , p))
  conclusion = abs (q , p)           ＝⟨ by-definition ⟩
               toℚ (𝔽-abs q)         ＝⟨ helper I ⟩
               toℚ (𝔽-abs (𝔽- q))   ＝⟨ toℚ-abs fe (𝔽- q) ⁻¹ ⟩
               abs (toℚ (𝔽- q))      ＝⟨ by-definition ⟩
               abs (- (q , p)) ∎

ℚ-abs-inverse : Fun-Ext → (q : ℚ) → (abs q ＝ q) ∔ (abs q ＝ - q)
ℚ-abs-inverse fe ((pos x , a) , q) = inl conclusion
 where
  I : (pos x , a) ≈ to𝔽 (toℚ (pos x , a))
  I = ≈-toℚ (pos x , a)
  II : Σ (x' , a') ꞉ 𝔽 , ((pos x , a) , q ＝ toℚ (x' , a'))
  II = q-has-qn fe ((pos x , a) , q)
  x' = pr₁ (pr₁ II)
  a' = pr₂ (pr₁ II)

  helper : (pos x , a) ≈ (x' , a') → toℚ (pos x , a) ＝ toℚ (x' , a')
  helper = equiv→equality fe (pos x , a) (x' , a')

  III : (pos x , a) ≈ (x' , a')
  III = refl

  conclusion : abs ((pos x , a) , q) ＝ (pos x , a) , q
  conclusion = abs ((pos x , a) , q)   ＝⟨ by-definition ⟩
               toℚ (pos x , a)         ＝⟨ helper III ⟩
               toℚ (x' , a')           ＝⟨ pr₂ II ⁻¹ ⟩
               (pos x , a) , q         ∎
ℚ-abs-inverse fe ((negsucc x , a) , q) = inr conclusion
 where
  conclusion : abs ((negsucc x , a) , q) ＝ - ((negsucc x , a) , q)
  conclusion = abs ((negsucc x , a) , q)     ＝⟨ by-definition ⟩
               toℚ ((absℤ (negsucc x)) , a)  ＝⟨ by-definition ⟩
               toℚ (pos (succ x) , a)        ＝⟨ by-definition ⟩
               toℚ (𝔽- (negsucc x , a))     ＝⟨ by-definition ⟩
               - ((negsucc x , a) , q)      ∎

ℚ-positive-not-zero : Fun-Ext → (x a : ℕ) → ¬ (toℚ (pos (succ x) , a) ＝ 0ℚ)
ℚ-positive-not-zero fe x a e = pos-succ-not-zero x III
 where
  I : (pos (succ x) , a) ≈ (pos 0 , 0)
  I = equality→equiv fe (pos (succ x) , a) (pos 0 , 0) e

  II : pos (succ x) ℤ* pos 1 ＝ pos 0 ℤ* pos (succ a)
  II = I

  III : pos (succ x) ＝ pos 0
  III = pos (succ x)            ＝⟨ by-definition ⟩
        pos (succ x) ℤ* (pos 1) ＝⟨ II ⟩
        pos 0 ℤ* pos (succ a)   ＝⟨ ℤ-zero-left-base (pos (succ a))  ⟩
        pos 0 ∎


ℚ-abs-is-positive : (q : ℚ) → 0ℚ ≤ abs q
ℚ-abs-is-positive ((pos zero , a) , _)     = 0 , I
 where
  I : pos 0 ℤ* pos 0 ℤ+ pos 0 ＝ pos 0 ℤ* pos (succ 0)
  I = pos 0 ℤ* pos 0 ℤ+ pos 0 ＝⟨ by-definition ⟩
      pos 0 ℤ* pos 0          ＝⟨ by-definition ⟩
      pos 0                   ＝⟨ by-definition ⟩
      pos 0 ℤ* pos 1          ∎
ℚ-abs-is-positive ((pos (succ x) , a) , q) = ℚ<-coarser-than-≤ 0ℚ (abs ((pos (succ x) , a) , q)) (ℚ-zero-less-than-positive x a)
ℚ-abs-is-positive ((negsucc x , a) , q)    = ℚ<-coarser-than-≤ 0ℚ (abs (((negsucc x , a) , q))) (ℚ-zero-less-than-positive x a)

ℚ-abs-zero-is-zero : Fun-Ext → (q : ℚ) → abs q ＝ 0ℚ → q ＝ 0ℚ
ℚ-abs-zero-is-zero fe ((pos 0 , a) , p) e = numerator-zero-is-zero fe ((pos 0 , a) , p) refl
ℚ-abs-zero-is-zero fe ((pos (succ x) , a) , p) e = 𝟘-elim (ℚ-positive-not-zero fe x a e)
ℚ-abs-zero-is-zero fe ((negsucc x , a) , p) e = 𝟘-elim (ℚ-positive-not-zero fe x a e)

ℚ-abs-≤ : Fun-Ext → (q : ℚ) → (- (abs q) ≤ q) × (q ≤ abs q)
ℚ-abs-≤ fe q = locate-q (ℚ-abs-inverse fe q)
 where
  i : 0ℚ ≤ abs q
  i = ℚ-abs-is-positive q
  ii : 0ℚ - abs q ≤ abs q - abs q
  ii = ℚ≤-addition-preserves-order fe 0ℚ (abs q) (- abs q) i
  iii : - abs q ≤ 0ℚ
  iii = transport₂ _≤_ (ℚ-zero-left-neutral fe (- abs q)) (ℚ-inverse-sum-to-zero fe (abs q)) ii
  iv : - abs q ≤ abs q
  iv = ℚ≤-trans fe (- abs q) 0ℚ (abs q) iii i

  locate-q : (abs q ＝ q) ∔ (abs q ＝ - q) → - abs q ≤ q × q ≤ abs q
  locate-q (inl e) = I , II
   where
    I : - abs q ≤ q
    I = transport (- abs q ≤_) e iv

    II : q ≤ abs q
    II = transport (q ≤_) (e ⁻¹) (ℚ≤-refl q)
  locate-q (inr r) = I , II
   where
    α : q ＝ - abs q
    α = q         ＝⟨ ℚ-minus-minus fe q ⟩
        - (- q)   ＝⟨ ap -_ (r ⁻¹) ⟩
        - abs q   ∎

    I : - abs q ≤ q
    I = transport (_≤ q) α (ℚ≤-refl q)

    II : q ≤ abs q
    II = transport (_≤ abs q) (α ⁻¹) iv

ℚ-abs-≤-unpack : Fun-Ext → (q ε : ℚ) → abs q ≤ ε → (- ε ≤ q) × (q ≤ ε)
ℚ-abs-≤-unpack fe q ε l = locate-q (ℚ-abs-inverse fe q)
 where
  abs-q-positive : 0ℚ ≤ abs q
  abs-q-positive = ℚ-abs-is-positive q

  ε-positive : 0ℚ ≤ ε
  ε-positive = ℚ≤-trans fe 0ℚ (abs q) ε abs-q-positive l

  neg-epsilon-negative : - ε ≤ 0ℚ
  neg-epsilon-negative = ℚ≤-swap fe 0ℚ ε ε-positive

  locate-q : (abs q ＝ q) ∔ (abs q ＝ - q) → - ε ≤ q × q ≤ ε
  locate-q (inl i) = ℚ≤-trans fe (- ε) 0ℚ q neg-epsilon-negative (transport (0ℚ ≤_) i abs-q-positive) , (transport (_≤ ε) i l)
  locate-q (inr i) = transport (- ε ≤_) (ℚ-minus-minus fe q ⁻¹) β , ℚ≤-trans fe q 0ℚ ε δ ε-positive
   where
    α : - q ≤ ε
    α = transport (_≤ ε) i l
    β : - ε ≤ - (- q)
    β = ℚ≤-swap fe (- q) ε α
    γ : - (- q) ≤ 0ℚ
    γ = transport (λ z → - z ≤ 0ℚ) i (ℚ≤-swap fe 0ℚ (abs q) abs-q-positive)
    δ : q ≤ 0ℚ
    δ = transport (_≤ 0ℚ) (ℚ-minus-minus fe q ⁻¹) γ

ℚ≤-to-abs : Fun-Ext → (x y : ℚ) → (- y ≤ x) × (x ≤ y) → abs x ≤ y
ℚ≤-to-abs fe x y (l₁ , l₂) = I (ℚ-abs-inverse fe x)
 where
  α : - x ≤ - (- y)
  α = ℚ≤-swap fe (- y) x l₁
  I : (abs x ＝ x) ∔ (abs x ＝ - x) → abs x ≤ y
  I (inl l) = transport (_≤ y) (l ⁻¹) l₂
  I (inr r) = transport₂ _≤_ (r ⁻¹) (ℚ-minus-minus fe y ⁻¹) α

ℚ<-to-abs : Fun-Ext → (x y : ℚ) → (- y < x) × (x < y) → abs x < y
ℚ<-to-abs fe x y (l₁ , l₂) = II (ℚ≤-split fe (abs x) y I)
 where
  I : abs x ≤ y
  I = ℚ≤-to-abs fe x y (ℚ<-coarser-than-≤ (- y) x l₁ , ℚ<-coarser-than-≤ x y l₂)
  II : abs x < y ∔ (abs x ＝ y) → abs x < y
  II (inl l) = l
  II (inr r) = III (ℚ-abs-inverse fe x)
   where

    III : (abs x ＝ x) ∔ (abs x ＝ - x) → abs x < y
    III (inl s) = 𝟘-elim (ℚ<-not-itself x (transport (x <_) (r ⁻¹ ∙ s) l₂))
    III (inr s) = 𝟘-elim (ℚ<-not-itself x (transport (_< x) IV l₁))
     where
      IV : - y ＝ x
      IV = - y     ＝⟨ ap -_ (r ⁻¹ ∙ s) ⟩
           - (- x) ＝⟨ ℚ-minus-minus fe x ⁻¹ ⟩
           x ∎

ℚ-abs-<-unpack :  Fun-Ext → (q ε : ℚ) → abs q < ε → (- ε < q) × (q < ε)
ℚ-abs-<-unpack fe q ε l = locate-q (ℚ-abs-inverse fe q)
 where
  abs-q-positive : 0ℚ ≤ abs q
  abs-q-positive = ℚ-abs-is-positive q

  ε-positive : 0ℚ < ε
  ε-positive = ℚ≤-<-trans fe 0ℚ (abs q) ε abs-q-positive l

  neg-epsilon-negative : - ε < 0ℚ
  neg-epsilon-negative = ℚ<-swap fe 0ℚ ε ε-positive

  locate-q : (abs q ＝ q) ∔ (abs q ＝ - q) → - ε < q × q < ε
  locate-q (inl i) = ℚ<-≤-trans fe (- ε) 0ℚ q neg-epsilon-negative (transport (0ℚ ≤_) i abs-q-positive) , (transport (_< ε) i l)
  locate-q (inr i) = transport (- ε <_) (ℚ-minus-minus fe q ⁻¹) β , ℚ≤-<-trans fe q 0ℚ ε δ ε-positive
   where
    α : - q < ε
    α = transport (_< ε) i l
    β : - ε < - (- q)
    β = ℚ<-swap fe (- q) ε α
    γ : - (- q) ≤ 0ℚ
    γ = transport (λ z → - z ≤ 0ℚ) i (ℚ≤-swap fe 0ℚ (abs q) abs-q-positive)
    δ : q ≤ 0ℚ
    δ = transport (_≤ 0ℚ) (ℚ-minus-minus fe q ⁻¹) γ

ℚ-triangle-inequality : Fun-Ext → (x y : ℚ) → abs (x + y) ≤ abs x + abs y
ℚ-triangle-inequality fe x y = ℚ≤-to-abs fe (x + y) (abs x + abs y) (I (ℚ-abs-≤ fe x) (ℚ-abs-≤ fe y))
 where
  I : - (abs x) ≤ x × x ≤ abs x → - abs y ≤ y × y ≤ abs y → - (abs x + abs y) ≤ x + y × x + y ≤ abs x + abs y
  I (l₁ , l₂) (l₃ , l₄) = transport (_≤ x + y) γ α , β
   where
    α : (- abs x) - abs y ≤ x + y
    α = ℚ≤-adding fe (- abs x) x (- abs y) y l₁ l₃
    γ : (- abs x) - abs y ＝ - (abs x + abs y)
    γ = ℚ-minus-dist fe (abs x) (abs y)
    β : x + y ≤ abs x + abs y
    β = ℚ≤-adding fe x (abs x) y (abs y) l₂ l₄

pos-abs-no-increase : Fun-Ext → (q ε : ℚ) → (0ℚ < q) × (q < ε) → abs q < ε
pos-abs-no-increase fe q ε (l₁ , l₂) = IV
 where
  I : 0ℚ < ε
  I = ℚ<-trans 0ℚ q ε l₁ l₂
  II : - ε < 0ℚ
  II = transport (- ε <_) ℚ-minus-zero-is-zero i
   where
    i : - ε < - 0ℚ
    i = ℚ<-swap fe 0ℚ ε I
  III : - ε < q
  III = ℚ<-trans (- ε) 0ℚ q II l₁
  IV : abs q < ε
  IV = ℚ<-to-abs fe q ε (III , l₂)

abs-mult : Fun-Ext → (x y : ℚ) → abs x * abs y ＝ abs (x * y)
abs-mult fe x y = case-split (ℚ-dichotomous' fe x 0ℚ) (ℚ-dichotomous' fe y 0ℚ)
 where
  case1 : 0ℚ ≤ x → 0ℚ ≤ y → abs x * abs y ＝ abs (x * y)
  case1 l₁ l₂ = abs x * abs y  ＝⟨ ap (_* abs y) (abs-of-pos-is-pos fe x l₁)                                         ⟩
                x * abs y      ＝⟨ ap (x *_) (abs-of-pos-is-pos fe y l₂)                                             ⟩
                x * y          ＝⟨ abs-of-pos-is-pos fe (x * y) (ℚ≤-pos-multiplication-preserves-order x y l₁ l₂) ⁻¹ ⟩
                abs (x * y)    ∎

  case2 : (0ℚ > x) → (0ℚ > y) → abs x * abs y ＝ abs (x * y)
  case2 l₁ l₂ = goal
   where
    0<-x : 0ℚ < - x
    0<-x = ℚ<-swap'' fe x l₁
    0<-y : 0ℚ < - y
    0<-y = ℚ<-swap'' fe y l₂

    remove-negatives : (- x) * (- y) ＝ x * y
    remove-negatives = (- x) * (- y)     ＝⟨ ℚ-negation-dist-over-mult fe x (- y)        ⟩
                       - x * (- y)       ＝⟨ ap -_ (ℚ*-comm x (- y))                     ⟩
                       - (- y) * x       ＝⟨ ap -_ (ℚ-negation-dist-over-mult fe y x)    ⟩
                       - (- y * x)       ＝⟨ ℚ-minus-minus fe (y * x) ⁻¹                 ⟩
                       y * x             ＝⟨ ℚ*-comm y x                                 ⟩
                       x * y             ∎

    0<x*y : 0ℚ < x * y
    0<x*y = transport (0ℚ <_) remove-negatives (ℚ<-pos-multiplication-preserves-order (- x) (- y) 0<-x 0<-y)

    goal : abs x * abs y ＝ abs (x * y)
    goal = abs x * abs y     ＝⟨ ap (_* abs y) (ℚ-abs-neg-equals-pos fe x)        ⟩
           abs (- x) * abs y ＝⟨ ap (_* abs y) (abs-of-pos-is-pos' fe (- x) 0<-x) ⟩
           (- x) * abs y     ＝⟨ ap ((- x) *_) (ℚ-abs-neg-equals-pos fe y)        ⟩
           (- x) * abs (- y) ＝⟨ ap ((- x) *_) (abs-of-pos-is-pos' fe (- y) 0<-y) ⟩
           (- x) * (- y)     ＝⟨ remove-negatives                                 ⟩
           x * y             ＝⟨ abs-of-pos-is-pos' fe (x * y) 0<x*y ⁻¹           ⟩
           abs (x * y)       ∎

  case3 : (a b : ℚ) → 0ℚ ≤ a → b < 0ℚ → abs a * abs b ＝ abs (a * b)
  case3 a b l₁ l₂ = abs a * abs b ＝⟨ ap (_* abs b) (abs-of-pos-is-pos fe a l₁)                   ⟩
                    a * abs b     ＝⟨ ap (a *_) (ℚ-abs-neg-equals-pos fe b)                       ⟩
                    a * abs (- b) ＝⟨ ap (a *_) (abs-of-pos-is-pos' fe (- b) (ℚ<-swap'' fe b l₂)) ⟩
                    a * (- b)     ＝⟨ ℚ*-comm a (- b)                                             ⟩
                    (- b) * a     ＝⟨ ℚ-negation-dist-over-mult fe b a                            ⟩
                    - b * a       ＝⟨ ap -_ (ℚ*-comm b a)                                         ⟩
                    - a * b       ＝⟨ abs-of-pos-is-pos fe (- a * b) (ℚ≤-swap' fe (a * b) I) ⁻¹   ⟩
                    abs (- a * b) ＝⟨ ℚ-abs-neg-equals-pos fe (a * b) ⁻¹                          ⟩
                    abs (a * b)   ∎

   where
    first : 0ℚ ≤ - b
    first = ℚ≤-swap' fe b (ℚ<-coarser-than-≤ b 0ℚ l₂)
    second : 0ℚ ≤ a * (- b)
    second = ℚ≤-pos-multiplication-preserves-order a (- b) l₁ first
    third : - (a * (- b)) ≤ - 0ℚ
    third = ℚ≤-swap fe 0ℚ (a * (- b)) second
    I : a * b ≤ 0ℚ
    I = transport₂ _≤_ II ℚ-minus-zero-is-zero third
     where
      II : - (a * (- b)) ＝ a * b
      II = - a * (- b) ＝⟨ ap -_ (ℚ*-comm a (- b))                     ⟩
           - (- b) * a ＝⟨ ap -_ (ℚ-negation-dist-over-mult fe b a)    ⟩
           - (- b * a) ＝⟨ ℚ-minus-minus fe (b * a) ⁻¹                 ⟩
           b * a       ＝⟨ ℚ*-comm b a                                 ⟩
           a * b       ∎

  case-split : x < 0ℚ ∔ 0ℚ ≤ x → y < 0ℚ ∔ 0ℚ ≤ y → abs x * abs y ＝ abs (x * y)
  case-split (inl l₁) (inl l₂) = case2 l₁ l₂
  case-split (inl l₁) (inr l₂) = goal
   where
    goal : abs x * abs y ＝ abs (x * y)
    goal = abs x * abs y ＝⟨ ℚ*-comm (abs x) (abs y) ⟩
           abs y * abs x ＝⟨ case3 y x l₂ l₁         ⟩
           abs (y * x)   ＝⟨ ap abs (ℚ*-comm y x)    ⟩
           abs (x * y)   ∎
  case-split (inr l₁) (inl l₂) = case3 x y l₁ l₂
  case-split (inr l₁) (inr l₂) = case1 l₁ l₂

\end{code}

Andrew Sneap, 10 March 2022

In this file, I prove that the Rationals are metric space, with
respect to the usual metric.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import UF.FunExt
open import UF.Base
open import UF.Subsingletons
open import UF.PropTrunc
open import Rationals.Type
open import Rationals.Abs
open import Rationals.Addition
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Positive renaming (_+_ to _ℚ₊+_)

module MetricSpaces.Rationals
  (fe : Fun-Ext)
  (pe : Prop-Ext)
  (pt : propositional-truncations-exist)
 where

open import Rationals.MinMax
open import MetricSpaces.Type fe pe pt

ℚ-zero-dist : (q : ℚ) → abs (q - q) ＝ 0ℚ
ℚ-zero-dist q = abs (q - q)  ＝⟨ ap abs (ℚ-inverse-sum-to-zero q) ⟩
                abs 0ℚ       ＝⟨ by-definition                    ⟩
                0ℚ           ∎

ℚ<-abs : (x y : ℚ) → x < y → y - x ＝ abs (x - y)
ℚ<-abs x y l = γ
 where
  I : 0ℚ < y - x
  I = ℚ<-difference-positive x y l

  γ : y - x ＝ abs (x - y)
  γ = y - x       ＝⟨ abs-of-pos-is-pos' (y - x) I ⁻¹ ⟩
      abs (y - x) ＝⟨ abs-comm y x                    ⟩
      abs (x - y) ∎

inequality-chain-to-metric : (p q r : ℚ)
                           → p ≤ q
                           → q ≤ r
                           → abs (p - r) ＝ abs (p - q) + abs (q - r)
inequality-chain-to-metric p q r l₁ l₂ = γ
 where
  γ₁ : abs (p - q) ＝ q - p
  γ₁ = ℚ≤-to-abs' p q l₁

  γ₂ : abs (q - r) ＝ r - q
  γ₂ = ℚ≤-to-abs' q r l₂

  I : p ≤ r
  I = ℚ≤-trans p q r l₁ l₂

  γ₃ : abs (p - r) ＝ r - p
  γ₃ = ℚ≤-to-abs' p r I

  γ : abs (p - r) ＝ abs (p - q) + abs (q - r)
  γ = abs (p - r)                 ＝⟨ γ₃                                  ⟩
      r - p                       ＝⟨ ap (_- p) (ℚ-inverse-intro'''' r q) ⟩
      r - q + q - p               ＝⟨ ℚ+-assoc (r - q) q (- p)            ⟩
      r - q + (q - p)             ＝⟨ ℚ+-comm (r - q) (q - p)             ⟩
      q - p + (r - q)             ＝⟨ ap (_+ (r - q)) (γ₁ ⁻¹)             ⟩
      abs (p - q) + (r - q)       ＝⟨ ap (abs (p - q) +_) (γ₂ ⁻¹)         ⟩
      abs (p - q) + abs (q - r)   ∎

inequality-chain-with-metric : (x y w z ε₁ ε₂ : ℚ)
                             → w ≤ y
                             → y ≤ z
                             → abs (x - y) < ε₁
                             → abs (w - z) < ε₂
                             → abs (x - z) < (ε₁ + ε₂)
inequality-chain-with-metric x y w z ε₁ ε₂ l₁ l₂ l₃ l₄ = γ
 where
  I : abs (x - z) ≤ abs (x - y) + abs (y - z)
  I = ℚ-triangle-inequality' x y z

  II : abs (w - z) ＝ abs (y - z) + abs (w - y)
  II = abs (w - z)               ＝⟨ inequality-chain-to-metric w y z l₁ l₂ ⟩
       abs (w - y) + abs (y - z) ＝⟨ ℚ+-comm (abs (w - y)) (abs (y - z))    ⟩
       abs (y - z) + abs (w - y) ∎

  III : 0ℚ ≤ abs (w - y)
  III = ℚ-abs-is-positive (w - y)

  IV : abs (y - z) ≤ abs (y - z) + abs (w - y)
  IV = ℚ≤-addition-preserves-order'' (abs (y - z)) (abs (w - y) ) III

  V : abs (y - z) ≤ abs (w - z)
  V = transport (abs (y - z) ≤_) (II ⁻¹) IV

  VI : abs (y - z) < ε₂
  VI = ℚ≤-<-trans (abs (y - z)) (abs (w - z)) ε₂ V l₄

  VII : abs (x - y) + abs (y - z) < ε₁ + ε₂
  VII = ℚ<-adding (abs (x - y)) ε₁ (abs (y - z)) ε₂ l₃ VI

  γ : abs (x - z) < ε₁ + ε₂
  γ = ℚ≤-<-trans (abs (x - z)) (abs (x - y) + abs (y - z)) (ε₁ + ε₂) I VII

B-ℚ : (x y : ℚ) (ε : ℚ₊) → 𝓤₀ ̇
B-ℚ x y (ε , 0<ε) = abs (x - y) < ε

ℚ-m1a : m1a ℚ B-ℚ
ℚ-m1a x y f = cases γ₁ γ₂ I
 where
  α : ℚ
  α = abs (x - y)

  0≤α : 0ℚ ≤ α
  0≤α = ℚ-abs-is-positive (x - y)

  I : (0ℚ < α) ∔ (0ℚ ＝ abs (x - y))
  I = ℚ≤-split 0ℚ α 0≤α

  γ₁ : 0ℚ < α → x ＝ y
  γ₁ l = 𝟘-elim (ℚ<-irrefl α (f (α , l )))

  γ₂ : 0ℚ ＝ abs (x - y) → x ＝ y
  γ₂ e = x         ＝⟨ ℚ-inverse-intro'''' x y                       ⟩
         x - y + y ＝⟨ ap (_+ y) (ℚ-abs-zero-is-zero (x - y) (e ⁻¹)) ⟩
         0ℚ + y    ＝⟨ ℚ-zero-left-neutral y                         ⟩
         y         ∎

ℚ-m1b : m1b ℚ B-ℚ
ℚ-m1b x (ε , 0<ε) = transport (_< ε) (ℚ-zero-dist x ⁻¹) 0<ε

ℚ-m2 : m2 ℚ B-ℚ
ℚ-m2 x y (ε , 0<ε) = transport (_< ε) (abs-comm x y)

ℚ-m3 : m3 ℚ B-ℚ
ℚ-m3 x y (ε₁ , 0<ε₁) (ε₂ , 0<ε₂) l B = ℚ<-trans (abs (x - y)) ε₁ ε₂ B l

ℚ-m4 : m4 ℚ B-ℚ
ℚ-m4 x y z (ε₁ , 0<ε₁) (ε₂ , 0<ε₂) B₁ B₂ = cases γ₁ γ₂ II
 where
  I : abs ((x - y) + (y - z)) ≤ abs (x - y) + abs (y - z)
  I = ℚ-triangle-inequality (x - y) (y - z)

  II : (abs ((x - y) + (y - z)) < abs (x - y) + abs (y - z))
     ∔ (abs ((x - y) + (y - z)) ＝ abs (x - y) + abs (y - z))
  II = ℚ≤-split (abs ((x - y) + (y - z))) (abs (x - y) + abs (y - z)) I

  III : abs (x - y) + abs (y - z) < ε₁ + ε₂
  III = ℚ<-adding (abs (x - y)) ε₁ (abs (y - z)) ε₂ B₁ B₂

  IV : abs (x - y + (y - z)) ＝ abs (x - z)
  IV = ap abs (ℚ-add-zero x (- z) y ⁻¹)

  γ₁ : abs ((x - y) + (y - z)) < abs (x - y) + abs (y - z)
     → B-ℚ x z ((ε₁ , 0<ε₁) ℚ₊+ (ε₂ , 0<ε₂))
  γ₁ l = ℚ<-trans (abs (x - z)) (abs (x - y) + abs (y - z)) (ε₁ + ε₂) V III
   where
    V : abs (x - z) < abs (x - y) + abs (y - z)
    V = transport (_< abs (x - y) + abs (y - z)) IV l

  γ₂ : abs ((x - y) + (y - z)) ＝ abs (x - y) + abs (y - z)
     → B-ℚ x z ((ε₁ , 0<ε₁) ℚ₊+ (ε₂ , 0<ε₂))
  γ₂ e = transport (_< ε₁ + ε₂) (e ⁻¹ ∙ IV) III

ℚ-metric-space : metric-space ℚ
ℚ-metric-space = B-ℚ , ℚ-m1a , ℚ-m1b , ℚ-m2 , ℚ-m3 , ℚ-m4

\end{code}

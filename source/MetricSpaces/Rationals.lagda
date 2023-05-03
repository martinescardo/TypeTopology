Andrew Sneap, 10 March 2022

In this file, I prove that the Rationals are metric space, with
respect to the usual metric.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

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
open import Rationals.Positive hiding (_+_)

module MetricSpaces.Rationals
         (fe : Fun-Ext)
         (pe : Prop-Ext)
         (pt : propositional-truncations-exist)

 where

open import Rationals.MinMax
open import MetricSpaces.Definition fe pe pt

ℚ-metric : ℚ → ℚ → ℚ
ℚ-metric p q = abs (p - q)

ℚ-zero-dist : (q : ℚ) → ℚ-metric q q ＝ 0ℚ
ℚ-zero-dist q = ℚ-metric q q  ＝⟨ by-definition                    ⟩
                abs (q - q)   ＝⟨ ap abs (ℚ-inverse-sum-to-zero q) ⟩
                abs 0ℚ        ＝⟨ by-definition                    ⟩
                0ℚ            ∎

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
                           → ℚ-metric p r ＝ ℚ-metric p q + ℚ-metric q r
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

  γ : ℚ-metric p r ＝ ℚ-metric p q + ℚ-metric q r
  γ = ℚ-metric p r                ＝⟨ γ₃                                  ⟩
      r - p                       ＝⟨ ap (_- p) (ℚ-inverse-intro'''' r q) ⟩
      r - q + q - p               ＝⟨ ℚ+-assoc (r - q) q (- p)            ⟩
      r - q + (q - p)             ＝⟨ ℚ+-comm (r - q) (q - p)             ⟩
      q - p + (r - q)             ＝⟨ ap (_+ (r - q)) (γ₁ ⁻¹)             ⟩
      abs (p - q) + (r - q)       ＝⟨ ap (ℚ-metric p q +_) (γ₂ ⁻¹)        ⟩
      ℚ-metric p q + ℚ-metric q r ∎

inequality-chain-with-metric : (x y w z ε₁ ε₂ : ℚ)
                             → w ≤ y
                             → y ≤ z
                             → ℚ-metric x y < ε₁
                             → ℚ-metric w z < ε₂
                             → ℚ-metric x z < (ε₁ + ε₂)
inequality-chain-with-metric x y w z ε₁ ε₂ l₁ l₂ l₃ l₄ = γ
 where
  I : abs (x - z) ≤ abs (x - y) + abs (y - z)
  I = ℚ-triangle-inequality' x y z

  II : ℚ-metric w z ＝ ℚ-metric y z + ℚ-metric w y
  II = ℚ-metric w z                ＝⟨ inequality-chain-to-metric w y z l₁ l₂ ⟩
       ℚ-metric w y + ℚ-metric y z ＝⟨ ℚ+-comm (abs (w - y)) (abs (y - z))    ⟩
       abs (y - z) + abs (w - y)   ∎

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

  γ : ℚ-metric x z < ε₁ + ε₂
  γ = ℚ≤-<-trans (abs (x - z)) (abs (x - y) + abs (y - z)) (ε₁ + ε₂) I VII

B-ℚ : (x y : ℚ) (ε : ℚ₊) → 𝓤₀ ̇
B-ℚ x y (ε , 0<ε) = ℚ-metric x y < ε

ℚ-m1a : m1a ℚ B-ℚ
ℚ-m1a x y f = cases γ₁ γ₂ I
 where
  α : ℚ
  α = ℚ-metric x y

  0≤α : 0ℚ ≤ α
  0≤α = ℚ-abs-is-positive (x - y)

  I : (0ℚ < α) ∔ (0ℚ ＝ abs (x - y))
  I = ℚ≤-split 0ℚ α 0≤α

  γ₁ : 0ℚ < α → x ＝ y
  γ₁ l = 𝟘-elim (ℚ<-not-itself α (f (α , l )))

  γ₂ : 0ℚ ＝ abs (x - y) → x ＝ y
  γ₂ e = x         ＝⟨ ℚ-inverse-intro'''' x y                       ⟩
         x - y + y ＝⟨ ap (_+ y) (ℚ-abs-zero-is-zero (x - y) (e ⁻¹)) ⟩
         0ℚ + y    ＝⟨ ℚ-zero-left-neutral y                         ⟩
         y ∎

ℚ-m1b : m1b ℚ B-ℚ
ℚ-m1b x (ε , 0<ε) = transport (_< ε) (ℚ-zero-dist x ⁻¹) 0<ε

ℚ-m2 : m2 ℚ B-ℚ
ℚ-m2 x y (ε , 0<ε) = transport (_< ε) (abs-comm x y)

ℚ-m3 : m3 ℚ B-ℚ
ℚ-m3 x y (ε₁ , 0<ε₁) (ε₂ , 0<ε₂) l B = ℚ<-trans (ℚ-metric x y) ε₁ ε₂ B l

ℚ-m4 : m4 ℚ B-ℚ
ℚ-m4 x y z (ε₁ , 0<ε₁) (ε₂ , 0<ε₂) B₁ B₂ = conclusion α
 where
  α : abs ((x - y) + (y - z)) ≤ (abs (x - y) + abs (y - z))
  α = ℚ-triangle-inequality (x - y) (y - z)

  β : (abs (x - y) + abs (y - z)) < (ε₁ + ε₂)
  β = ℚ<-adding (abs (x - y)) ε₁ (abs(y - z)) ε₂ B₁ B₂

  δ : abs ((x - y) + (y + (- z))) ＝ abs (x - z)
  δ = ap abs (ℚ-add-zero x (- z) y ⁻¹)

  conclusion : abs ((x - y) + (y - z)) ≤ (abs (x - y) + abs (y - z)) → abs (x - z) < (ε₁ + ε₂)
  conclusion l = I (ℚ≤-split (abs ((x - y) + (y - z))) ((abs (x - y) + abs (y - z))) l)
   where
    I : (abs ((x - y) + (y - z)) < (abs (x - y) + abs (y - z)))
      ∔ (abs ((x - y) + (y - z)) ＝ abs (x - y) + abs (y - z))
      → abs (x - z) < (ε₁ + ε₂)
    I (inl l) =  ℚ<-trans (abs (x - z)) ((abs (x - y) + abs (y - z))) (ε₁ + ε₂) γ β
     where
      γ : abs (x - z) < (abs (x - y) + abs (y - z))
      γ = transport (λ k → k < (abs (x - y) + abs (y - z))) δ l
    I (inr e) = transport (_< (ε₁ + ε₂)) (e ⁻¹ ∙ δ) β

ℚ-metric-space : metric-space ℚ
ℚ-metric-space = B-ℚ , ℚ-m1a , ℚ-m1b , ℚ-m2 , ℚ-m3 , ℚ-m4

\end{code}

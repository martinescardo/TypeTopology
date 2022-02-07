\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import OrderNotation --TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-Base -- TypeTopology
open import UF-Subsingletons --TypeTopology
open import UF-PropTrunc -- TypeTopology


open import Rationals
open import RationalsAbs
open import RationalsAddition
open import RationalsNegation
open import RationalsOrder

module MetricSpaceRationals
         (fe : Fun-Ext)
         (pt : propositional-truncations-exist)
         (pe : Prop-Ext)
 where

open import MetricSpaceAltDef pt fe pe

ℚ-metric : ℚ → ℚ → ℚ
ℚ-metric p q = abs (p - q)

ℚ-self-dist : Fun-Ext → (q : ℚ) → ℚ-metric q q ≡ 0ℚ
ℚ-self-dist fe q = ℚ-metric q q ≡⟨ by-definition ⟩
                   abs (q - q)   ≡⟨ ap abs (ℚ-inverse-sum-to-zero fe q) ⟩
                   abs 0ℚ        ≡⟨ by-definition ⟩
                   0ℚ ∎

ℚ-metric-commutes : (p q : ℚ) → ℚ-metric p q ≡ ℚ-metric q p
ℚ-metric-commutes p q = conclusion
 where
  conclusion : ℚ-metric p q ≡ ℚ-metric q p 
  conclusion = ℚ-metric p q                   ≡⟨ by-definition ⟩
               abs (p - q)                    ≡⟨ ℚ-abs-neg-equals-pos fe (p - q) ⟩
               abs (- (p - q))                ≡⟨ by-definition ⟩
               abs (- (p + (- q)))            ≡⟨ ap (λ z → abs (- z)) (ℚ+-comm p (- q)) ⟩
               abs (- ((- q) + p))            ≡⟨ ap abs (ℚ-minus-dist fe (- q) p ⁻¹) ⟩
               abs ((- (- q)) + (- p))        ≡⟨ ap (λ z → abs (z + (- p))) (ℚ-minus-minus fe q ⁻¹) ⟩
               abs (q + (- p))                ≡⟨ by-definition ⟩
               abs (q - p)                    ≡⟨ by-definition ⟩
               ℚ-metric q p                   ∎

inequality-chain-to-metric : (w y z : ℚ) → w ≤ y → y ≤ z → ℚ-metric w z ≡ ℚ-metric w y + ℚ-metric y z
inequality-chain-to-metric w y z l₁ l₂ = conclusion
 where
  l₃ : w ≤ z
  l₃ = ℚ≤-trans fe w y z l₁ l₂
  conclusion : ℚ-metric w z ≡ ℚ-metric w y + ℚ-metric y z
  conclusion = ℚ-metric w z                ≡⟨ by-definition ⟩
               abs (w - z)                 ≡⟨ ℚ-metric-commutes w z ⟩
               abs (z - w)                 ≡⟨ abs-of-pos-is-pos fe (z - w) (ℚ≤-difference-positive fe w z l₃) ⟩
               z - w                       ≡⟨ ℚ-zero-left-neutral fe (z - w) ⁻¹ ⟩
               0ℚ + (z - w)                ≡⟨ ap (_+ (z - w)) (ℚ-inverse-sum-to-zero fe y ⁻¹) ⟩
               y + (- y) + (z - w)         ≡⟨ ℚ+-assoc fe y (- y) (z - w) ⟩
               y + ((- y) + (z - w))       ≡⟨ ap (y +_) (ℚ+-comm (- y) (z - w)) ⟩
               y + (z - w + (- y))         ≡⟨ ap (λ α → y + (α + (- y))) (ℚ+-comm z (- w)) ⟩
               y + ((- w) + z + (- y))     ≡⟨ ℚ+-assoc fe y ((- w) + z) (- y) ⁻¹ ⟩
               y + ((- w) + z) + (- y)     ≡⟨ ap (_+ (- y)) (ℚ+-assoc fe y (- w) z ⁻¹) ⟩
               (y - w) + z + (- y)         ≡⟨ ℚ+-assoc fe (y - w) z (- y) ⟩
               y - w + (z - y)             ≡⟨ ap₂ _+_ (abs-of-pos-is-pos fe (y - w) (ℚ≤-difference-positive fe w y l₁) ⁻¹) (abs-of-pos-is-pos fe (z - y) (ℚ≤-difference-positive fe y z l₂) ⁻¹) ⟩
               abs (y - w) + abs (z - y)   ≡⟨ ap₂ _+_ (ℚ-metric-commutes y w) (ℚ-metric-commutes z y) ⟩
               abs (w - y) + abs (y - z)   ≡⟨ by-definition ⟩
               ℚ-metric w y + ℚ-metric y z ∎

inequality-chain-with-metric : (x y w z ε₁ ε₂ : ℚ) → w ≤ y → y ≤ z → ℚ-metric x y < ε₁ → ℚ-metric w z < ε₂ → ℚ-metric x z < (ε₁ + ε₂)
inequality-chain-with-metric x y w z ε₁ ε₂ l₁ l₂ l₃ l₄ = conclusion 
 where
  from-previous-result : ℚ-metric w z ≡ ℚ-metric w y + ℚ-metric y z
  from-previous-result = inequality-chain-to-metric w y z l₁ l₂
  I : ℚ-metric x z ≡ ℚ-metric (x - y) (z - y)
  I = ℚ-metric x z                  ≡⟨ by-definition ⟩
      abs (x - z)                   ≡⟨ ap abs (ℚ-add-zero fe x (- z) y) ⟩
      abs (x - y + (y - z))         ≡⟨ ap (λ α → abs (x - y + α)) (ℚ+-comm y (- z)) ⟩
      abs (x - y + ((- z) + y))     ≡⟨ ap (λ α → abs (x - y + ((- z) + α))) (ℚ-minus-minus fe y) ⟩
      abs (x - y + ((- z) - (- y))) ≡⟨ ap (λ α → abs (x - y + α)) (ℚ-minus-dist fe z (- y)) ⟩
      abs (x - y - (z - y))         ≡⟨ by-definition ⟩
      ℚ-metric (x - y) (z - y) ∎
      
  II : ℚ-metric (x - y) (z - y) ≤ (abs (x - y) + abs (- (z - y)))
  II = ℚ-triangle-inequality fe (x - y) (- (z - y))
  
  III : (abs (x - y) + abs (- (z - y))) ≡ ℚ-metric x y + ℚ-metric y z
  III = abs (x - y) + abs (- (z - y))   ≡⟨ ap (abs (x - y) +_) (ℚ-abs-neg-equals-pos fe (z - y) ⁻¹) ⟩
        abs (x - y) + abs (z - y)       ≡⟨ ap (abs (x - y) +_) (ℚ-metric-commutes z y) ⟩
        abs (x - y) + ℚ-metric y z      ≡⟨ by-definition ⟩
        ℚ-metric x y + ℚ-metric y z ∎
        
  IV : ℚ-metric (x - y) (z - y) ≤ (ℚ-metric x y + ℚ-metric y z)
  IV = transport (λ α → ℚ-metric (x - y) (z - y) ≤ α) III II
  
  V : ℚ-metric y z ≤ ℚ-metric w z
  V = transport (ℚ-metric y z ≤_) (from-previous-result ⁻¹) ii
   where
    i : ℚ-metric y z ≤ (ℚ-metric y z + ℚ-metric w y)
    i = ℚ≤-addition-preserves-order'' fe (ℚ-metric y z) (ℚ-metric w y) (ℚ-abs-is-positive (w - y))
    ii : ℚ-metric y z ≤ (ℚ-metric w y + ℚ-metric y z)
    ii = transport (ℚ-metric y z ≤_) (ℚ+-comm (ℚ-metric y z) (ℚ-metric w y)) i
    
  VI : (ℚ-metric x y + ℚ-metric w z) < (ε₁ + ε₂)
  VI = ℚ<-adding (ℚ-metric x y) ε₁ (ℚ-metric w z) ε₂ l₃ l₄
  
  VII : ℚ-metric x z ≤ ℚ-metric x y + ℚ-metric w z
  VII = transport (_≤ (ℚ-metric x y + ℚ-metric w z)) (I ⁻¹) ii
   where
    i : (ℚ-metric x y + ℚ-metric y z) ≤ (ℚ-metric x y + ℚ-metric w z)
    i = transport₂ _≤_ (ℚ+-comm (ℚ-metric y z) (ℚ-metric x y)) (ℚ+-comm (ℚ-metric w z) (ℚ-metric x y)) (ℚ≤-addition-preserves-order fe (ℚ-metric y z) (ℚ-metric w z) (ℚ-metric x y) V)
    ii : ℚ-metric (x - y) (z - y) ≤ (ℚ-metric x y + ℚ-metric w z)
    ii = ℚ≤-trans fe (ℚ-metric (x - y) (z - y)) ((ℚ-metric x y + ℚ-metric y z)) ((ℚ-metric x y + ℚ-metric w z)) IV i

  conclusion : ℚ-metric x z < (ε₁ + ε₂)
  conclusion = ℚ≤-<-trans fe (ℚ-metric x z) (ℚ-metric x y + ℚ-metric w z) (ε₁ + ε₂) VII VI

B-ℚ : (x y ε : ℚ) → 0ℚ < ε → 𝓤₀ ̇
B-ℚ x y ε l = ℚ-metric x y < ε

ℚ-m1a : m1a ℚ B-ℚ
ℚ-m1a x y f = I (ℚ≤-split fe 0ℚ (abs (x - y)) (ℚ-abs-is-positive (x - y)))
 where
  α : ℚ
  α = ℚ-metric x y
  I : (0ℚ < abs (x - y)) ∔ (0ℚ ≡ abs (x - y)) → x ≡ y
  I (inl z) = 𝟘-elim (ℚ<-not-itself α ζ)
   where
    ζ : α < α
    ζ = f α z
  I (inr z) = ii
   where
    i : (x - y) ≡ 0ℚ
    i = ℚ-abs-zero-is-zero fe (x - y) (z ⁻¹)
    ii : x ≡ y
    ii = x                      ≡⟨ ℚ-zero-right-neutral fe x ⁻¹ ⟩
         x + 0ℚ                 ≡⟨ ap (x +_) (ℚ-inverse-sum-to-zero fe y ⁻¹) ⟩
         x + (y - y)            ≡⟨ ap (x +_) (ℚ+-comm y (- y)) ⟩
         x + ((- y) + y)        ≡⟨ ℚ+-assoc fe x (- y) y ⁻¹ ⟩
         x + (- y) + y          ≡⟨ ap (_+ y) i ⟩
         0ℚ + y                 ≡⟨ ℚ-zero-left-neutral fe y ⟩ 
         y                      ∎
  
ℚ-m1b : m1b ℚ B-ℚ
ℚ-m1b x y l = transport (λ v → v < y) (ℚ-self-dist fe x ⁻¹) l

ℚ-m2 : m2 ℚ B-ℚ
ℚ-m2 x y ε l₁ B = transport (λ z → z < ε) (ℚ-metric-commutes x y) B

ℚ-m3 : m3 ℚ B-ℚ
ℚ-m3 x y ε₁ ε₂ l₁ l₂ l₃ B = ℚ<-trans (ℚ-metric x y) ε₁ ε₂ B l₃

ℚ-m4 : m4 ℚ B-ℚ
ℚ-m4 x y z ε₁ ε₂ l₁ l₂ B₁ B₂ = conclusion α
 where
  α : abs ((x - y) + (y - z)) ≤ (abs (x - y) + abs (y - z))
  α = ℚ-triangle-inequality fe (x - y) (y - z)

  β : (abs (x - y) + abs (y - z)) < (ε₁ + ε₂)
  β = ℚ<-adding (abs (x - y)) ε₁ (abs(y - z)) ε₂ B₁ B₂

  δ : abs ((x - y) + (y + (- z))) ≡ abs (x - z)
  δ = ap abs (ℚ-add-zero fe x (- z) y ⁻¹)

  conclusion : abs ((x - y) + (y - z)) ≤ (abs (x - y) + abs (y - z)) → abs (x - z) < (ε₁ + ε₂)
  conclusion l = I (ℚ≤-split fe (abs ((x - y) + (y - z))) ((abs (x - y) + abs (y - z))) l) 
   where
    I : (abs ((x - y) + (y - z)) < (abs (x - y) + abs (y - z))) ∔ (abs ((x - y) + (y - z)) ≡ abs (x - y) + abs (y - z)) → abs (x - z) < (ε₁ + ε₂)
    I (inl l) =  ℚ<-trans (abs (x - z)) ((abs (x - y) + abs (y - z))) (ε₁ + ε₂) γ β
     where
      γ : abs (x - z) < (abs (x - y) + abs (y - z))
      γ = transport (λ k → k < (abs (x - y) + abs (y - z))) δ l
    I (inr e) = transport (_< (ε₁ + ε₂)) (e ⁻¹ ∙ δ) β

ℚ-metric-space : metric-space ℚ
ℚ-metric-space = B-ℚ , ℚ-m1a , ℚ-m1b , ℚ-m2 , ℚ-m3 , ℚ-m4


\end{code}

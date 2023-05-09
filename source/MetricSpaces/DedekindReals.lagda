Andrew Sneap, 10 March 2022

In this file, I prove that the Dedekind reals are a complete metric space.
The core result (that cauchy sequences converge) requires cleaning.

\begin{code}
{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --lossy-unification --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.Order
open import UF.Base
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Subsingletons
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Order renaming ( max to ℕmax
                                    ; max-comm to ℕmax-comm
                                    ; max-assoc to ℕmax-assoc)
open import Rationals.Addition
open import Rationals.Type
open import Rationals.Abs
open import Rationals.Negation
open import Rationals.Order
open import Rationals.MinMax
open import Rationals.Multiplication
open import Rationals.Positive renaming (_+_ to _ℚ₊+_)

module MetricSpaces.DedekindReals
  (fe : Fun-Ext)
  (pe : Prop-Ext)
  (pt : propositional-truncations-exist)
 where

open PropositionalTruncation pt

open import Rationals.Limits fe pe pt
open import MetricSpaces.Definition fe pe pt
open import MetricSpaces.Rationals fe pe pt
open import DedekindReals.Type fe pe pt
open import DedekindReals.Properties fe pe pt
open import DedekindReals.Order fe pe pt

\end{code}

We say that two reals are ε-close if we can find a pair of rationals,
one either side of each real such that the the distance between the
furthest value on each side is less than ε.

\begin{code}

record Strict-Order-Chain {𝓤} {𝓥} {𝓦} {𝓣} {𝓧 : Universe}
 (X : 𝓤 ̇) (Y : 𝓥 ̇) (Z : 𝓦 ̇)
 (_<₁_ : X → Y → 𝓣 ̇)
 (_<₂_ : Y → Z → 𝓧 ̇) :  (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓧)⁺ ̇ where
 field
  _<_<_ : X → Y → Z → 𝓦 ⊔ 𝓧 ̇

 infix 30 _<_<_

open Strict-Order-Chain {{...}} public

instance
 Strict-Order-Chain-ℚ-ℚ-ℚ : Strict-Order-Chain ℚ ℚ ℚ _<_ _<_
 _<_<_ {{Strict-Order-Chain-ℚ-ℚ-ℚ}} p q r = (p < q) × (q < r)

 Strict-Order-Chain-ℚ-ℝ-ℚ : Strict-Order-Chain ℚ ℝ ℚ _<_ _<_
 _<_<_ {{Strict-Order-Chain-ℚ-ℝ-ℚ}} p x q = (p < x) × (x < q)

record Order-Chain {𝓤} {𝓥} {𝓦} {𝓣} {𝓧 : Universe}
 (X : 𝓤 ̇) (Y : 𝓥 ̇) (Z : 𝓦 ̇)
 (_≤₁_ : X → Y → 𝓣 ̇)
 (_≤₂_ : Y → Z → 𝓧 ̇) :  (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓧)⁺ ̇ where
 field
  _≤_≤_ : X → Y → Z → 𝓦 ⊔ 𝓧 ̇

 infix 30 _≤_≤_

open Order-Chain {{...}} public

instance
 Order-Chain-ℚ-ℚ-ℚ : Order-Chain ℚ ℚ ℚ _≤_ _≤_
 _≤_≤_ {{Order-Chain-ℚ-ℚ-ℚ}} p q r = (p ≤ q) × (q ≤ r)

B-ℝ : (x y : ℝ) → ℚ₊ → 𝓤₀ ̇
B-ℝ x y ε = ∃ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < y < q) × B-ℚ p q ε

ℝ-m2 : m2 ℝ B-ℝ
ℝ-m2 x y ε = ∥∥-functor γ
 where
  γ : Σ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < y < q) × B-ℚ p q ε
    → Σ (p , q) ꞉ ℚ × ℚ , (p < y < q) × (p < x < q) × B-ℚ p q ε
  γ ((p , q) , l₁ , l₂ , B) = (p , q) , l₂ , l₁ , B

ℝ-m1a-lemma : (x y : ℝ) → ((ε : ℚ₊) → B-ℝ x y ε) → (p : ℚ) → p < x → p < y
ℝ-m1a-lemma x y f p p<x = ∥∥-rec II γ I
 where
  I : ∃ q ꞉ ℚ , (p < q) × (q < x)
  I = rounded-left-d x p p<x

  II : is-prop (p < y)
  II = ∈-is-prop (lower-cut-of y) p

  γ : Σ q ꞉ ℚ , (p < q) × (q < x)
    → p < y
  γ (q , p<q , q<x) = ∥∥-rec II γ' III
   where
    ε₊ : ℚ₊
    ε₊ = q - p , ℚ<-difference-positive p q p<q

    III : ∃ (u , v) ꞉ ℚ × ℚ , (u < x < v) × (u < y < v) × B-ℚ u v ε₊
    III = f ε₊

    γ' : Σ (u , v) ꞉ ℚ × ℚ , (u < x < v) × (u < y < v) × B-ℚ u v ε₊
       → p < y
    γ' ((u , v) , (u<x , x<v) , (u<y , _) , B) = use-rounded-real-L y p u γ'' u<y
     where
      u<v : u < v
      u<v = disjoint-from-real x u v (u<x , x<v)

      IV : abs (u - v) ＝ v - u
      IV = ℚ<-to-abs' u v u<v

      V : v - u < q - p
      V = transport (_< q - p) IV B

      VI : v - u + p < q
      VI = ℚ<-subtraction-preserves-order'' (v - u) q p V

      VII : p + (v - u) < q
      VII = transport (_< q) (ℚ+-comm (v - u) p) VI

      VIII : p < q - (v - u)
      VIII = ℚ<-subtraction-preserves-order''' p (v - u) q VII

      IX : q - (v - u) ＝ u - (v - q)
      IX = q - (v - u)   ＝⟨ ℚ-minus-dist' (v - u) q ⁻¹         ⟩
           - (v - u - q) ＝⟨ ap -_ (ℚ+-rearrange v (- u) (- q)) ⟩
           - (v - q - u) ＝⟨ ℚ-minus-dist' (v - q) u            ⟩
           u - (v - q)   ∎

      X : p < u - (v - q)
      X = transport (p <_) IX VIII

      q<v : q < v
      q<v = disjoint-from-real x q v (q<x , x<v)

      XI : 0ℚ < v - q
      XI = ℚ<-difference-positive q v q<v

      XII : u - (v - q) < u
      XII = ℚ<-subtraction-preserves-order u (v - q) XI

      γ'' : p < u
      γ'' = ℚ<-trans p (u - (v - q)) u X XII

ℝ-m1a : m1a ℝ B-ℝ
ℝ-m1a x y f = ℝ-equality-from-left-cut' x y γ₁ γ₂
 where
  γ₁ : (p : ℚ) → p < x → p < y
  γ₁ = ℝ-m1a-lemma x y f

  f' : (ε : ℚ₊) → B-ℝ y x ε
  f' ε = ℝ-m2 x y ε (f ε)

  γ₂ : (p : ℚ) → p < y → p < x
  γ₂ = ℝ-m1a-lemma y x f'

ℝ-m1b : m1b ℝ B-ℝ
ℝ-m1b x (ε , 0<ε) = ∥∥-functor γ (ℝ-arithmetically-located x ε 0<ε)
 where
  γ : Σ (p , q) ꞉ ℚ × ℚ , ((p < x) × (x < q) × (0ℚ < (q - p)) × (q - p) < ε)
    → Σ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < x < q) × B-ℚ p q (ε , 0<ε)
  γ ((p , q) , p<x , x<q , 0<q-p , q-p<ε) = γ'
   where
    I : abs (q - p) < ε
    I = pos-abs-no-increase (q - p) ε (0<q-p , q-p<ε)

    l : B-ℚ p q (ε , 0<ε)
    l = transport (_< ε) (abs-comm q p) I

    γ' : Σ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < x < q) × B-ℚ p q (ε , 0<ε)
    γ' = (p , q) , (p<x , x<q) , (p<x , x<q) , l

ℝ-m3 : m3 ℝ B-ℝ
ℝ-m3 x y (ε₁ , 0<ε₁) (ε₂ , 0<ε₂) ε₁<ε₂ = ∥∥-functor γ
 where
  γ : Σ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < y < q) × B-ℚ p q (ε₁ , 0<ε₁)
    → Σ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < y < q) × B-ℚ p q (ε₂ , 0<ε₂)
  γ ((p , q) , l₁ , l₂ , B) = (p , q) , l₁ , l₂ , γ'
   where
    γ' : B-ℚ p q (ε₂ , 0<ε₂)
    γ' = ℚ<-trans (abs (p - q)) ε₁ ε₂ B ε₁<ε₂

ℝ-m4 : m4 ℝ B-ℝ
ℝ-m4 x y z (ε₁ , 0<ε₁) (ε₂ , 0<ε₂) B₁ B₂ = ∥∥-functor γ (binary-choice B₁ B₂)
 where
  ε₃ = ε₁ + ε₂
  ε₃' = ε₂ + ε₁
  0<ε₃ = ℚ<-adding-zero ε₁ ε₂ 0<ε₁ 0<ε₂

  γ : (Σ (a , b) ꞉ ℚ × ℚ , (a < x < b) × (a < y < b) × B-ℚ a b (ε₁ , 0<ε₁))
    × (Σ (c , d) ꞉ ℚ × ℚ , (c < y < d) × (c < z < d) × B-ℚ c d (ε₂ , 0<ε₂))
    → (Σ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < z < q) × B-ℚ p q (ε₃ , 0<ε₃))
  γ ( ((a , b) , (a<x , x<b) , (a<y , y<b) , B₃)
    , ((c , d) , (c<y , y<d) , (c<z , z<d) , B₄)) = γ'
   where
    a≤d : a ≤ d
    a≤d = disjoint-from-real' y a d (a<y , y<d)

    c≤b : c ≤ b
    c≤b = disjoint-from-real' y c b (c<y , y<b)

    p = min a c
    q = max b d

    p<x : p < x
    p<x = use-rounded-real-L' x p a (min≤ a c) a<x

    x<q : x < q
    x<q = use-rounded-real-R' x b q (max≤ b d) x<b

    p<z : p < z
    p<z = use-rounded-real-L' z p c (min≤' a c) c<z

    z<q : z < q
    z<q = use-rounded-real-R' z d q (max≤' b d) z<d

    I : (a ≤ c) × (p ＝ a) ∔ (c ≤ a) × (p ＝ c)
    I = min-to-≤ a c

    II : (b ≤ d) × (q ＝ d) ∔ (d ≤ b) × (q ＝ b)
    II = max-to-≤ b d

    ε₁<ε₃ : ε₁ < ε₃
    ε₁<ε₃ = ℚ<-addition-preserves-order'' ε₁ ε₂ 0<ε₂

    ε₂<ε₃' : ε₂ < ε₃'
    ε₂<ε₃' = ℚ<-addition-preserves-order'' ε₂ ε₁ 0<ε₁

    ε₂<ε₃ : ε₂ < ε₃
    ε₂<ε₃ = transport (ε₂ <_) (ℚ+-comm ε₂ ε₁) ε₂<ε₃'

    c₁ : c ≤ b → b ≤ d → abs (a - d) < ε₃
    c₁ c≤b b≤d = inequality-chain-with-metric a b c d ε₁ ε₂ c≤b b≤d B₃ B₄

    c₂ : abs (a - b) < ε₃
    c₂ = ℚ<-trans (abs (a - b)) ε₁ ε₃ B₃ ε₁<ε₃

    c₃ : abs (c - d) < ε₃
    c₃ = ℚ<-trans (abs (c - d)) ε₂ ε₃ B₄ ε₂<ε₃

    c₄' : (d ≤ b) → abs (c - b) < ε₃'
    c₄' d≤b = inequality-chain-with-metric c d a b ε₂ ε₁ a≤d d≤b B₄ B₃

    c₄ : d ≤ b → abs (c - b) < ε₃
    c₄ d≤b = transport (abs (c - b) <_) (ℚ+-comm ε₂ ε₁) (c₄' d≤b)

    γ' : Σ (p , q) ꞉ ℚ × ℚ , (p < x < q) × (p < z < q) × B-ℚ p q (ε₃ , 0<ε₃)
    γ' = (min a c , max b d) , (p<x , x<q) , (p<z , z<q) , (γ'' I II)
     where
      γ'' : (a ≤ c) × (p ＝ a) ∔ (c ≤ a) × (p ＝ c)
          → (b ≤ d) × (q ＝ d) ∔ (d ≤ b) × (q ＝ b)
          → B-ℚ p q (ε₃ , 0<ε₃)
      γ'' (inl (a≤c , e₁)) (inl (b≤d , e₂))
       = transport₂ (λ ■₁ ■₂ → abs (■₁ - ■₂) < ε₃) (e₁ ⁻¹) (e₂ ⁻¹) (c₁ c≤b b≤d)
      γ'' (inl (a≤c , e₁)) (inr (d≤b , e₂))
       = transport₂ (λ ■₁ ■₂ → abs (■₁ - ■₂) < ε₃) (e₁ ⁻¹) (e₂ ⁻¹) c₂
      γ'' (inr (c≤a , e₁)) (inl (b≤d , e₂))
       = transport₂ (λ ■₁ ■₂ → abs (■₁ - ■₂) < ε₃) (e₁ ⁻¹) (e₂ ⁻¹) c₃
      γ'' (inr (a≤c , e₁)) (inr (d≤b , e₂))
       = transport₂ (λ ■₁ ■₂ → abs (■₁ - ■₂) < ε₃) (e₁ ⁻¹) (e₂ ⁻¹) (c₄ d≤b)

ℝ-metric-space : metric-space ℝ
ℝ-metric-space = B-ℝ , ℝ-m1a , ℝ-m1b , ℝ-m2 , ℝ-m3 , ℝ-m4

cauchy-approximation : 𝓤₁ ̇
cauchy-approximation
  = Σ f ꞉ (ℚ₊ → ℝ) , ((ε₁ ε₂ : ℚ₊) → B-ℝ (f ε₁) (f ε₂) (ε₁ ℚ₊+ ε₂))

cauchy-approximation-limit : cauchy-approximation → 𝓤₁ ̇
cauchy-approximation-limit (f , _)
 = Σ l ꞉ ℝ , ((ε₁ ε₂ : ℚ₊) → B-ℝ (f ε₁) l (ε₁ ℚ₊+ ε₂))

cale-rl-lemma : (p q r s : ℚ) → q + r + s ＝ p + r + (q - p + s)
cale-rl-lemma p q r s = γ
 where
  γ : q + r + s ＝ p + r + (q - p + s)
  γ = q + r + s                 ＝⟨ ap (_+ s) (ℚ+-comm q r)                   ⟩
      r + q + s                 ＝⟨ ℚ-inverse-intro' (r + q + s) p            ⟩
      p - p + (r + q + s)       ＝⟨ ℚ+-assoc p (- p) (r + q + s)              ⟩
      p + ((- p) + (r + q + s)) ＝⟨ ap (p +_) (ℚ+-comm (- p) (r + q + s))     ⟩
      p + (r + q + s - p)       ＝⟨ ap (λ ■ → p + (■ - p)) (ℚ+-assoc r q s)   ⟩
      p + (r + (q + s) - p)     ＝⟨ ap (p +_) (ℚ+-assoc r (q + s) (- p))      ⟩
      p + (r + (q + s - p))     ＝⟨ ℚ+-assoc p r (q + s - p) ⁻¹               ⟩
      p + r + (q + s - p)       ＝⟨ ap (p + r +_) (ℚ+-rearrange q (- p) s ⁻¹) ⟩
      p + r + (q - p + s)       ∎

cale-lo-lemma : (p q : ℚ)
              → p < q
              → let ε = 1/5 * (q - p)
                in p + ε + ε < q - ε - ε
cale-lo-lemma p q p<q = γ
 where
  ε' = q - p
  ε = 1/5 * ε'
  0<ε' = ℚ<-difference-positive p q p<q
  0<ε = ℚ<-pos-multiplication-preserves-order 1/5 ε' 0<1/5 0<ε'
  0<2ε = ℚ<-adding-zero ε ε 0<ε 0<ε

  e₁ : 1/5 * ε' + 1/5 * ε' ＝ 2/5 * ε'
  e₁ = ℚ-distributivity' ε' 1/5 1/5 ⁻¹

  e₂ : 2/5 * ε' + 2/5 * ε' ＝ 4/5 * ε'
  e₂ = ℚ-distributivity' ε' 2/5 2/5 ⁻¹

  e₃ : 1/5 * ε' + 4/5 * ε' ＝ 1ℚ * ε'
  e₃ = ℚ-distributivity' ε' 1/5 4/5 ⁻¹

  I : p + ε + ε + ε + (ε + ε) ＝ q - ε - ε + (ε + ε)
  I = p + ε + ε + ε + (ε + ε)       ＝⟨ ap (p + ε + ε + ε +_) e₁                ⟩
      p + ε + ε + ε + 2/5 * ε'      ＝⟨ ap (_+ 2/5 * ε') (ℚ+-assoc (p + ε) ε ε) ⟩
      p + ε + (ε + ε) + 2/5 * ε'    ＝⟨ ap (λ ■ → p + ε + ■ + 2/5 * ε') e₁      ⟩
      p + ε + 2/5 * ε' + 2/5 * ε'   ＝⟨ ℚ+-assoc (p + ε) (2/5 * ε') (2/5 * ε')  ⟩
      p + ε + (2/5 * ε' + 2/5 * ε') ＝⟨ ap (p + ε +_) e₂                        ⟩
      p + ε + 4/5 * ε'              ＝⟨ ℚ+-assoc p ε (4/5 * ε')                 ⟩
      p + (ε + 4/5 * ε')            ＝⟨ ap (p +_) e₃                            ⟩
      p + 1ℚ * (q - p)              ＝⟨ ap (p +_) (ℚ-mult-left-id ε')           ⟩
      p + (q - p)                   ＝⟨ ap (p +_) (ℚ+-comm q (- p))             ⟩
      p + ((- p) + q)               ＝⟨ ℚ+-assoc p (- p) q ⁻¹                   ⟩
      p - p + q                     ＝⟨ ℚ-inverse-intro' q p ⁻¹                 ⟩
      q                             ＝⟨ ℚ-add-zero-twice q ε                    ⟩
      q - ε - ε + ε + ε             ＝⟨ ℚ+-assoc (q - ε - ε) ε ε                ⟩
      q - ε - ε + (ε + ε)           ∎

  II : p + ε + ε + ε ＝ q - ε - ε
  II = ℚ+-right-cancellable (p + ε + ε + ε) (q - ε - ε) (ε + ε) I

  III : p + ε + ε < p + ε + ε + ε
  III = ℚ<-addition-preserves-order'' (p + ε + ε) ε 0<ε

  γ : p + ε + ε < q - ε - ε
  γ = transport (p + ε + ε <_) II III

cale-di-lemma₁ : (p q r s t : ℚ) → p + q + r - (p - s - t) ＝ r + t + (q + s)
cale-di-lemma₁ p q r s t = γ
 where
  I : - (p - s - t) ＝ s + (t - p)
  I = - (p - s - t)       ＝⟨ ap -_ (ℚ+-assoc p (- s) (- t))          ⟩
      - (p + ((- s) - t)) ＝⟨ ap (λ ■ → - (p + ■)) (ℚ-minus-dist s t) ⟩
      - (p - (s + t))     ＝⟨ ℚ-minus-dist' p (s + t)                 ⟩
      s + t - p           ＝⟨ ℚ+-assoc s t (- p)                      ⟩
      s + (t - p)         ∎

  II : q + r + (s + (t - p)) ＝ (- p) + (q + r + s + t)
  II = q + r + (s + (t - p))   ＝⟨ ℚ+-assoc (q + r) s (t - p) ⁻¹   ⟩
       q + r + s + (t - p)     ＝⟨ ℚ+-assoc (q + r + s) t (- p) ⁻¹ ⟩
       q + r + s + t + (- p)   ＝⟨ ℚ+-comm (q + r + s + t) (- p)   ⟩
       (- p) + (q + r + s + t) ∎

  γ : p + q + r - (p - s - t) ＝ r + t + (q + s)
  γ = p + q + r - (p - s - t)       ＝⟨ ap (p + q + r +_) I                    ⟩
      p + q + r + (s + (t - p))     ＝⟨ ap (_+ (s + (t - p))) (ℚ+-assoc p q r) ⟩
      p + (q + r) + (s + (t - p))   ＝⟨ ℚ+-assoc p (q + r) (s + (t - p))       ⟩
      p + (q + r + (s + (t - p)))   ＝⟨ ap (p +_) II                           ⟩
      p + ((- p) + (q + r + s + t)) ＝⟨ ℚ+-assoc p (- p) (q + r + s + t) ⁻¹    ⟩
      p - p + (q + r + s + t)       ＝⟨ ℚ-inverse-intro' (q + r + s + t) p ⁻¹  ⟩
      q + r + s + t                 ＝⟨ ap (λ ■ → ■ + s + t) (ℚ+-comm q r)     ⟩
      r + q + s + t                 ＝⟨ ap (_+ t) (ℚ+-assoc r q s)             ⟩
      r + (q + s) + t               ＝⟨ ℚ+-rearrange r t (q + s) ⁻¹            ⟩
      r + t + (q + s)               ∎

cal-lim-lemma₁ : (p q : ℚ) → 0ℚ < q → p + 1/2 * q < p + q
cal-lim-lemma₁ p q 0<q = ℚ<-addition-preserves-order''' (1/2 * q) q p I
 where
  I : 1/2 * q < q
  I = half-of-pos-is-less q 0<q

cal-lim-lemma₂ : (p q r s : ℚ)
               → p < q
               → q - p < 1/2 * s
               → 0ℚ < r
               → 0ℚ < s
               → abs (p - r - 1/2 * s - q) < r + s
cal-lim-lemma₂ p q r s p<q l₁ 0<r 0<s = γ
 where
  l₂ : 0ℚ < q - p
  l₂ = ℚ<-difference-positive p q p<q

  l₃ : 0ℚ < 1/2 * s
  l₃ = ℚ<-pos-multiplication-preserves-order 1/2 s 0<1/2 0<s

  l₄ : 0ℚ < r + 1/2 * s
  l₄ = ℚ<-adding-zero r (1/2 * s) 0<r l₃

  I : abs (p - r - 1/2 * s - q) ＝ abs (q - p + (r + 1/2 * s))
  I = abs (p - r - 1/2 * s - q)         ＝⟨ i   ⟩
      abs (q - (p - r - 1/2 * s))       ＝⟨ ii  ⟩
      abs (q + (1/2 * s - (p - r)))     ＝⟨ iii ⟩
      abs (q + (1/2 * s + (r - p)))     ＝⟨ iv  ⟩
      abs (q + (r - p + 1/2 * s))       ＝⟨ v   ⟩
      abs (q + ((- p) + r + 1/2 * s))   ＝⟨ vi  ⟩
      abs (q + ((- p) + (r + 1/2 * s))) ＝⟨ vii ⟩
      abs (q - p + (r + 1/2 * s))       ∎
   where
    i   = abs-comm (p - r - 1/2 * s) q
    ii  = ap (λ ■ → abs (q + ■)) (ℚ-minus-dist' (p - r) (1/2 * s))
    iii = ap (λ ■ → abs (q + (1/2 * s + ■))) (ℚ-minus-dist' p r)
    iv  = ap (λ ■ → abs (q + ■)) (ℚ+-comm (1/2 * s) (r - p))
    v   = ap (λ ■ → abs (q + (■ + 1/2 * s))) (ℚ+-comm r (- p))
    vi  = ap (λ ■ → abs (q + ■)) (ℚ+-assoc (- p) r (1/2 * s))
    vii = ap abs (ℚ+-assoc q (- p) (r + 1/2 * s) ⁻¹)

  II : abs (q - p + (r + 1/2 * s)) ≤ abs (q - p) + abs (r + 1/2 * s)
  II = ℚ-triangle-inequality (q - p) (r + 1/2 * s)

  e₁ : abs (q - p) ＝ q - p
  e₁ = abs-of-pos-is-pos' (q - p) l₂

  e₂ : abs (r + 1/2 * s) ＝ r + 1/2 * s
  e₂ = abs-of-pos-is-pos' (r + 1/2 * s) l₄

  III : abs (q - p) + abs (r + 1/2 * s) ＝ q - p + (1/2 * s + r)
  III = abs (q - p) + abs (r + 1/2 * s) ＝⟨ ap (_+ abs (r + 1/2 * s)) e₁        ⟩
        q - p + abs (r + 1/2 * s)       ＝⟨ ap (q - p +_) e₂                    ⟩
        q - p + (r + 1/2 * s)           ＝⟨ ap (q - p +_) (ℚ+-comm r (1/2 * s)) ⟩
        q - p + (1/2 * s + r)           ∎

  IV : abs (q - p + (r + 1/2 * s)) ≤ q - p + (1/2 * s + r)
  IV = transport (abs (q - p + (r + 1/2 * s)) ≤_) III II

  V : q - p + (1/2 * s + r) < 1/2 * s + (1/2 * s + r)
  V = ℚ<-addition-preserves-order (q - p) (1/2 * s) (1/2 * s + r) l₁

  VI : abs (q - p + (r + 1/2 * s)) < 1/2 * s + (1/2 * s + r)
  VI = ℚ≤-<-trans
        (abs (q - p + (r + 1/2 * s)))
         (q - p + (1/2 * s + r))
          (1/2 * s + (1/2 * s + r))
           IV V

  VII : 1/2 * s + (1/2 * s + r) ＝ r + s
  VII = 1/2 * s + (1/2 * s + r) ＝⟨ ℚ+-assoc (1/2 * s) (1/2 * s) r ⁻¹ ⟩
        1/2 * s + 1/2 * s + r   ＝⟨ ap (_+ r) (ℚ-into-half' s ⁻¹)     ⟩
        s + r                   ＝⟨ ℚ+-comm s r                       ⟩
        r + s                   ∎

  γ : abs (p - r - 1/2 * s - q) < r + s
  γ = transport₂ _<_ (I ⁻¹) VII VI

cal-lim-lemma₃ : (p q r s : ℚ)
               → p < q
               → q - p < 1/2 * s
               → 0ℚ < r
               → 0ℚ < s
               → abs (p - (q + r + 1/2 * s)) < r + s
cal-lim-lemma₃ p q r s p<q l₁ 0<r 0<s = γ
 where
  s' = 1/2 * s

  I : abs (p - r - s' - q) < r + s
  I = cal-lim-lemma₂ p q r s p<q l₁ 0<r 0<s

  II : p - r - s' - q ＝ p - (q + r + s')
  II = p - r - s' - q         ＝⟨ ℚ+-assoc (p - r) (- s') (- q)         ⟩
       p - r + ((- s') - q)   ＝⟨ ap (p - r +_) (ℚ-minus-dist s' q)     ⟩
       p - r - (s' + q)       ＝⟨ ap (λ ■ → p - r - ■) (ℚ+-comm s' q)   ⟩
       p - r - (q + s')       ＝⟨ ℚ+-assoc p (- r) (- (q + s'))         ⟩
       p + ((- r) - (q + s')) ＝⟨ ap (p +_) (ℚ-minus-dist r (q + s'))   ⟩
       p - (r + (q + s'))     ＝⟨ ap (λ ■ → p - ■) (ℚ+-assoc r q s' ⁻¹) ⟩
       p - (r + q + s')       ＝⟨ ap (λ ■ → p - (■ + s')) (ℚ+-comm r q) ⟩
       p - (q + r + s')       ∎

  III : abs (p - r - s' - q) ＝ abs (p - (q + r + s'))
  III = ap abs II

  γ : abs (p - (q + r + s')) < r + s
  γ = transport (_< r + s) III I

cal-L cal-R : (ca : cauchy-approximation) → 𝓟 ℚ
cal-L (f , _) p
 = (∃ (ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , _)) ꞉ ℚ₊ × ℚ₊ , (p + ε₁ + ε₂) < f ε₁₊)
 , ∃-is-prop

cal-R (f , _) q
 = (∃ (ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , _)) ꞉ ℚ₊ × ℚ₊ , f ε₁₊ < q - ε₁ - ε₂)
 , ∃-is-prop

cal-il : (ca : cauchy-approximation) → inhabited-left (cal-L ca)
cal-il (f , α) = ∥∥-functor γ (inhabited-from-real-L (f 1ℚ₊))
 where
  I : (p : ℚ) → p ＝ p - 1ℚ - 1ℚ + 1ℚ + 1ℚ
  I p = ℚ-add-zero-twice p 1ℚ

  II : (p : ℚ) → p < f 1ℚ₊ → p - 1ℚ - 1ℚ + 1ℚ + 1ℚ < f 1ℚ₊
  II p p<f1 = transport (_< f 1ℚ₊) (I p) p<f1

  γ : Σ p ꞉ ℚ , p < f 1ℚ₊
    → Σ p ꞉ ℚ , p ∈ cal-L (f , α)
  γ (p , p<f1) = p - 1ℚ - 1ℚ , ∣ (1ℚ₊ , 1ℚ₊) , II p p<f1 ∣

cal-ir : (ca : cauchy-approximation) → inhabited-right (cal-R ca)
cal-ir (f , α) = ∥∥-functor γ (inhabited-from-real-R (f 1ℚ₊))
 where
  I : (q : ℚ) → q ＝ q + 1ℚ + 1ℚ - 1ℚ - 1ℚ
  I q = ℚ-add-zero-twice' q 1ℚ

  II : (q : ℚ) → f 1ℚ₊ < q → f 1ℚ₊ < q + 1ℚ + 1ℚ - 1ℚ - 1ℚ
  II q f1<q = transport (f 1ℚ₊ <_) (I q) f1<q

  γ : Σ q ꞉ ℚ , f 1ℚ₊ < q
    → Σ q ꞉ ℚ , q ∈ cal-R (f , α)
  γ (q , f1<q) = q + 1ℚ + 1ℚ , ∣ (1ℚ₊ , 1ℚ₊) , II q f1<q ∣

cal-rl : (ca : cauchy-approximation) → rounded-left (cal-L ca)
cal-rl (f , α) p = ∥∥-functor γ₁ , ∥∥-rec ∃-is-prop γ₂
 where
  L = cal-L (f , α)

  γ₁ : Σ (ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , _)) ꞉ ℚ₊ × ℚ₊ , (p + ε₁ + ε₂) < f ε₁₊
     → Σ q ꞉ ℚ , p < q × q ∈ L
  γ₁ ((ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , 0<ε₂)) , l) = p + ε₃ , γ , γ'
   where
    ε₃ = 1/2 * ε₂
    0<ε₃ = halving-preserves-order' ε₂ 0<ε₂

    γ : p < p + ε₃
    γ = ℚ<-addition-preserves-order'' p (1/2 * ε₂) 0<ε₃

    I : p + ε₁ + ε₂ ＝ p + ε₃ + ε₁ + ε₃
    I = p + ε₁ + ε₂        ＝⟨ ℚ+-rearrange p ε₁ ε₂                    ⟩
        p + ε₂ + ε₁        ＝⟨ ap (λ - → p + - + ε₁) (ℚ-into-half' ε₂) ⟩
        p + (ε₃ + ε₃) + ε₁ ＝⟨ ap (_+ ε₁) (ℚ+-assoc p ε₃ ε₃ ⁻¹)        ⟩
        p + ε₃ + ε₃ + ε₁   ＝⟨ ℚ+-rearrange (p + ε₃) ε₁ ε₃ ⁻¹          ⟩
        p + ε₃ + ε₁ + ε₃   ∎

    II : p + ε₃ + ε₁ + ε₃ < f ε₁₊
    II = transport (_< f ε₁₊) I l

    γ' : (p + ε₃) ∈ L
    γ' = ∣ (ε₁₊ , ε₃ , 0<ε₃) , II ∣

  γ₂ : Σ q ꞉ ℚ , p < q × q ∈ L
     → ∃ (ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , _)) ꞉ ℚ₊ × ℚ₊ , (p + ε₁ + ε₂) < f ε₁₊
  γ₂ (q , p<q , l) = ∥∥-functor γ l
   where
    γ : Σ (ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , _)) ꞉ ℚ₊ × ℚ₊ , (q + ε₁ + ε₂) < f ε₁₊
      → Σ (ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , _)) ꞉ ℚ₊ × ℚ₊ , (p + ε₁ + ε₂) < f ε₁₊
    γ ((ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , 0<ε₂)) , l') = (ε₁₊ , ε₄ , 0<ε₄) , γ'
     where
      ε₃ = q - p
      0<ε₃ = ℚ<-difference-positive p q p<q
      ε₄ = ε₃ + ε₂
      0<ε₄ = ℚ<-adding-zero ε₃ ε₂ 0<ε₃ 0<ε₂

      I : q + ε₁ + ε₂ ＝ p + ε₁ + ((q - p) + ε₂)
      I = cale-rl-lemma p q ε₁ ε₂

      γ' : p + ε₁ + ε₄ < f ε₁₊
      γ' = transport (_< f ε₁₊) I l'

cal-rr : (ca : cauchy-approximation) → rounded-right (cal-R ca)
cal-rr (f , α) q = ∥∥-functor γ₁ , ∥∥-rec ∃-is-prop γ₂
 where
  R = cal-R (f , α)

  γ₁ : Σ (ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , _)) ꞉ ℚ₊ × ℚ₊ , f ε₁₊ < q - ε₁ - ε₂
     → Σ p ꞉ ℚ , p < q × p ∈ R
  γ₁ ((ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , 0<ε₂)) , l) = q - ε₃ , γ , γ'
   where
    ε₃ = 1/2 * ε₂
    0<ε₃ = halving-preserves-order' ε₂ 0<ε₂

    γ : q - ε₃ < q
    γ = ℚ<-subtraction-preserves-order q ε₃ 0<ε₃

    I : q - ε₁ - ε₂ ＝ q - ε₃ - ε₁ - ε₃
    I = q - ε₁ - ε₂            ＝⟨ ℚ+-rearrange q (- ε₁) (- ε₂)             ⟩
        q - ε₂ - ε₁            ＝⟨ ap (λ α → q - α - ε₁) (ℚ-into-half' ε₂)  ⟩
        q - (ε₃ + ε₃) - ε₁     ＝⟨ ap (λ α → q + α - ε₁) i                  ⟩
        q + ((- ε₃) - ε₃) - ε₁ ＝⟨ ap (_- ε₁) (ℚ+-assoc q (- ε₃) (- ε₃) ⁻¹) ⟩
        q - ε₃ - ε₃ - ε₁       ＝⟨ ℚ+-rearrange (q - ε₃) (- ε₁) (- ε₃) ⁻¹   ⟩
        q - ε₃ - ε₁ - ε₃       ∎
     where
      i : - (ε₃ + ε₃) ＝ (- ε₃) - ε₃
      i = ℚ-minus-dist ε₃ ε₃ ⁻¹

    II : f ε₁₊ < q - ε₃ - ε₁ - ε₃
    II = transport (f ε₁₊ <_) I l

    γ' : (q - ε₃) ∈ R
    γ' = ∣ (ε₁₊ , ε₃ , 0<ε₃) , II ∣

  γ₂ : Σ p ꞉ ℚ , p < q × p ∈ R
     → ∃ (ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , _)) ꞉ ℚ₊ × ℚ₊ , f ε₁₊ < q - ε₁ - ε₂
  γ₂ (p , p<q , l) = ∥∥-functor γ l
   where
    γ : Σ (ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , _)) ꞉ ℚ₊ × ℚ₊ , f ε₁₊ < p - ε₁ - ε₂
      → Σ (ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , _)) ꞉ ℚ₊ × ℚ₊ , f ε₁₊ < q - ε₁ - ε₂
    γ ((ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , 0<ε₂)) , l') = (ε₁₊ , ε₄ , 0<ε₄) , γ'
     where
      ε₃ = q - p
      0<ε₃ = ℚ<-difference-positive p q p<q
      ε₄ = ε₃ + ε₂
      0<ε₄ = ℚ<-adding-zero ε₃ ε₂ 0<ε₃ 0<ε₂

      I : p - q - ε₂ ＝ - ε₄
      I = p - q - ε₂       ＝⟨ ap (_- ε₂) (ℚ-minus-dist'' p q) ⟩
          (- (q - p)) - ε₂ ＝⟨ ℚ-minus-dist (q - p) ε₂         ⟩
          - ε₄             ∎

      II : p - ε₁ - ε₂ ＝ q - ε₁ - ε₄
      II = p - ε₁ - ε₂           ＝⟨ cale-rl-lemma q p (- ε₁) (- ε₂) ⟩
           q - ε₁ + (p - q - ε₂) ＝⟨ ap (q - ε₁ +_) I                ⟩
           q - ε₁ - ε₄           ∎

      γ' : f ε₁₊ < q - ε₁ - ε₄
      γ' = transport (f ε₁₊ <_) II l'

cal-lo : (ca : cauchy-approximation) → located (cal-L ca) (cal-R ca)
cal-lo (f , α) p q p<q = ∥∥-functor γ II
   where
    ε₁ = q - p
    0<ε₁ = ℚ<-difference-positive p q p<q

    ε₂ = 1/5 * ε₁
    0<ε₂ = ℚ<-pos-multiplication-preserves-order 1/5 ε₁ 0<1/5 0<ε₁
    ε₂₊ = ε₂ , 0<ε₂

    I : p + ε₂ + ε₂ < q - ε₂ - ε₂
    I = cale-lo-lemma p q p<q

    II : (p + ε₂ + ε₂ < f ε₂₊) ∨ (f ε₂₊ < q - ε₂ - ε₂)
    II = located-from-real (f (ε₂ , 0<ε₂)) (p + ε₂ + ε₂) (q - ε₂ - ε₂) I

    γ : (p + ε₂ + ε₂ < f ε₂₊) ∔ (f ε₂₊ < q - ε₂ - ε₂)
      → p ∈ cal-L (f , α) ∔ q ∈ cal-R (f , α)
    γ (inl l) = inl ∣ ((ε₂ , 0<ε₂) , (ε₂ , 0<ε₂)) , l ∣
    γ (inr r) = inr ∣ ((ε₂ , 0<ε₂) , (ε₂ , 0<ε₂)) , r ∣

cal-di : (ca : cauchy-approximation) → disjoint (cal-L ca) (cal-R ca)
cal-di (f , α) = disjoint→trans L R (cal-lo (f , α)) γ
 where
  L = cal-L (f , α)
  R = cal-R (f , α)

  γ : (p : ℚ) → ¬ (p ∈ L × p ∈ R)
  γ p (p<y , y<p) = ∥∥-rec 𝟘-is-prop γ' (binary-choice p<y y<p)
   where
    γ' : (Σ (ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , _)) ꞉ ℚ₊ × ℚ₊ , (p + ε₁ + ε₂) < f ε₁₊)
       × (Σ (ε₃₊@(ε₃ , 0<ε₃) , (ε₄ , _)) ꞉ ℚ₊ × ℚ₊ , f ε₃₊ < (p - ε₃ - ε₄))
       → 𝟘
    γ' ( ((ε₁₊@(ε₁ , 0<ε₁) , (ε₂ , 0<ε₂)) , l₁)
       , ((ε₃₊@(ε₃ , 0<ε₃) , (ε₄ , 0<ε₄)) , l₂)) = γ₂
     where
      γ₁ : Σ (a , b) ꞉ ℚ × ℚ , (a < f (ε₁ , 0<ε₁) < b)
                             × (a < f (ε₃ , 0<ε₃) < b)
                             × abs (a - b) < ε₁ + ε₃
         → 𝟘
      γ₁ ((a , b) , (l₃ , l₄) , (l₅ , l₆) , l₇) = γ''
       where
        ε₅ = ε₂ + ε₄
        0<ε₅ = ℚ<-adding-zero ε₂ ε₄ 0<ε₂ 0<ε₄

        a<b : a < b
        a<b = disjoint-from-real (f ε₁₊) a b (l₃ , l₄)

        I : p + ε₁ + ε₂ < b
        I = disjoint-from-real (f ε₁₊) (p + ε₁ + ε₂) b (l₁ , l₄)

        II : a < p - ε₃ - ε₄
        II = disjoint-from-real (f ε₃₊) a (p - ε₃ - ε₄) (l₅ , l₂)

        III : - (p - ε₃ - ε₄) < - a
        III = ℚ<-swap a (p - ε₃ - ε₄) II

        IV : p + ε₁ + ε₂ - (p - ε₃ - ε₄) < b - a
        IV = ℚ<-adding (p + ε₁ + ε₂) b (- (p - ε₃ - ε₄)) (- a) I III

        V : 0ℚ < b - a
        V = ℚ<-difference-positive a b a<b

        VI : abs (a - b) ＝ b - a
        VI = ℚ<-to-abs' a b a<b

        VII : b - a < ε₁ + ε₃
        VII = transport (_< ε₁ + ε₃) VI l₇

        VIII : p + ε₁ + ε₂ - (p - ε₃ - ε₄) < ε₁ + ε₃
        VIII = ℚ<-trans (p + ε₁ + ε₂ - (p - ε₃ - ε₄)) (b - a) (ε₁ + ε₃) IV VII

        IX : p + ε₁ + ε₂ - (p - ε₃ - ε₄) ＝ ε₂ + ε₄ + (ε₁ + ε₃)
        IX = cale-di-lemma₁ p ε₁ ε₂ ε₃ ε₄

        X : ε₂ + ε₄ + (ε₁ + ε₃) < ε₁ + ε₃
        X = transport (_< ε₁ + ε₃) IX VIII

        XI : ε₂ + ε₄ < 0ℚ
        XI = ℚ<-subtraction-order' (ε₂ + ε₄) (ε₁ + ε₃) X

        XII : 0ℚ < 0ℚ
        XII = ℚ<-trans 0ℚ (ε₂ + ε₄) 0ℚ 0<ε₅ XI

        γ'' : 𝟘
        γ'' = ℚ<-not-itself 0ℚ XII

      γ₂ : 𝟘
      γ₂ = ∥∥-rec 𝟘-is-prop γ₁ (α ε₁₊ ε₃₊)

ca-limit : (ca : cauchy-approximation) → ℝ
ca-limit ca = (L , R) , il , ir , rl , rr , di , lo
 where
  L = cal-L ca
  R = cal-R ca

  il : inhabited-left L
  il = cal-il ca

  ir : inhabited-right R
  ir = cal-ir ca

  rl : rounded-left L
  rl = cal-rl ca

  rr : rounded-right R
  rr = cal-rr ca

  lo : located L R
  lo = cal-lo ca

  di : disjoint L R
  di = cal-di ca

ca-limit-is-limit : (ca : cauchy-approximation) → cauchy-approximation-limit ca
ca-limit-is-limit (f , α) = y , y-is-limit
 where
  y = ca-limit (f , α)

  y-is-limit : (ε₁ ε₂ : ℚ₊) → B-ℝ (f ε₁) y (ε₁ ℚ₊+ ε₂)
  y-is-limit ε₁₊@(ε₁ , 0<ε₁) ε₂₊@(ε₂ , 0<ε₂) = ∥∥-rec ∃-is-prop γ I
   where
    ε₃ = 1/2 * ε₂
    0<ε₃ = halving-preserves-order' ε₂ 0<ε₂

    ε₄ = ε₁ + ε₃
    0<ε₄ = ℚ<-adding-zero ε₁ ε₃ 0<ε₁ 0<ε₃

    I : ∃ (p , q) ꞉ ℚ × ℚ , (p < f ε₁₊) × (f ε₁₊ < q)
                          × (0ℚ < q - p) × (q - p < ε₃)
    I = ℝ-arithmetically-located (f ε₁₊) ε₃ 0<ε₃

    γ : Σ (p , q) ꞉ ℚ × ℚ , (p < f ε₁₊) × (f ε₁₊ < q)
                          × (0ℚ < q - p) × (q - p < ε₃)
      → ∃ (p , r) ꞉ ℚ × ℚ , (p < (f ε₁₊) < r)
                          × (p < y < r)
                          × B-ℚ p r (ε₁₊ ℚ₊+ ε₂₊)
    γ ((p , q) , l₁ , l₂ , l₃ , l₄) = ∥∥-functor γ₁ γ₂
     where
      p<q : p < q
      p<q = disjoint-from-real (f ε₁₊) p q (l₁ , l₂)

      II : q < q + ε₁ + ε₃
      II = ℚ-addition-order q ε₁ ε₃ 0<ε₄

      III : f ε₁₊ < q + ε₁ + ε₃ - ε₁ - ε₃
      III = transport (f ε₁₊ <_) (ℚ-add-zero-twice'' q ε₁ ε₃) l₂

      IV : p - ε₁ - ε₃ + ε₁ + ε₃ < f ε₁₊
      IV = transport (_< f ε₁₊) (ℚ-add-zero-twice''' p ε₁ ε₃) l₁

      V : (p - ε₁ - ε₃) <ℚ p
      V = ℚ-subtraction-order p ε₁ ε₃ 0<ε₄

      l₅ : f ε₁₊ < q + ε₁ + ε₃
      l₅ = use-rounded-real-R (f ε₁₊) q (q + ε₁ + ε₃) II l₂

      l₆ : y < q + ε₁ + ε₃
      l₆ = ∣ (ε₁₊ , ε₃ , 0<ε₃) , III ∣

      l₇ : p - ε₁ - ε₃ < f ε₁₊
      l₇ = use-rounded-real-L (f ε₁₊) (p - ε₁ - ε₃) p V l₁

      l₈ : p - ε₁ - ε₃ < y
      l₈ = ∣ (ε₁₊ , ε₃ , 0<ε₃) , IV ∣

      VI : ε₁ + ε₃ < ε₁ + ε₂
      VI = cal-lim-lemma₁ ε₁ ε₂ 0<ε₂

      γ' : abs (p - ε₁ - ε₃ - q) < ε₁ + ε₂
      γ' = cal-lim-lemma₂ p q ε₁ ε₂ p<q l₄ 0<ε₁ 0<ε₂

      γ'' : abs (p - (q + ε₁ + ε₃)) < ε₁ + ε₂
      γ'' = cal-lim-lemma₃ p q ε₁ ε₂ p<q l₄ 0<ε₁ 0<ε₂

      γ₁ : (p < y) ∔ (y < q)
         → Σ (p , r) ꞉ ℚ × ℚ , (p < f ε₁₊ < r)
                             × (p < y < r)
                             × B-ℚ p r (ε₁₊ ℚ₊+ ε₂₊)
      γ₁ (inl p<y) = (p , q + ε₁ + ε₃) , (l₁ , l₅) , (p<y , l₆) , γ''
      γ₁ (inr y<q) = (p - ε₁ - ε₃ , q) , (l₇ , l₂) , (l₈ , y<q) , γ'

      γ₂ : (p < y) ∨ (y < q)
      γ₂ = located-from-real y p q p<q

{-
Proof was 500 lines
-}

-- RealsCauchySequence : (S : ℕ → ℝ) → 𝓤₀ ̇
-- RealsCauchySequence = cauchy-sequence ℝ ℝ-metric-space


-- modulus-of-convergence' : (S : ℕ → ℝ)
--                         → (RCS : RealsCauchySequence S)
--                         → Σ M ꞉ (ℚ₊ → ℕ) , ((ε : ℚ) → (l : 0ℚ < ε) → (m n : ℕ) → M (ε , l) ≤ m → M (ε , l) ≤ n → B-ℝ (S m) (S n) ε l)
-- modulus-of-convergence' S RCS = II I
--  where
--   condition : (ε : ℚ₊) → ℕ → 𝓤₀ ̇
--   condition (ε , l) N = (m n : ℕ) → N ≤ m → N ≤ n → B-ℝ (S m) (S n) ε l
--   I : Σ M ꞉ (ℚ₊ → ℕ) , ((x : ℚ₊) → condition x (M x))
--   I = generalised-dependent-type-universal-property (λ _ → ℕ) condition RCS
--   II : Σ M ꞉ (ℚ₊ → ℕ) , (((ε , l) : ℚ₊) → condition _ (M _)) → Sigma (ℚ₊ → ℕ)
--                                                                  (λ M → (ε : ℚ) (l : 0ℚ <  ε) (m n : ℕ) → M (ε , l) ≤ m → M (ε , l) ≤ n → B-ℝ (S m) (S n) ε l)
--   II (M , f) = M , (λ ε l m n x x₁ → f (ε , l) m n x x₁)

-- mod-convergence-property : (S : ℕ → ℝ) → (RCS : RealsCauchySequence S)
--                          → ((M , f) : Σ M ꞉ (ℚ₊ → ℕ) , ((ε : ℚ) → (l : 0ℚ < ε) → (m n : ℕ) → M (ε , l) ≤ m → M (ε , l) ≤ n → B-ℝ (S m) (S n) ε l))
--                          → ((ε  , l₁) : ℚ₊) → ((δ , l₂) : ℚ₊)
--                          → B-ℝ (S (M (1/2 * δ , halving-preserves-order' δ l₂))) (S (M (1/2 * ε , halving-preserves-order' ε l₁))) (1/2 * (δ + ε)) (ℚ<-pos-multiplication-preserves-order 1/2 (δ + ε) 0<1/2 (ℚ<-adding-zero δ ε l₂ l₁))
-- mod-convergence-property S RCS (M , f) (ε , l₁) (δ , l₂) = B-ℝ-ε-transport (S Mδ/2) (S Mε/2) (1/2 * δ + 1/2 * ε) (1/2 * (δ + ε)) I II III use-triangle-inequality
--  where
--   1/2-delta-pos : 0ℚ < 1/2 * δ
--   1/2-delta-pos = halving-preserves-order' δ l₂
--   1/2-epsilon-pos : 0ℚ < 1/2 * ε
--   1/2-epsilon-pos = halving-preserves-order' ε l₁
--   Mε/2 : ℕ
--   Mε/2 = M (1/2 * ε , 1/2-epsilon-pos)
--   Mδ/2 : ℕ
--   Mδ/2 = M (1/2 * δ , 1/2-delta-pos)
--   yₙ : ℕ
--   yₙ = ℕmax Mδ/2 Mε/2
--   delta-y : B-ℝ (S Mδ/2) (S yₙ) (1/2 * δ) 1/2-delta-pos
--   delta-y = f (1/2 * δ) 1/2-delta-pos Mδ/2 yₙ (≤-refl Mδ/2) (max-≤-upper-bound Mδ/2 Mε/2)
--   epsilon-y : B-ℝ (S Mε/2) (S yₙ) (1/2 * ε) 1/2-epsilon-pos
--   epsilon-y = f (1/2 * ε) 1/2-epsilon-pos Mε/2 yₙ (≤-refl Mε/2) (transport (Mε/2 ≤_) (ℕmax-comm Mε/2 Mδ/2) (max-≤-upper-bound Mε/2 Mδ/2))
--   y-epsilon : B-ℝ (S yₙ) (S Mε/2) (1/2 * ε) 1/2-epsilon-pos
--   y-epsilon = ℝ-m2 (S Mε/2) (S yₙ) (1/2 * ε) 1/2-epsilon-pos epsilon-y
--   use-triangle-inequality : B-ℝ (S Mδ/2) (S Mε/2) (1/2 * δ + 1/2 * ε) (ℚ<-adding-zero (1/2 * δ) (1/2 * ε) 1/2-delta-pos 1/2-epsilon-pos)
--   use-triangle-inequality = ℝ-m4 (S Mδ/2) (S yₙ) (S Mε/2) (1/2 * δ) (1/2 * ε) 1/2-delta-pos 1/2-epsilon-pos delta-y y-epsilon
--   I : 1/2 * δ + 1/2 * ε ＝ 1/2 * (δ + ε)
--   I = ℚ-distributivity 1/2 δ ε ⁻¹
--   III : 0ℚ < 1/2 * (δ + ε)
--   III = ℚ<-pos-multiplication-preserves-order 1/2 (δ + ε) 0<1/2 (ℚ<-adding-zero δ ε l₂ l₁)
--   II : 0ℚ < 1/2 * δ + 1/2 * ε
--   II = transport (0ℚ <_) (I ⁻¹) III

-- ℝ-cauchy-sequences-are-convergent : (S : ℕ → ℝ) → cauchy→convergent ℝ ℝ-metric-space S
-- ℝ-cauchy-sequences-are-convergent S RCS = I (modulus-of-convergence' S RCS)
--  where
--   I : Σ M ꞉ (ℚ₊ → ℕ) , ((ε : ℚ) → (l : 0ℚ < ε) (m n : ℕ) → M (ε , l) ≤ m → M (ε , l) ≤ n → B-ℝ (S m) (S n) ε l) → convergent-sequence ℝ ℝ-metric-space S
--   I (M , f) = II (cauchy-approximation-limit-exists property-satisfies-cauchy-approximation)
--    where
--     by-convergence-property : ((ε , l₁) : ℚ₊)
--                             → ((δ , l₂) : ℚ₊)
--                             → B-ℝ (S (M (1/2 * δ , halving-preserves-order' δ l₂))) (S (M (1/2 * ε , halving-preserves-order' ε l₁))) (1/2 * (δ + ε)) (ℚ<-pos-multiplication-preserves-order 1/2 (δ + ε) 0<1/2 (ℚ<-adding-zero δ ε l₂ l₁))
--     by-convergence-property = mod-convergence-property S RCS (M , f)

--     property-satisfies-cauchy-approximation : cauchy-approximation
--     property-satisfies-cauchy-approximation = (λ (ε , l) → S (M ((1/2 * ε) , halving-preserves-order' ε l))) , sub-proof
--      where
--       sub-proof : ((ε , l) (δ , l₂) : ℚ₊) → B-ℝ (S (M (1/2 * ε , halving-preserves-order' ε l))) (S (M (1/2 * δ , halving-preserves-order' δ l₂))) (ε + δ) (ℚ<-adding-zero ε δ l l₂)
--       sub-proof (ε , l) (δ , l₂) = ℝ-m3 (S (M (1/2 * ε , halving-preserves-order' ε l))) (S (M (1/2 * δ , halving-preserves-order' δ l₂))) (1/2 * (ε + δ)) (ε + δ) (ℚ<-pos-multiplication-preserves-order 1/2 (ε + δ) 0<1/2 less) less (half-of-pos-is-less (ε + δ) less) (by-convergence-property (δ , l₂) (ε , l))
--        where
--         less : 0ℚ <ℚ ε + δ
--         less = ℚ<-adding-zero ε δ l l₂
--     II : Σ y ꞉ ℝ , (((ε , l₁) : ℚ₊) → ((δ , l₂) : ℚ₊) → B-ℝ (S (M (1/2 * ε  , halving-preserves-order' ε l₁))) y (ε + δ) (ℚ<-adding-zero ε δ l₁ l₂)) → convergent-sequence ℝ ℝ-metric-space S
--     II (y , g) = ∣ y , III ∣
--      where
--       III : ((ε , l) : ℚ₊) → Σ N ꞉ ℕ , ((n : ℕ) → N < n → B-ℝ y (S n) ε l)
--       III (ε , l) = (M (1/4 * ε , l₅)) , IV
--        where
--         l₅ : 0ℚ < 1/4 * ε
--         l₅ = ℚ<-pos-multiplication-preserves-order 1/4 ε (0 , refl) l
--         l₆ : 0ℚ < 1/2 * ε
--         l₆ = halving-preserves-order' ε l
--         l₇ : 0ℚ < 1/2 * ε + 1/4 * ε
--         l₇ = ℚ<-adding-zero (1/2 * ε) (1/4 * ε) l₆ l₅
--         IV : (n : ℕ) → M (1/4 * ε , l₅) < n → B-ℝ y (S n) ε l
--         IV n l₃ = B-ℝ-ε-transport y (S n) (1/2 * ε + 1/4 * ε + 1/4 * ε) ε vi (transport (0ℚ <_) (vi ⁻¹) l) l v
--          where
--            i : B-ℝ (S (M (1/4 * ε , l₅))) (S n) (1/4 * ε) l₅
--            i = f (1/4 * ε) l₅ (M (1/4 * ε , l₅)) n (≤-refl (M (1/4 * ε , l₅))) (<-coarser-than-≤ (M (1/4 * ε , l₅)) n l₃)
--            ii : B-ℝ (S (M (1/2 * (1/2 * ε) , halving-preserves-order' (1/2 * ε) l₆))) y (1/2 * ε + 1/4 * ε) (ℚ<-adding-zero (1/2 * ε) (1/4 * ε) l₆ l₅)
--            ii = g (1/2 * ε , l₆) (1/4 * ε , l₅)
--            iii : B-ℝ (S (M (1/4 * ε , l₅))) y (1/2 * ε + 1/4 * ε) (ℚ<-adding-zero (1/2 * ε) (1/4 * ε) l₆ l₅)
--            iii = transport (λ z → B-ℝ z y (1/2 * ε + 1/4 * ε) (ℚ<-adding-zero (1/2 * ε) (1/4 * ε) l₆ l₅)) α ii
--             where
--              α : S (M (1/2 * (1/2 * ε) , halving-preserves-order' (1/2 * ε) l₆)) ＝ S (M (1/4 * ε , l₅))
--              α = ap (λ z → S (M z)) (to-subtype-＝ (ℚ<-is-prop 0ℚ) (ℚ*-assoc 1/2 1/2 ε ⁻¹ ∙ ap (_* ε) half-of-quarter))
--            iv : B-ℝ y (S (M (1/4 * ε , l₅))) (1/2 * ε + 1/4 * ε) l₇
--            iv = ℝ-m2 (S (M (1/4 * ε , l₅))) y (1/2 * ε + 1/4 * ε) l₇ iii
--            v : B-ℝ y (S n) (1/2 * ε + 1/4 * ε + 1/4 * ε) (ℚ<-adding-zero (1/2 * ε + 1/4 * ε) (1/4 * ε) l₇ l₅)
--            v = ℝ-m4 y (S (M (1/4 * ε , l₅))) (S n) (1/2 * ε + 1/4 * ε) (1/4 * ε) l₇ l₅ iv i
--            vi : 1/2 * ε + 1/4 * ε + 1/4 * ε ＝ ε
--            vi = 1/2 * ε + 1/4 * ε + 1/4 * ε ＝⟨ ap (_+ 1/4 * ε) (ℚ-distributivity' ε 1/2 1/4 ⁻¹) ⟩
--                 (1/2 + 1/4) * ε + 1/4 * ε   ＝⟨ ap (λ z → z * ε + 1/4 * ε) 1/2+1/4 ⟩
--                 3/4 * ε + 1/4 * ε           ＝⟨ ℚ-distributivity' ε 3/4 1/4 ⁻¹ ⟩
--                 (3/4 + 1/4) * ε             ＝⟨ ap (_* ε) (ℚ+-comm 3/4 1/4 ∙ 1/4+3/4) ⟩
--                 1ℚ * ε                      ＝⟨ ℚ-mult-left-id ε ⟩
--                 ε ∎

-- ℝ-complete-metric-space : complete-metric-space ℝ
-- ℝ-complete-metric-space = ℝ-metric-space , ℝ-cauchy-sequences-are-convergent

-- \end{code}

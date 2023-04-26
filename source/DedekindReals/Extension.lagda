Andrew Sneap - 19 April 2023

This file proves an extension theorem, which extends functions (f : ℚ → ℚ) to
functions (f̂ : ℝ → ℝ), given that f is uniformly continuous.

Escardo contributed the Dedekind cut definition of the extension construction,
suggested the "ball" notation and the paper proof that the "extend" function is
disjoint, as well as verbally discussing the other cut conditions of "extend".

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --lossy-unification --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Abs
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.MinMax
open import Rationals.Negation
open import UF.Base
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Subsingletons

module DedekindReals.Extension
  (fe : Fun-Ext)
  (pe : Prop-Ext)
  (pt : propositional-truncations-exist)
 where

open PropositionalTruncation pt

open import DedekindReals.Properties fe pt pe
open import DedekindReals.Type pe pt fe
open import MetricSpaces.DedekindReals pt fe pe
open import MetricSpaces.Rationals fe pt pe

\end{code}

Introduce some useful notation

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

_∈⦅_⦆ : ℚ → ℚ × ℚ → 𝓤₀ ̇
x₀ ∈⦅ a , b ⦆ = a < x₀ < b

_∈⟦_⟧ : ℚ → ℚ × ℚ → 𝓤₀ ̇
x₀ ∈⟦ a , b ⟧ = a ≤ x₀ ≤ b

_ℝ∈⦅_⦆ : ℝ → ℚ × ℚ → 𝓤₀ ̇
x ℝ∈⦅ a , b ⦆ = a < x < b

_∈𝐁_⦅_⦆ : ℚ → ℚ₊ → ℚ → 𝓤₀ ̇
x ∈𝐁 (δ , _) ⦅ x₀ ⦆ = x ∈⦅ x₀ - δ , x₀ + δ ⦆

_∈𝐁_⟦_⟧ : ℚ → ℚ₊ → ℚ → 𝓤₀ ̇
x ∈𝐁 (δ , _) ⟦ x₀ ⟧ = x ∈⟦ x₀ - δ , x₀ + δ ⟧

_ℝ∈𝐁_⦅_⦆ : ℝ → ℚ₊ → ℚ → 𝓤₀ ̇
x ℝ∈𝐁 (δ , _) ⦅ x₀ ⦆ = x ℝ∈⦅ x₀ - δ , x₀ + δ ⦆

\end{code}

Define various forms of continuity

\begin{code}

{-
is-continuous : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
              → (m₁ : metric-space M₁)
              → (m₂ : metric-space M₂)
              → (f : M₁ → M₂)
              → 𝓤 ̇
is-continuous {𝓤} {𝓥} {M₁} {M₂} m₁ m₂ f
 = (x x₀ : M₁) → (ε₊ : ℚ₊) → {!!}

is-bishop-continuous : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
                     → (m₁ : metric-space M₁)
                     → (m₂ : metric-space M₂)
                     → (f : M₁ → M₂)
                     → 𝓤 ̇
is-bishop-continuous = {!!}
-}

ℚ-is-uniformly-continuous : (f : ℚ → ℚ) → 𝓤₀ ̇
ℚ-is-uniformly-continuous f
 = (ε : ℚ₊) → Σ δ ꞉ ℚ₊ , ((x x₀ : ℚ) → x ∈𝐁 δ ⦅ x₀ ⦆ → f x ∈𝐁 ε ⦅ f x₀ ⦆)

ℝ-is-uniformly-continuous : (f : ℝ → ℝ) → 𝓤₁ ̇
ℝ-is-uniformly-continuous f
 = ((ε , 0<ε) : ℚ₊)
 → Σ (δ , 0<δ) ꞉ ℚ₊ , ((x x₀ : ℝ) → B-ℝ x x₀ δ 0<δ → B-ℝ (f x) (f x₀) ε 0<ε)

δ⦅⦆ : (f : ℚ → ℚ) → (ℚ-is-uniformly-continuous f) → ℚ₊ → ℚ₊
δ⦅⦆ f ic ε = pr₁ (ic ε)

δ-uc : (f : ℚ → ℚ)
     → (ic : ℚ-is-uniformly-continuous f)
     → (ε : ℚ₊)
     → (x x₀ : ℚ)
     → x ∈𝐁 δ⦅⦆ f ic ε ⦅ x₀ ⦆
     → f x ∈𝐁 ε ⦅ f x₀ ⦆
δ-uc f ic ε = pr₂ (ic ε)

δ'⦅⦆ : (f : ℝ → ℝ) → (ℝ-is-uniformly-continuous f) → ℚ₊ → ℚ₊
δ'⦅⦆ f ic ε = pr₁ (ic ε)

δ'-uc : (f : ℝ → ℝ)
      → (ic : ℝ-is-uniformly-continuous f)
      → ((ε , 0<ε) : ℚ₊)
      → (x x₀ : ℝ)
      → let (δ , 0<δ) = δ'⦅⦆ f ic (ε , 0<ε) in B-ℝ x x₀ δ 0<δ
      → B-ℝ (f x) (f x₀) ε 0<ε
δ'-uc f ic ε = pr₂ (ic ε)

find-rational-con : (x₀ x₀' : ℚ) ((δ , 0<δ) (δ' , 0<δ') : ℚ₊)
             → (x : ℝ)
             → x ℝ∈𝐁 (δ , 0<δ) ⦅ x₀ ⦆
             → x ℝ∈𝐁 (δ' , 0<δ') ⦅ x₀' ⦆
             → Σ x' ꞉ ℚ , max (x₀ - δ) (x₀' - δ') < x' < min (x₀ + δ) (x₀' + δ')
find-rational-con x₀ x₀' (δ , _) (δ' , _) x (l₁ , l₂) (l₃ , l₄)
 = γ (decide-max (x₀ - δ) (x₀' - δ')) (decide-min (x₀ + δ) (x₀' + δ'))
  where
   I : (a b c d : ℚ)
     → a < x < b
     → c ＝ a
     → d ＝ b
     → c < d
   I a b c d (l₁ , l₂) e₁ e₂
    = transport₂ _<_ (e₁ ⁻¹) (e₂ ⁻¹) (disjoint-from-real x a b (l₁ , l₂))

   γ : (max (x₀ - δ) (x₀' - δ') ＝ x₀' - δ')
     ∔ (max (x₀ - δ) (x₀' - δ') ＝ x₀ - δ)
     → (min (x₀ + δ) (x₀' + δ') ＝ x₀ + δ)
     ∔ (min (x₀ + δ) (x₀' + δ') ＝ x₀' + δ')
     → Σ x' ꞉ ℚ , max (x₀ - δ) (x₀' - δ') < x' < min (x₀ + δ) (x₀' + δ')
   γ (inl α) (inl β) = ℚ-dense _ _ (I _ _ _ _ (l₃ , l₂) α β)
   γ (inl α) (inr β) = ℚ-dense _ _ (I _ _ _ _ (l₃ , l₄) α β)
   γ (inr α) (inl β) = ℚ-dense _ _ (I _ _ _ _ (l₁ , l₂) α β)
   γ (inr α) (inr β) = ℚ-dense _ _ (I _ _ _ _ (l₁ , l₄) α β)

restrict-balls₁ : (x₀ x₀' x' : ℚ) ((δ₁ , 0<δ₁) (δ₂ , 0<δ₂) : ℚ₊)
                → (max (x₀ - δ₁) (x₀' - δ₂) < x' < min (x₀ + δ₁) (x₀' + δ₂))
                → x' ∈𝐁 δ₁ , 0<δ₁ ⦅ x₀ ⦆
restrict-balls₁ x₀ x₀' x' (δ₁ , 0<δ₁) (δ₂ , 0<δ₂) (l₁ , l₂) = γ₁ , γ₂
 where
  γ₁ : x₀ - δ₁ < x'
  γ₁ = ℚ≤-<-trans (x₀ - δ₁) (max (x₀ - δ₁) (x₀' - δ₂)) x' (max≤ (x₀ - δ₁) _) l₁

  γ₂ : x' < x₀ + δ₁
  γ₂ = ℚ<-≤-trans x' (min (x₀ + δ₁) (x₀' + δ₂)) (x₀ + δ₁) l₂ (min≤ (x₀ + δ₁) _)

restrict-balls₂ : (x₀ x₀' x' : ℚ) ((δ₁ , 0<δ₁) (δ₂ , 0<δ₂) : ℚ₊)
                → (max (x₀ - δ₁) (x₀' - δ₂) < x' < min (x₀ + δ₁) (x₀' + δ₂))
                → x' ∈𝐁 δ₂ , 0<δ₂ ⦅ x₀' ⦆
restrict-balls₂ x₀ x₀' x' (δ₁ , 0<δ₁) (δ₂ , 0<δ₂) (l₁ , l₂)
 = restrict-balls₁ x₀' x₀ x' (δ₂ , 0<δ₂) (δ₁ , 0<δ₁) (γ₁ , γ₂)
  where
   γ₁ : max (x₀' - δ₂) (x₀ - δ₁) < x'
   γ₁ = transport (_< x') (max-comm (x₀ - δ₁) (x₀' - δ₂)) l₁

   γ₂ : x' < min (x₀' + δ₂) (x₀ + δ₁)
   γ₂ = transport (x' <_) (min-comm (x₀ + δ₁) (x₀' + δ₂)) l₂

\end{code}

The extension relies on being able to find a rational δ-close to arbitrary close
to arbitrary reals. This is a simple corollary of arithmetic locatedness. Hence,
for any given uniformly continuous function (f : ℚ → ℚ), and a given ε and
(x : ℝ), we can find (x₀ : ℚ) δ-close to x, meaning f x is ε-close to f x₀.

This property is used multiple times when defining the extension.

\begin{code}

ball-around-real : (x : ℝ)
                 → (ε : ℚ₊)
                 → (f : ℚ → ℚ)
                 → (ic : ℚ-is-uniformly-continuous f)
                 → ∃ x₀ ꞉ ℚ , x ℝ∈𝐁 δ⦅⦆ f ic ε ⦅ x₀ ⦆
ball-around-real x ε f ic = ∥∥-functor γ (ℝ-arithmetically-located x δ 0<δ)
 where
  δ₊ : ℚ₊
  δ₊ = δ⦅⦆ f ic ε

  δ : ℚ
  δ = pr₁ δ₊

  0<δ : 0ℚ < δ
  0<δ =  pr₂ δ₊

  γ : Σ (u , v) ꞉ ℚ × ℚ , (u < x) × (x < v) × (0ℚ < v - u) × (v - u < δ)
    → Σ x₀ ꞉ ℚ , x ℝ∈𝐁 δ₊ ⦅ x₀ ⦆
  γ ((u , v) , l₁ , l₂ , l₃ , l₄) = u , (γ₁ , γ₂)
   where
    I : u - δ < u
    I = ℚ<-subtraction-preserves-order u δ 0<δ

    II : v < u + δ
    II = ℚ<-subtraction-order v u δ l₄

    γ₁ : u - δ < x
    γ₁ = rounded-left-c (lower-cut-of x) (rounded-from-real-L x) (u - δ) u I l₁

    γ₂ : x < u + δ
    γ₂ = rounded-right-c (upper-cut-of x) (rounded-from-real-R x) v (u + δ) II l₂

ball-around-real' : (x : ℝ)
                  → (f : ℚ → ℚ)
                  → (ic : ℚ-is-uniformly-continuous f)
                  → ∃ (x₀ , ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic ε ⦅ x₀ ⦆
ball-around-real' x f ic = ∥∥-functor γ (ball-around-real x (1ℚ , 0<1) f ic)
 where
  γ : Σ x₀ ꞉ ℚ , x ℝ∈𝐁 δ⦅⦆ f ic (1ℚ , 0<1) ⦅ x₀ ⦆
    → Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
  γ (x₀ , b) = (x₀ , 1ℚ , 0<1) , b

\end{code}

With the above machinery, we can now define the extension.

\begin{code}

extend : (f : ℚ → ℚ)
       → (ic : ℚ-is-uniformly-continuous f)
       → ℝ → ℝ
extend f ic x = (L , R) , il , ir , rl , rr , d , lo
 where
  L' R' : ℚ → 𝓤₀ ̇
  L' p = ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆)
                                   × p < f x₀ - ε
  R' q = ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆)
                                   × f x₀ + ε < q

  L R : 𝓟 ℚ
  L p = L' p , ∃-is-prop
  R q = R' q , ∃-is-prop

  Bx : ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
  Bx = ball-around-real' x f ic

  il : inhabited-left L
  il = ∥∥-functor γ Bx
   where
    γ : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
      → Σ p ꞉ ℚ , p ∈ L
    γ ((x₀ , ε , 0<ε) , h) = let (p , l) = ℚ-no-least-element (f x₀ - ε)
                             in p , ∣ (x₀ , ε , 0<ε) , h , l ∣

  ir : inhabited-right R
  ir = ∥∥-functor γ Bx
   where
    γ : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
      → Σ p ꞉ ℚ , p ∈ R
    γ ((x₀ , ε , 0<ε) , h) = let (p , l) = ℚ-no-max-element (f x₀ + ε)
                             in p , ∣ (x₀ , ε , 0<ε) , h , l ∣

  rl : rounded-left L
  rl p = γ₁ , γ₂
   where
    γ₁ : ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                   × p < f x₀ - ε
       → ∃ q ꞉ ℚ , p < q × q ∈ L
    γ₁ = ∥∥-functor γ
     where
      γ : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                    × p < f x₀ - ε
        → Σ q ꞉ ℚ , p < q × q ∈ L
      γ ((x₀ , ε , 0<ε) , h , l)
       = let (q , l₁ , l₂) = ℚ-rounded-left₁ (f x₀ - ε) p l
         in q , l₁ , ∣ (x₀ , ε , 0<ε) , h , l₂ ∣

    γ₂ : ∃ q ꞉ ℚ , p < q × q ∈ L
       → ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                   × p < f x₀ - ε
    γ₂ = ∥∥-rec ∃-is-prop γ
     where
      γ : Σ q ꞉ ℚ , p < q × q ∈ L
        → ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                    × p < f x₀ - ε
      γ (q , l , ex) = ∥∥-functor γ' ex
       where
        γ' : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                       × q < f x₀ - ε
           → Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                       × p < f x₀ - ε
        γ' ((x₀ , ε , 0<ε) , h , l') = (x₀ , ε , 0<ε) , h , I
         where
          I : p < f x₀ - ε
          I = ℚ<-trans p q (f x₀ - ε) l l'

  rr : rounded-right R
  rr q = γ₁ , γ₂
   where
    γ₁ : ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                   × f x₀ + ε < q
       → ∃ p ꞉ ℚ , p < q × p ∈ R
    γ₁ = ∥∥-functor γ
     where
      γ : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                    × f x₀ + ε < q
        → Σ p ꞉ ℚ , p < q × p ∈ R
      γ ((x₀ , ε , 0<ε) , h , l)
       = let (p , l₁ , l₂) = ℚ-rounded-right₁ (f x₀ + ε) q l
         in p , l₁ , ∣ (x₀ , ε , 0<ε) , h , l₂ ∣

    γ₂ : ∃ p ꞉ ℚ , p < q × p ∈ R
       → ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                   × f x₀ + ε < q
    γ₂ = ∥∥-rec ∃-is-prop γ
     where
      γ : Σ p ꞉ ℚ , p < q × p ∈ R
        → ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                    × f x₀ + ε < q
      γ (p , l , ex) = ∥∥-functor γ' ex
       where
        γ' : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                       × f x₀ + ε < p
           → Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                       × f x₀ + ε < q
        γ' ((x₀ , ε , 0<ε) , h , l') = (x₀ , ε , 0<ε) , h , I
         where
          I : f x₀ + ε < q
          I = ℚ<-trans (f x₀ + ε) p q l' l

  d : disjoint L R
  d p q (l₁ , l₂) = ∥∥-rec (ℚ<-is-prop p q) γ (binary-choice l₁ l₂)
   where
    γ : (Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                   × p < f x₀ - ε)
      × (Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                   × f x₀ + ε < q)
      → p < q
    γ (((x₀ , ε , 0<ε) , h , l) , ((x₀' , ε' , 0<ε') , h' , l'))
     = γ' (find-rational-con x₀ x₀' δ₁₊ δ₂₊ x h h')
     where
      δ₁₊ δ₂₊ : ℚ₊
      δ₁₊ = δ⦅⦆ f ic (ε , 0<ε)
      δ₂₊ = δ⦅⦆ f ic (ε' , 0<ε')

      δ₁ δ₂ : ℚ
      δ₁ = pr₁ δ₁₊
      δ₂ = pr₁ δ₂₊

      γ' : Σ x' ꞉ ℚ ,
            (let (δ₁ , _) = δ⦅⦆ f ic (ε , 0<ε)
                 (δ₂ , _) = δ⦅⦆ f ic (ε' , 0<ε')
             in max (x₀ - δ₁) (x₀' - δ₂) < x' < min (x₀ + δ₁) (x₀' + δ₂))
         → p < q
      γ' (x' , l₃ , l₄) = ℚ<-trans p (f x') q V VI
       where
        I : x' ∈𝐁 δ₁₊ ⦅ x₀ ⦆
        I = restrict-balls₁ x₀ x₀' x' δ₁₊ δ₂₊ (l₃ , l₄)

        II : x' ∈𝐁 δ₂₊ ⦅ x₀' ⦆
        II = restrict-balls₂ x₀ x₀' x' δ₁₊ δ₂₊ (l₃ , l₄)

        III : f x' ∈𝐁 ε , 0<ε ⦅ f x₀ ⦆
        III = δ-uc f ic (ε , 0<ε) x' x₀ I

        IV : f x' ∈𝐁 ε' , 0<ε' ⦅ f x₀' ⦆
        IV = δ-uc f ic (ε' , 0<ε') x' x₀' II

        V : p < f x'
        V = ℚ<-trans p (f x₀ - ε) (f x') l (pr₁ III)

        VI : f x' < q
        VI = ℚ<-trans (f x') (f x₀' + ε') q (pr₂ IV) l'

  lo : located L R
  lo p q l = ∥∥-functor γ (ball-around-real x (ε , 0<ε) f ic)
   where
    ε : ℚ
    ε = 1/4 * (q - p)

    l₁ : 0ℚ < q - p
    l₁ = ℚ<-difference-positive p q l

    0<ε : 0ℚ < ε
    0<ε = ℚ<-pos-multiplication-preserves-order 1/4 (q - p) 0<1/4 l₁

    γ : Σ x₀ ꞉ ℚ , x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
      → (p ∈ L) ∔ (q ∈ R)
    γ  (x₀ , b) = γ' (order-lemma' p q (f x₀) l)
     where
      γ' : (p < f x₀ - ε) ∔ (f x₀ + ε < q)
         → p ∈ L ∔ q ∈ R
      γ' (inl l₄) = inl ∣ (x₀ , ε , 0<ε) , b , l₄ ∣
      γ' (inr l₄) = inr ∣ (x₀ , ε , 0<ε) , b , l₄ ∣

\end{code}

We now prove that the extend construction is indeed an extension. This means
that for any rational input, the extension output agrees with the function
output.

TODO : And is uniformly continuous and unique

\begin{code}

extend-is-extension : (q : ℚ)
                    → (f : ℚ → ℚ)
                    → (ic : ℚ-is-uniformly-continuous f)
                    → (extend f ic) (ι q) ＝ ι (f q)
extend-is-extension q f ic = γ
 where
  L  = lower-cut-of ((extend f ic) (ι q))

  γ₁ : (p : ℚ) → p ∈ L → p < f q
  γ₁ p = ∥∥-rec (ℚ<-is-prop p (f q)) I
   where
    I : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , ι q ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                  × p < f x₀ - ε
      → p < f q
    I ((x₀ , ε , 0<ε) , b , l) = ℚ<-trans p (f x₀ - ε) (f q) l (pr₁ II)
     where
      II : f q ∈𝐁 ε , 0<ε ⦅ f x₀ ⦆
      II = δ-uc f ic (ε , 0<ε) q x₀ b

  γ₂ : (p : ℚ)
     → p < f q
     → ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , ι q ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                 × p < f x₀ - ε
  γ₂ p l = ∥∥-functor γ (ball-around-real (ι q) (ε , 0<ε) f ic)
   where
    ε : ℚ
    ε = 1/2 * (f q - p)

    I : 0ℚ < f q - p
    I = ℚ<-difference-positive p (f q) l

    0<ε : 0ℚ < ε
    0<ε = ℚ<-pos-multiplication-preserves-order 1/2 (f q - p) 0<1/2 I

    δ₊ : ℚ₊
    δ₊ = δ⦅⦆ f ic (ε , 0<ε)

    γ : Σ x₀ ꞉ ℚ , (ι q ℝ∈𝐁 δ₊ ⦅ x₀ ⦆)
      → Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , ι q ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⦅ x₀ ⦆
                                  × p < f x₀ - ε
    γ (x₀ , b) = (x₀ , ε , 0<ε) , (b , γ')
     where
      II : f q < f x₀ + ε
      II = pr₂ (δ-uc f ic (ε , 0<ε) q x₀ b)

      IV : f q + (p - f q) < f x₀ + ε + (p - f q)
      IV = ℚ<-addition-preserves-order
            (f q) (f x₀ + ε) (p - f q) II

      V : f q + (p - f q) ＝ p
      V = f q + (p - f q) ＝⟨ ℚ+-comm (f q) (p - f q)        ⟩
          p - f q + f q   ＝⟨ ℚ-inverse-intro'''' p (f q) ⁻¹ ⟩
          p               ∎

      VI : f q - p ＝ - (p - f q)
      VI = f q - p         ＝⟨ ℚ+-comm (f q) (- p)                 ⟩
           (- p) + f q     ＝⟨ ap ((- p) +_) (ℚ-minus-minus (f q)) ⟩
           (- p) - (- f q) ＝⟨ ℚ-minus-dist p (- f q)              ⟩
           - (p - f q)     ∎

      VII : ε + (p - f q) ＝ - ε
      VII = ε + (p - f q)                        ＝⟨ i    ⟩
            1/2 * (- (p - f q)) + (p - f q)      ＝⟨ ii   ⟩
            (- 1/2) * (p - f q) + (p - f q)      ＝⟨ iii  ⟩
            (- 1/2) * (p - f q) + 1ℚ * (p - f q) ＝⟨ iv   ⟩
            ((- 1/2) + 1ℚ) * (p - f q)           ＝⟨ v    ⟩
            (1ℚ - 1/2) * (p - f q)               ＝⟨ vi   ⟩
            1/2 * (p - f q)                      ＝⟨ vii  ⟩
            - (- 1/2 * (p - f q))                ＝⟨ viii ⟩
            - 1/2 * (- (p - f q))                ＝⟨ ix   ⟩
            - ε                    ∎
       where
        i    = ap (λ z → 1/2 * z + (p - f q)) VI
        ii   = ap (_+ (p - f q)) (ℚ-negation-dist-over-mult'' 1/2 (p - f q))
        iii  = ap ((- 1/2) * (p - f q) +_) (ℚ-mult-left-id (p - f q) ⁻¹)
        iv   = ℚ-distributivity' (p - f q) (- 1/2) 1ℚ ⁻¹
        v    = ap (_* (p - f q)) (ℚ+-comm (- 1/2) 1ℚ)
        vi   = ap (_* (p - f q)) 1-1/2
        vii  = ℚ-minus-minus (1/2 * (p - f q))
        viii = ap -_  (ℚ-negation-dist-over-mult' 1/2 (p - f q) ⁻¹)
        ix   = ap (λ z → - 1/2 * z) (VI ⁻¹)

      VIII : f x₀ + ε + (p - f q) ＝ f x₀ - ε
      VIII = f x₀ + ε + (p - f q)   ＝⟨ ℚ+-assoc (f x₀) ε (p - f q) ⟩
             f x₀ + (ε + (p - f q)) ＝⟨ ap (f x₀ +_) VII            ⟩
             f x₀ - ε               ∎

      γ' : p <ℚ f x₀ - ε
      γ' = transport₂ _<_ V VIII IV

  γ : (extend f ic) (ι q) ＝ ι (f q)
  γ = ℝ-equality-from-left-cut' ((extend f ic) (ι q)) (ι (f q)) γ₁ γ₂

\end{code}

To illustrate the use of the extension theorem, the following example is
provided which lifts the increment function on rationals to a function on reals.

The function which adds one is clearly uniformly continuous (and this is proved
below). Hence we simply apply the extension thereom and we are done.

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
ℝ-incr-agrees-with-ℚ-incr q = extend-is-extension q ℚ-incr ℚ-incr-uc

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

ℝ-_ : ℝ → ℝ
ℝ-_ = extend -_ ℚ-neg-is-uc

open import Rationals.Abs

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

ℚ⁴ = ℚ × ℚ × ℚ × ℚ

midpoint-switch : (p q : ℚ)
                → p + 1/2 * abs (p - q) ＝ q - 1/2 * abs (p - q)
midpoint-switch = {!!}

ball-around-close-reals : (x x₀ : ℝ)
                        → ((ε , 0<ε) : ℚ₊)
                        → B-ℝ x x₀ ε 0<ε
                        → ∃ p ꞉ ℚ , (x ℝ∈𝐁 (ε , 0<ε) ⦅ p ⦆)
                                  × (x₀ ℝ∈𝐁 (ε , 0<ε) ⦅ p ⦆)
ball-around-close-reals
 x@((Lx , Rx) , _ , _ , rlx , rrx , _ , _)
 x₀@((Lx₀ , Rx₀) , _ , _ , rlx₀ , rrx₀ , _ , _)
 (ε , 0<ε) = ∥∥-functor γ
 where
  γ : Σ (a , b , c , d) ꞉ ℚ⁴ , (a < x)
                             × (c < x₀)
                             × (x < b)
                             × (x₀ < d)
                             × B-ℚ (min a c) (max b d) ε 0<ε
    → Σ p ꞉ ℚ , (x ℝ∈𝐁 ε , 0<ε ⦅ p ⦆) × (x₀ ℝ∈𝐁 ε , 0<ε ⦅ p ⦆)
  γ ((a , b , c , d) , l₁ , l₂ , l₃ , l₄ , m)
   = m₁ + k , (γ₁ , γ₂) , (γ₃ , γ₄)
   where
    m₁ = min a c
    m₂ = max b d

    k = 1/2 * abs (m₁ - m₂)

    l₅ : k < 1/2 * ε
    l₅ = ℚ<-pos-multiplication-preserves-order'' (abs (m₁ - m₂)) ε 1/2 m 0<1/2

    l₆ : 0ℚ < 1/2 * ε
    l₆ = ℚ<-pos-multiplication-preserves-order 1/2 ε 0<1/2 0<ε

    l₇ : k < ε
    l₇ = ℚ<-trans k (1/2 * ε) ε l₅ (half-of-pos-is-less ε 0<ε)

    l₈ : 0ℚ < ε - k
    l₈ = ℚ<-difference-positive k ε l₇

    I : m₁ + k < m₁ + 1/2 * ε
    I = ℚ<-addition-preserves-order''' k (1/2 * ε) m₁ l₅

    II : m₁ + k - ε < m₁ + 1/2 * ε - ε
    II = ℚ<-addition-preserves-order (m₁ + k) (m₁ + 1/2 * ε) (- ε) I

    III : m₁ + 1/2 * ε - ε ＝ m₁ - 1/2 * ε
    III = m₁ + 1/2 * ε - ε            ＝⟨ i   ⟩
          m₁ + (1/2 * ε - ε)          ＝⟨ ii  ⟩
          m₁ + (1/2 * ε - 1ℚ * ε)     ＝⟨ iii ⟩
          m₁ + (1/2 * ε + (- 1ℚ) * ε) ＝⟨ iv  ⟩
          m₁ + (1/2 - 1ℚ) * ε         ＝⟨ v   ⟩
          m₁ - 1/2 * ε                ∎
     where
      i   = ℚ+-assoc m₁ (1/2 * ε) (- ε)
      ii  = ap (λ z → m₁ + (1/2 * ε - z)) (ℚ-mult-left-id ε ⁻¹)
      iii = ap (λ z → m₁ + ((1/2 * ε) + z)) (ℚ-negation-dist-over-mult 1ℚ ε ⁻¹)
      iv  = ap (m₁ +_) (ℚ-distributivity' ε 1/2 (- 1ℚ) ⁻¹)
      v   = ap (m₁ +_) (ℚ-negation-dist-over-mult 1/2 ε)

    IV : m₁ + k - ε < m₁ - 1/2 * ε
    IV = transport (m₁ + k - ε <_) III II

    V : m₁ - 1/2 * ε < m₁
    V = ℚ<-subtraction-preserves-order m₁ (1/2 * ε) l₆

    VI : m₁ + k - ε < m₁
    VI = ℚ<-trans (m₁ + k - ε) (m₁ - 1/2 * ε) m₁ IV V

    VII : m₂ + (ε - k) ＝ m₁ + k + ε
    VII = m₂ + (ε - k)     ＝⟨ ap (m₂ +_) (ℚ+-comm ε (- k)) ⟩
          m₂ + ((- k) + ε) ＝⟨ ℚ+-assoc m₂ (- k) ε ⁻¹ ⟩
          m₂ - k + ε       ＝⟨ ap (_+ ε) (midpoint-switch m₁ m₂ ⁻¹) ⟩
          m₁ + k + ε       ∎

    VIII : m₂ < m₂ + (ε - k)
    VIII = ℚ<-addition-preserves-order'' m₂ (ε - k) l₈

    IX : m₂ <ℚ (m₁ + k + ε)
    IX = transport (m₂ <_) VII VIII

    γ₁ : m₁ + k - ε < x
    γ₁ = rounded-left-c Lx rlx (m₁ + k - ε) a γ' l₁
     where
      γ' : m₁ + k - ε < a
      γ' = ℚ<-≤-trans (m₁ + k - ε) m₁ a VI (min≤ a c)

    γ₂ : x < m₁ + k + ε
    γ₂ = rounded-right-c Rx rrx b (m₁ + k + ε) γ' l₃
     where
      γ' : b < m₁ + k + ε
      γ' = ℚ≤-<-trans b m₂ (m₁ + k + ε) (max≤ b d) IX

    γ₃ : m₁ + k - ε < x₀
    γ₃ = rounded-left-c Lx₀ rlx₀ (m₁ + k - ε) c γ' l₂
     where
      γ' : m₁ + k - ε < c
      γ' = ℚ<-≤-trans (m₁ + k - ε) m₁ c VI (min≤' a c)

    γ₄ : x₀ < m₁ + k + ε
    γ₄ = rounded-right-c Rx₀ rrx₀ d (m₁ + k + ε) γ' l₄
     where
      γ' : d < m₁ + k + ε
      γ' = ℚ≤-<-trans d m₂ (m₁ + k + ε) (max≤' b d) IX

expand-interval-within-bound : (p : ℚ)
                             → ((ε , 0<ε) : ℚ₊)
                             → Σ (a , b) ꞉ ℚ × ℚ , (a < p - 1/4 * ε)
                                                 × (p + 1/4 * ε < b)
                                                 × B-ℚ a b ε 0<ε
expand-interval-within-bound = {!!}

extensions-uc : (f : ℚ → ℚ)
              → (ic : ℚ-is-uniformly-continuous f)
              → ℝ-is-uniformly-continuous (extend f ic)
extensions-uc f ic (ε , 0<ε) = δ₊ , γ
 where
  ε' : ℚ
  ε' = 1/4 * ε

  0<ε' : 0ℚ < ε'
  0<ε' = ℚ<-pos-multiplication-preserves-order 1/4 ε 0<1/4 0<ε

  δ₊ : ℚ₊
  δ₊ = δ⦅⦆ f ic (ε' , 0<ε')
  δ = pr₁ δ₊
  0<δ = pr₂ δ₊

  γ : (x x₀ : ℝ)
    → B-ℝ x x₀ δ 0<δ
    → B-ℝ (extend f ic x) (extend f ic x₀) ε 0<ε
  γ x x₀ b = ∥∥-functor γ' (ball-around-close-reals x x₀ (δ , 0<δ) b)
   where
    f̂x = extend f ic x
    f̂x₀ = extend f ic x₀

    γ' : Σ p ꞉ ℚ , (x ℝ∈𝐁 δ , 0<δ ⦅ p ⦆) × (x₀ ℝ∈𝐁 δ , 0<δ ⦅ p ⦆)
       → Σ (a , b , c , d) ꞉ ℚ⁴ , (a < f̂x)
                                × (c < f̂x₀)
                                × (f̂x < b)
                                × (f̂x₀ < d)
                                × B-ℚ (min a c) (max b d) ε 0<ε
    γ' (p , B₁ , B₂) = γ'' I
     where
      I : Σ (a , b) ꞉ ℚ × ℚ , (a < f p - 1/4 * ε)
                            × (f p + 1/4 * ε < b)
                            × B-ℚ a b ε 0<ε
      I = expand-interval-within-bound (f p) (ε , 0<ε)

      γ'' : Σ (a , b) ꞉ ℚ × ℚ , (a < f p - 1/4 * ε)
                               × (f p + 1/4 * ε < b)
                               × B-ℚ a b ε 0<ε
          → Σ (a , b , c , d) ꞉ ℚ⁴ , (a < f̂x)
                                × (c < f̂x₀)
                                × (f̂x < b)
                                × (f̂x₀ < d)
                                × B-ℚ (min a c) (max b d) ε 0<ε
      γ'' ((a , b) , l₅ , l₆ , m)
       = (a , b , a , b) , a<f̂x , b<f̂x₀ , f̂x<b , f̂x₀<b , γ'''
       where
        a<f̂x : a < f̂x
        a<f̂x = ∣ (p , ε' , 0<ε') , B₁ , l₅ ∣

        b<f̂x₀ : a < f̂x₀
        b<f̂x₀ = ∣ (p , ε' , 0<ε') , B₂ , l₅ ∣

        f̂x<b : f̂x < b
        f̂x<b = ∣ (p , ε' , 0<ε') , B₁ , l₆ ∣

        f̂x₀<b : f̂x₀ < b
        f̂x₀<b = ∣ (p , ε' , 0<ε') , B₂ , l₆ ∣

        II : a ＝ min a a
        II = min-refl a ⁻¹

        III : b ＝ max b b
        III = max-refl b ⁻¹

        IV : B-ℚ a b ε 0<ε
        IV = m

        γ''' : B-ℚ (min a a) (max b b) ε 0<ε
        γ''' = transport₂ (λ α β → B-ℚ α β ε 0<ε) II III IV

\end{code}

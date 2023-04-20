Andrew Sneap - 19 April 2023

This file proves an extension theorem, which takes lifts functions (f : ℚ → ℚ)
to functions (f̂ : ℝ → ℝ), given that f is uniformly continuous.

Escardo contributed the Dedekind cut definition of the extension construction,
suggested the "ball" notation and the paper proof that the "extend" function is
disjoint, as well as verbally discussing the other cut conditions of "extend".

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --lossy-unification --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.CanonicalMap
open import Notation.Order
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

ℚ₊ : 𝓤₀ ̇
ℚ₊ = Σ q ꞉ ℚ , 0ℚ < q

_∈𝐁_⦅_⦆ : ℚ → ℚ₊ → ℚ → 𝓤₀ ̇
x ∈𝐁 (δ , _) ⦅ x₀ ⦆ = x ∈⦅ x₀ - δ , x₀ + δ ⦆

_∈𝐁_⟦_⟧ : ℚ → ℚ₊ → ℚ → 𝓤₀ ̇
x ∈𝐁 (δ , _) ⟦ x₀ ⟧ = x ∈⟦ x₀ - δ , x₀ + δ ⟧

_ℝ∈𝐁_⦅_⦆ : ℝ → ℚ₊ → ℚ → 𝓤₀ ̇
x ℝ∈𝐁 (δ , _) ⦅ x₀ ⦆ = x ℝ∈⦅ x₀ - δ , x₀ + δ ⦆

\end{code}

Modulus of uniform continuity

\begin{code}

ℚ-is-uniformly-continuous : (f : ℚ → ℚ)
                          → 𝓤₀ ̇
ℚ-is-uniformly-continuous f
 = (ε : ℚ₊) → Σ δ ꞉ ℚ₊ , ((x x₀ : ℚ) → x ∈𝐁 δ ⦅ x₀ ⦆ → f x ∈𝐁 ε ⦅ f x₀ ⦆)

δ⦅⦆ : (f : ℚ → ℚ) → (ℚ-is-uniformly-continuous f) → ℚ₊ → ℚ₊
δ⦅⦆ f ic ε = pr₁ (ic ε)

\end{code}

Statement of theorem : ?

\begin{code}


\end{code}

Prove some nice lemmas

\begin{code}

ℚ-rounded-left₁ : (y : ℚ) (x : ℚ) → x < y → Σ p ꞉ ℚ , x < p < y
ℚ-rounded-left₁ y x l = ℚ-dense x y l

ℚ-rounded-left₂ : (y : ℚ) (x : ℚ) → Σ p ꞉ ℚ , x < p < y → x < y
ℚ-rounded-left₂ y x (p , l₁ , l₂) = ℚ<-trans x p y l₁ l₂

ℚ-rounded-right₁ : (y : ℚ) (x : ℚ) → y < x → Σ q ꞉ ℚ , (q < x) × (y < q)
ℚ-rounded-right₁ y x l = I (ℚ-dense y x l)
 where
  I : Σ q ꞉ ℚ , y < q < x
    → Σ q ꞉ ℚ , (q < x) × (y < q)
  I (q , l₁ , l₂) = q , l₂ , l₁

ℚ-rounded-right₂ : (y : ℚ) (x : ℚ) → Σ q ꞉ ℚ , (q < x) × (y < q) → y < x
ℚ-rounded-right₂ y x (q , l₁ , l₂) = ℚ<-trans y q x l₂ l₁

\end{code}

Prove the theorem

\begin{code}

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
        III = pr₂ (ic (ε , 0<ε)) x' x₀ I

        IV : f x' ∈𝐁 ε' , 0<ε' ⦅ f x₀' ⦆
        IV = pr₂ (ic (ε' , 0<ε')) x' x₀' II

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

We now prove that the extend construction is indeed an extension.

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
      II = pr₂ (ic (ε , 0<ε)) q x₀ b

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
      II = pr₂ (pr₂ (ic (ε , 0<ε)) q x₀ b)

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

\end{code}

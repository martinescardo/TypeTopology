Andrew Sneap

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --lossy-unification --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition
open import Rationals.Negation
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Subsingletons

module MetricSpaces.Extension2
  (fe : Fun-Ext)
  (pe : Prop-Ext)
  (pt : propositional-truncations-exist)
 where

open PropositionalTruncation pt

open import DedekindReals.Type pe pt fe
open import MetricSpaces.Definition pt fe pe
open import MetricSpaces.Rationals fe pt pe

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

_∈𝐁_⦅_⦆ : ℚ → ℚ₊ → ℚ → 𝓤₀ ̇
x ∈𝐁 (δ , _) ⦅ x₀ ⦆ = x ∈⦅ x₀ - δ , x₀ + δ ⦆

_∈𝐁_⟦_⟧ : ℚ → ℚ₊ → ℚ → 𝓤₀ ̇
x ∈𝐁 (δ , _) ⟦ x₀ ⟧ = x ∈⟦ x₀ - δ , x₀ + δ ⟧

_ℝ∈𝐁_⟦_⟧ : ℝ → ℚ₊ → ℚ → 𝓤₀ ̇
x ℝ∈𝐁 (δ , _) ⟦ x₀ ⟧ = x ℝ∈⦅ (x₀ - δ , x₀ + δ) ⦆

\end{code}

Modulus of uniform continuity

\begin{code}

ℚ-is-uniformly-continuous : (f : ℚ → ℚ)
                          → 𝓤₀ ̇
ℚ-is-uniformly-continuous f
 = (ε : ℚ₊) → Σ δ ꞉ ℚ₊ , ((x x₀ : ℚ) → x ∈𝐁 δ ⟦ x₀ ⟧ → f x ∈𝐁 ε ⟦ f x₀ ⟧)

δ⦅⦆ : (f : ℚ → ℚ) → (ℚ-is-uniformly-continuous f) → ℚ₊ → ℚ₊
δ⦅⦆ f ic ε = pr₁ (ic ε)

\end{code}

Statement of theorem : ?

\begin{code}

extension-theorem : 𝓤₁ ̇
extension-theorem = (f : ℚ → ℚ)
                  → (ic : ℚ-is-uniformly-continuous f)
                  → ℝ → ℝ

\end{code}

Prove some nice lemmas

\begin{code}

ℚ-rounded-left₁ : (y : ℚ) (x : ℚ) → x < y → Σ p ꞉ ℚ , x < p < y
ℚ-rounded-left₁ y x l = ℚ-dense x y l

ℚ-rounded-left₂ : (y : ℚ) (x : ℚ) → Σ p ꞉ ℚ , (x < p) × p < y → x < y
ℚ-rounded-left₂ y x (p , l₁ , l₂) = ℚ<-trans x p y l₁ l₂

ℚ-rounded-right₁ : (y : ℚ) (x : ℚ) → y < x → Σ q ꞉ ℚ , (q < x) × y < q
ℚ-rounded-right₁ y x l = I (ℚ-dense y x l)
 where
  I : Σ q ꞉ ℚ , y < q < x
    → Σ q ꞉ ℚ , (q < x) × (y < q)
  I (q , l₁ , l₂) = q , l₂ , l₁

ℚ-rounded-right₂ : (y : ℚ) (x : ℚ) → Σ q ꞉ ℚ , (q < x) × y < q → y < x
ℚ-rounded-right₂ y x (q , l₁ , l₂) = ℚ<-trans y q x l₂ l₁

\end{code}

Prove the theorem

\begin{code}

f→f̂ : extension-theorem
f→f̂ f ic x = (L , R) , il , ir , rl , rr , d , lo
 where
  L' R' : ℚ → 𝓤₀ ̇
  L' p = ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                   × p < f x₀ - ε
  R' q = ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                   × f x₀ + ε < q

  L R : 𝓟 ℚ
  L p = L' p , ∃-is-prop
  R q = R' q , ∃-is-prop

  Bx : ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
  Bx = {!!}

  il : inhabited-left L
  il = ∥∥-functor γ Bx
   where
    γ : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
      → Σ p ꞉ ℚ , p ∈ L
    γ ((x₀ , ε , 0<ε) , h) = let (p , l) = ℚ-no-least-element (f x₀ - ε)
                             in p , ∣ (x₀ , ε , 0<ε) , h , l ∣

  ir : inhabited-right R
  ir = ∥∥-functor γ Bx
   where
    γ : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
      → Σ p ꞉ ℚ , p ∈ R
    γ ((x₀ , ε , 0<ε) , h) = let (p , l) = ℚ-no-max-element (f x₀ + ε)
                             in p , ∣ (x₀ , ε , 0<ε) , h , l ∣

  rl : rounded-left L
  rl p = γ₁ , γ₂
   where
    γ₁ : ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                   × p < f x₀ - ε
       → ∃ q ꞉ ℚ , p < q × q ∈ L
    γ₁ = ∥∥-functor γ
     where
      γ : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                    × p < f x₀ - ε
        → Σ q ꞉ ℚ , p < q × q ∈ L
      γ ((x₀ , ε , 0<ε) , h , l)
       = let (q , l₁ , l₂) = ℚ-rounded-left₁ (f x₀ - ε) p l
         in q , l₁ , ∣ (x₀ , ε , 0<ε) , h , l₂ ∣

    γ₂ : ∃ q ꞉ ℚ , p < q × q ∈ L
       → ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                   × p < f x₀ - ε
    γ₂ = ∥∥-rec ∃-is-prop γ
     where
      γ : Σ q ꞉ ℚ , p < q × q ∈ L
        → ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                    × p < f x₀ - ε
      γ (q , l , ex) = ∥∥-functor γ' ex
       where
        γ' : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                       × q < f x₀ - ε
           → Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                       × p < f x₀ - ε
        γ' ((x₀ , ε , 0<ε) , h , l') = (x₀ , ε , 0<ε) , h , I
         where
          I : p < f x₀ - ε
          I = ℚ<-trans p q (f x₀ - ε) l l'

  rr : rounded-right R
  rr q = γ₁ , γ₂
   where
    γ₁ : ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                   × f x₀ + ε < q
       → ∃ p ꞉ ℚ , p < q × p ∈ R
    γ₁ = ∥∥-functor γ
     where
      γ : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                    × f x₀ + ε < q
        → Σ p ꞉ ℚ , p < q × p ∈ R
      γ ((x₀ , ε , 0<ε) , h , l)
       = let (p , l₁ , l₂) = ℚ-rounded-right₁ (f x₀ + ε) q l
         in p , l₁ , ∣ (x₀ , ε , 0<ε) , h , l₂ ∣

    γ₂ : ∃ p ꞉ ℚ , p < q × p ∈ R
       → ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                   × f x₀ + ε < q
    γ₂ = ∥∥-rec ∃-is-prop γ
     where
      γ : Σ p ꞉ ℚ , p < q × p ∈ R
        → ∃ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                    × f x₀ + ε < q
      γ (p , l , ex) = ∥∥-functor γ' ex
       where
        γ' : Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                       × f x₀ + ε < p
           → Σ (x₀ , ε , 0<ε) ꞉ ℚ × ℚ₊ , (x ℝ∈𝐁 δ⦅⦆ f ic (ε , 0<ε) ⟦ x₀ ⟧)
                                       × f x₀ + ε < q
        γ' ((x₀ , ε , 0<ε) , h , l') = (x₀ , ε , 0<ε) , h , I
         where
          I : f x₀ + ε < q
          I = ℚ<-trans (f x₀ + ε) p q l' l

  d : disjoint L R
  d = {!!}

  lo : located L R
  lo = {!!}

\end{code}

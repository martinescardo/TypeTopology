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

is-continuous : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
              → (m₁ : metric-space M₁)
              → (m₂ : metric-space M₂)
              → (f : M₁ → M₂)
              → 𝓤 ̇
is-continuous {𝓤} {𝓥} {M₁} {M₂} m₁ m₂ f = {!!}

is-bishop-continuous : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
                     → (m₁ : metric-space M₁)
                     → (m₂ : metric-space M₂)
                     → (f : M₁ → M₂)
                     → 𝓤 ̇
is-bishop-continuous = {!!}

is-uniformly-continuous : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
                        → (m₁ : metric-space M₁)
                        → (m₂ : metric-space M₂)
                        → (f : M₁ → M₂)
                        → 𝓤 ̇
is-uniformly-continuous = {!!}

\end{code}

Modulus of uniform continuity

\begin{code}

_δ[_] : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
      → {m₁ : metric-space M₁}
      → {m₂ : metric-space M₂}
      → (f : M₁ → M₂)
      → {is-uniformly-continuous m₁ m₂ f}
      → ((ε , ε>0) : ℚ₊)
      → ℚ₊
_δ[_] f {iuc} ε = {!iuc!}

δ' : {M₁ : 𝓤 ̇ } {M₂ : 𝓥 ̇ }
   → {m₁ : metric-space M₁}
   → {m₂ : metric-space M₂}
   → (f : M₁ → M₂)
   → {is-uniformly-continuous m₁ m₂ f}
   → ((ε , ε>0) : ℚ₊)
   → ℚ
δ' f ε = pr₁ (_δ[_] f ε)

\end{code}

Statement of theorem : ?

\begin{code}

mℚ = ℚ-metric-space

extension-theorem : 𝓤₁ ̇
extension-theorem = (f : ℚ → ℚ)
                  → (ic : is-uniformly-continuous mℚ mℚ f)
                  → ℝ → ℝ

\end{code}

Introduce some useful notation

\begin{code}

record Order-Chain {𝓤} {𝓥} {𝓦} {𝓣} {𝓧 : Universe} (X : 𝓤 ̇) (Y : 𝓥 ̇) (Z : 𝓦 ̇)
 (_<₁_ : X → Y → 𝓣 ̇)
 (_<₂_ : Y → Z → 𝓧 ̇) :  (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓧)⁺ ̇ where
 field
  _<_<_ : X → Y → Z → 𝓦 ⊔ 𝓧 ̇

 infix 30 _<_<_

open Order-Chain {{...}} public

instance
 Order-Chain-ℚ-ℚ-ℚ : Order-Chain ℚ ℚ ℚ _<_ _<_
 _<_<_ {{Order-Chain-ℚ-ℚ-ℚ}} p q r = (p < q) × (q < r)

 Order-Chain-ℚ-ℝ-ℚ : Order-Chain ℚ ℝ ℚ _<_ _<_
 _<_<_ {{Order-Chain-ℚ-ℝ-ℚ}} p x q = (p < x) × (x < q)

_∈Bℚ[_]_ : (x δ x₀ : ℚ) → 𝓤₀ ̇
x ∈Bℚ[ δ ] x₀ = x₀ - δ < x < x₀ + δ

_∈Bℝ[_]_ : (x : ℝ) → (δ x₀ : ℚ) → 𝓤₀ ̇
x ∈Bℝ[ δ ] x₀ = x₀ - δ < x < x₀ + δ

\end{code}

Prove the theorem

\begin{code}

f→f̂ : extension-theorem
f→f̂ f ic x = (L , R) , il , ir , rl , rr , d , l
 where
  L' R' : ℚ → 𝓤₀ ̇
  L' p = ∃ (x₀ , (ε , 0<ε)) ꞉ ℚ × ℚ₊ , (x ∈Bℝ[ δ' ic (ε , 0<ε) ] x₀)
                                     × p < f x₀ - ε
  R' q = ∃ (x₀ , (ε , 0<ε)) ꞉ ℚ × ℚ₊ , (x ∈Bℝ[ δ' ic (ε , 0<ε) ] x₀)
                                     × f x₀ + ε < q

  L R : 𝓟 ℚ
  L p = L' p , ∃-is-prop
  R q = R' q , ∃-is-prop

  il : inhabited-left L
  il = {!!}

  ir : inhabited-right R
  ir = {!!}

  rl : rounded-left L
  rl = {!!}

  rr : rounded-right R
  rr = {!!}

  d : disjoint L R
  d = {!!}

  l : located L R
  l = {!!}

\end{code}

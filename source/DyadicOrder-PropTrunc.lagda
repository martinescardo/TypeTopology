Tom de Jong, 7 March 2020

As suggested by Martin Escardo.

No endpoints, density and binary interpolation for (𝔻 , ≺) formulated using ∃.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import Dyadic
open import DyadicOrder
open import UF-PropTrunc

module DyadicOrder-PropTrunc (pt : propositional-truncations-exist) where

open PropositionalTruncation pt

≺-has-no-left-endpoint : (x : 𝔻) → ∃ y ꞉ 𝔻 , y ≺ x
≺-has-no-left-endpoint x = ∣ ≺-has-no-left-endpoint-Σ x ∣

≺-has-no-right-endpoint : (x : 𝔻) → ∃ y ꞉ 𝔻 , x ≺ y
≺-has-no-right-endpoint x = ∣ ≺-has-no-right-endpoint-Σ x ∣

≺-is-dense : {x y : 𝔻} → x ≺ y → ∃ z ꞉ 𝔻 , x ≺ z × z ≺ y
≺-is-dense {x} {y} l = ∣ ≺-is-dense-Σ x y l ∣

≺-interpolation₂ : (x₁ x₂ y : 𝔻) → x₁ ≺ y → x₂ ≺ y
                 → ∃ z ꞉ 𝔻 , x₁ ≺ z × x₂ ≺ z × z ≺ y
≺-interpolation₂ x₁ x₂ y l₁ l₂ = ∣ ≺-interpolation₂-Σ x₁ x₂ y l₁ l₂ ∣

\end{code}

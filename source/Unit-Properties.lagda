One-element type properties.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Unit-Properties where

open import Universes
open import Unit
open import Empty
open import Id
open import Negation

𝟙-all-* : (x : 𝟙 {𝓤}) → x ≡ *
𝟙-all-* {𝓤} * = refl {𝓤}
𝟙-is-not-𝟘 : 𝟙 ≢ 𝟘
𝟙-is-not-𝟘 p = transport (λ X → X) p *

\end{code}

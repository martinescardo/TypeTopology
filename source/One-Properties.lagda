One-element type properties.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module One-Properties where

open import Universes
open import One
open import Id

𝟙-all-* : (x : 𝟙 {𝓤}) → x ≡ *
𝟙-all-* {𝓤} * = refl {𝓤}

\end{code}

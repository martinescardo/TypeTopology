Martin Escardo, 5th September 2018, 27th September 2023.

The contents of this file has been generalized in terms of universe levels
and has been moved to UF.Powerset-MultiUniverse.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Powerset where

open import MLTT.Spartan
open import UF.Powerset-MultiUniverse renaming (𝓟 to 𝓟') public

𝓟 : 𝓤  ̇ → 𝓤 ⁺ ̇
𝓟 {𝓤} X = 𝓟' {𝓤} X

\end{code}

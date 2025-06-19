Jonathan Sterling, June 2023

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Dominance.Definition
open import MLTT.Spartan
open import UF.Univalence


import UF.PairFun as PairFun

module Dominance.Initial
        {𝓣 𝓚 : Universe}
        (𝓣-ua : is-univalent 𝓣)
        (d : 𝓣 ̇ → 𝓚 ̇ )
        (isd : is-dominance d)
       where

open import Dominance.Lifting {𝓣} {𝓚} 𝓣-ua d isd
open import W.Type

module Initial-Lift-Algebra where
 ω : 𝓣 ⁺ ⊔ 𝓚 ̇
 ω = W (dominant-prop D) pr₁

\end{code}

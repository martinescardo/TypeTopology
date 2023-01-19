--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

December 2022
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
open import UF.Base
open import PathSequences.Base
open import PathSequences.Concat

module PathSequences.Convenience {X : 𝓤 ̇} where

\end{code}

\begin{code}

reverse : {x y : X} (s : x ≡ y) → y ≡ x
reverse [] = []
reverse (p ◃∙ s) = reverse s ∙▹ (p ⁻¹)
  
\end{code}

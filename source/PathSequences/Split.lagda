--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

November 2022
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan
--open import MLTT.Natural-Numbers-Type 
open import UF.Base
open import PathSequences.Base
open import PathSequences.Concat

module PathSequences.Split {X : 𝓤 ̇} where

\end{code}


\begin{code}

point-from-start : (n : ℕ) {x y : X} (s : x ≡ y) → X
point-from-start zero {x} s = x
point-from-start (succ n) {x} [] = x
point-from-start (succ n) {x} (p ◃∙ s) = point-from-start n s


drop : ( n : ℕ) {x y : X} (s : x ≡ y) → point-from-start n s ≡ y
drop zero s = s
drop (succ n) [] = []
drop (succ n) (p ◃∙ s) = drop n s


tail : {x y : X} (s : x ≡ y) → point-from-start 1 s ≡ y
tail = drop 1


take : (n : ℕ) {x y : X} (s : x ≡ y) → x ≡ point-from-start n s
take zero s = []
take (succ n) [] = []
take (succ n) (p ◃∙ s) = p ◃∙ (take n s)

\end{code}

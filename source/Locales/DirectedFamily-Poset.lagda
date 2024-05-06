--------------------------------------------------------------------------------
title:          Directed families on posets
author:         Ayberk Tosun
date-started:   2024-05-06
--------------------------------------------------------------------------------

Factored out from the `Locales.Frame` module on 2024-05-06.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification --exact-split --double-check #-}

open import UF.PropTrunc
open import UF.FunExt
open import Slice.Family
open import UF.SubtypeClassifier

module Locales.DirectedFamily-Poset (pt : propositional-truncations-exist)
                                    (fe : Fun-Ext) where

open import Locales.Frame pt fe hiding (is-directed)
open import MLTT.Spartan
open import UF.Subsingletons
open import UF.Logic

open AllCombinators pt fe

open PropositionalTruncation pt

\end{code}

We work in a module parameterized by two posets `P` and `Q`.

\begin{code}

module Directed-Families-On-Posets (P : Poset 𝓤 𝓥) (Q : Poset 𝓤' 𝓥') where

\end{code}

We denote the carrier sets of `P` and `Q` by `∣P∣` and `∣Q∣` respectively.

\begin{code}

 ∣P∣ = ∣ P ∣ₚ
 ∣Q∣ = ∣ Q ∣ₚ

\end{code}

\begin{code}

 open import Locales.DirectedFamily pt fe (λ x y → x ≤[ P ] y)
  using ()
  renaming (is-directed to is-directed₁)
 open import Locales.DirectedFamily pt fe (λ x y → x ≤[ Q ] y)
  using (is-closed-under-binary-upper-bounds)
  renaming (is-directed to is-directed₂)

\end{code}

\begin{code}

 monotone-image-on-directed-set-is-directed : ((f , _) : P ─m→ Q)
                                            → (S : Fam 𝓤 ∣  P ∣ₚ)
                                            → is-directed₁ S holds
                                            → is-directed₂ ⁅ f x ∣ x ε S ⁆ holds
 monotone-image-on-directed-set-is-directed (f , 𝓂) S (ι , υ) = ι , †
  where
   † : is-closed-under-binary-upper-bounds ⁅ f x ∣ x ε S ⁆ holds
   † i j = ∥∥-rec ∃-is-prop ‡ (υ i j)
    where
     ‡ : Σ k ꞉ index S ,
           (S [ i ] ≤[ P ] S [ k ]) holds × ((S [ j ] ≤[ P ] S [ k ]) holds)
       → ∃ k ꞉ index S ,
           (f (S [ i ]) ≤[ Q ] f (S [ k ]) ∧ (f (S [ j ]) ≤[ Q ] f (S [ k ])))
         holds
     ‡ (k , p , q) = ∣ k , (𝓂 (S [ i ] , S [ k ]) p , 𝓂 (S [ j ] , S [ k ]) q) ∣

\end{code}

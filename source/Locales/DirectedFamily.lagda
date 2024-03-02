--------------------------------------------------------------------------------
title:          Directed families
author:         Ayberk Tosun
date-started:   2024-03-02
--------------------------------------------------------------------------------

Many constructions and theorems related to directed families have been developed
in various modules despite involving only posets. This is a new module in which
I will be collecting these things that concern only directed families.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons

module Locales.DirectedFamily
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Frame pt fe hiding (is-directed)
open import MLTT.Fin hiding (𝟎; 𝟏)
open import MLTT.List hiding ([_])
open import MLTT.Spartan
open import Slice.Family
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier
open import UF.Equiv

open PropositionalTruncation pt
open AllCombinators pt fe

\end{code}

\section{Directed families}

\begin{code}

module PropertiesOfDirectedFamilies {X : 𝓤  ̇} (_≤_ : X → X → Ω 𝓥) where

\end{code}

Alias for the order just to be able to declare fixity without warnings.

\begin{code}

 infix 7 _⊑_
 _⊑_ = _≤_

\end{code}

\begin{code}

 is-closed-under-binary-upper-bounds : Fam 𝓦 X → Ω (𝓥 ⊔ 𝓦)
 is-closed-under-binary-upper-bounds S =
  Ɐ i ꞉ I , Ɐ j ꞉ I , Ǝₚ k ꞉ I , ((S [ i ] ⊑ S [ k ]) ∧ (S [ j ]) ≤ (S [ k ]))
   where
    I = index S

 is-directed : (S : Fam 𝓦 X) → Ω (𝓥 ⊔ 𝓦)
 is-directed S = ∥ index S ∥Ω ∧ is-closed-under-binary-upper-bounds S

 directed-implies-inhabited : (S : Fam 𝓦 X)
                            → (is-directed S ⇒ ∥ index S ∥Ω) holds
 directed-implies-inhabited S (ι , _) = ι

 directed-implies-closed-under-binary-upper-bounds
  : (S : Fam 𝓦 X)
  → (is-directed S
  ⇒ is-closed-under-binary-upper-bounds S) holds
 directed-implies-closed-under-binary-upper-bounds S (_ , υ) = υ

\end{code}

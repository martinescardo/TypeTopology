Tom de Jong, 27 May 2019.
Refactored December 2021.

* Continuous K and S functions. These will interpret the K and S combinators of
  PCF in ScottModelOfPCF.lagda.
* Continuous ifZero function specific to the lifting of the natural numbers.
  This will then be used to interpret the ifZero combinator of PCF in
  ScottModelOfPCF.lagda.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.ScottModelOfPCF.PCFCombinators
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe)
       where

open import PCF.Combinatory.PCFCombinators pt fe 𝓥 public

\end{code}

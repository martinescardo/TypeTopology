\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import NotionsOfDecidability.Complemented
open import TypeTopology.DiscreteAndSeparated
open import Notation.Order
open import Naturals.Order
open import Naturals.Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient
open import UF.Miscelanea
open import MLTT.Two-Properties
open import MLTT.Plus-Properties
open import UF.Equiv

module Thesis.Chapter4.ApproxOrder-Examples (fe : FunExt) where

open import Thesis.Chapter2.FiniteDiscrete
open import Thesis.Chapter3.ClosenessSpaces fe
open import Thesis.Chapter3.ClosenessSpaces-Examples fe
open import Thesis.Chapter3.SearchableTypes fe
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to _↑
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)



\end{code}

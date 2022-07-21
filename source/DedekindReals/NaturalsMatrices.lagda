Andrew Sneap


\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_)

open import NaturalNumbers
open import Fin
open import UF-FunExt

open import Rationals
open import FieldAxioms
open import FieldRationals

module NaturalsMatrices
  (fe : Fun-Ext)
 where

open import Matrices (RationalsOrderedField' fe)


this : matrix 2 2
this = 2x2ᵢ

\end{code}

Anna Williams 29 January 2026

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Categories.Pre
open import Notation.UnderlyingType

module Categories.Notation.Pre where

open import Categories.Notation.Wild public

module PrecategoryNotation {𝓤 𝓥 : Universe} (P : Precategory 𝓤 𝓥) where
 open WildCategoryNotation ⟨ P ⟩ public

\end{code}

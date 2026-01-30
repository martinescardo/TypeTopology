Anna Williams 29 January 2026

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (id)
open import Categories.Wild
open import Categories.Pre
open import Categories.Notation.Wild
open import Notation.UnderlyingType

module Categories.Notation.Pre where

module PrecategoryNotation {𝓤 𝓥 : Universe} (P : Precategory 𝓤 𝓥) where
 open WildCategoryNotation ⟨ P ⟩ public

\end{code}

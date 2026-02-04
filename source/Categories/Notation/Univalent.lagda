Anna Williams 29 January 2026

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (id)
open import Categories.Wild
open import Categories.Univalent
open import Categories.Notation.Wild
open import Notation.UnderlyingType

module Categories.Notation.Univalent where

module CategoryNotation {𝓤 𝓥 : Universe} (C : Category 𝓤 𝓥) where
 open WildCategoryNotation ⟨ C ⟩ public

\end{code}

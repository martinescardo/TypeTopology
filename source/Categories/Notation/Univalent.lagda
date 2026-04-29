Anna Williams 29 January 2026

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (id)
open import Categories.Univalent
open import Notation.UnderlyingType

module Categories.Notation.Univalent where

open import Categories.Notation.Pre public

module CategoryNotation {𝓤 𝓥 : Universe} (C : Category 𝓤 𝓥) where
 open PrecategoryNotation ⟨ C ⟩ public

\end{code}

Anna Williams 14 February 2026

Notation for working with displayed categories.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Notation.UnderlyingType
open import Categories.Pre
open import Categories.Displayed.Univalent
open import Categories.Displayed.Notation.Pre

module Categories.Displayed.Notation.Univalent where

module DispCatNotation {𝓤 𝓥 : Universe}
                       {P : Precategory 𝓤 𝓥}
                       (D : DisplayedCategory 𝓦 𝓣 P) where
 open DispPrecatNotation ⟨ D ⟩ public


\end{code}

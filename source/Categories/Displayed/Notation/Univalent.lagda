Anna Williams 14 February 2026

Notation for working with displayed categories.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Notation.UnderlyingType
open import Categories.Pre
open import Categories.Notation.Wild
open import Categories.Displayed.Pre
open import Categories.Displayed.Univalent
open import Categories.Displayed.Notation.Pre

module Categories.Displayed.Notation.Univalent where

instance
 d-cat-obj : {P : Precategory 𝓦 𝓣} → DOBJ (obj P) (DisplayedCategory 𝓤 𝓥 P) (𝓤 ̇ )
 obj[_] {{d-cat-obj}} = λ a b → DisplayedPrecategory.obj[ ⟨ b ⟩ ] a

module DisplayedCategoryNotation {𝓤 𝓥 : Universe}
                       {P : Precategory 𝓤 𝓥}
                       (D : DisplayedCategory 𝓦 𝓣 P) where
                       
 open DisplayedPrecategoryNotation ⟨ D ⟩ public

\end{code}

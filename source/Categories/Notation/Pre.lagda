Anna Williams 29 January 2026

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Categories.Pre
open import Notation.UnderlyingType

module Categories.Notation.Pre where

open import Categories.Notation.Wild public

module _ {𝓤 𝓥 : Universe} where
 record PrecatNotation (P : Precategory 𝓤 𝓥) : 𝓤 ⊔ 𝓥 ̇ where
  open WildCategoryNotation ⟨ P ⟩

  field
   to-≅-＝ : {a b : obj P}
           → {f f' : a ≅ b}
           → ⌜ f ⌝ ＝ ⌜ f' ⌝
           → f ＝ f'

 open PrecatNotation {{...}} public

module PrecategoryNotation {𝓤 𝓥 : Universe} (P : Precategory 𝓤 𝓥) where
 instance
  precat-not : PrecatNotation P
  to-≅-＝ {{precat-not}} = isomorphism-properties.to-≅-＝ P

 open WildCategoryNotation ⟨ P ⟩ public

\end{code}

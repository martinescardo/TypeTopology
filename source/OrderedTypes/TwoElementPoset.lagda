Ian Ray, 9 August 2023 updated 11 January 2024.

Constructing the two element poset.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

open import UF.Subsingletons
open import UF.SubtypeClassifier

module OrderedTypes.TwoElementPoset
 (pt : propositional-truncations-exist)
 (fe : Fun-Ext)
 where

open import Locales.Frame pt fe hiding (𝟚; ₀; ₁)

2-Poset : Poset 𝓤₀ 𝓤₀
2-Poset = (𝟚 , 2-ord , 2-ord-is-partial-order)
 where
  2-ord : 𝟚 → 𝟚 →  Ω 𝓤₀
  2-ord ₀ x = (𝟙 , 𝟙-is-prop)
  2-ord ₁ ₀ = (𝟘 , 𝟘-is-prop)
  2-ord ₁ ₁ = (𝟙 , 𝟙-is-prop)

  2-ord-is-partial-order : is-partial-order 𝟚 2-ord
  2-ord-is-partial-order = (2-ord-is-preorder , 2-ord-is-antisymmetric)
   where
    2-ord-is-preorder : is-preorder 2-ord holds
    2-ord-is-preorder = (2-ord-is-reflexive , 2-ord-is-transitive)
     where
      2-ord-is-reflexive : is-reflexive 2-ord holds
      2-ord-is-reflexive ₀ = ⋆
      2-ord-is-reflexive ₁ = ⋆

      2-ord-is-transitive : is-transitive 2-ord holds
      2-ord-is-transitive ₀ y z p q = ⋆
      2-ord-is-transitive ₁ ₀ z p q = 𝟘-elim p
      2-ord-is-transitive ₁ ₁ ₀ p q = 𝟘-elim q
      2-ord-is-transitive ₁ ₁ ₁ p q = ⋆

    2-ord-is-antisymmetric : is-antisymmetric 2-ord
    2-ord-is-antisymmetric {₀} {₀} p q = refl
    2-ord-is-antisymmetric {₀} {₁} p q = 𝟘-elim q
    2-ord-is-antisymmetric {₁} {₀} p q = 𝟘-elim p
    2-ord-is-antisymmetric {₁} {₁} p q = refl

\end{code}

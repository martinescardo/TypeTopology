Martin Escardo, 10 Jun 2026.

A supremum of a compact-indexed family of compact ordinals is
compact. I knew this years ago, and it is used implicitly in some
files.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence
open import UF.PropTrunc

module Ordinals.CompactnessOfSuprema
        (ua : Univalence)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import MLTT.Spartan
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Type
open import Ordinals.Underlying
open import TypeTopology.CompactTypes
open import UF.Size

module _ (sr : Set-Replacement pt) where

 open suprema pt sr

 sup-is-compact∙ : {I : 𝓤 ̇ } {α : I → Ordinal 𝓤}
                 → is-compact∙ I
                 → ((i : I) → is-compact∙ ⟨ α i ⟩)
                 → is-compact∙ ⟨ sup α ⟩
 sup-is-compact∙ {𝓤} {I} {α} I-compact∙ α-compact∙
  = codomain-of-surjection-is-compact∙ pt
     (sum-to-sup α)
     (sum-to-sup-is-surjection α)
     (Σ-is-compact∙ I-compact∙ α-compact∙)

\end{code}

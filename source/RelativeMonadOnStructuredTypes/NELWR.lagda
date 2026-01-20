Martin Escardo and Paulo Oliva, 20th August 2024.

Affine relative monad of non-empty lists without repetitions, assume a
discrete type (a type with decidable equality).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import Notation.General
open import MLTT.Spartan
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.FunExt
open import RelativeMonadOnStructuredTypes.OneSigmaStructure
open import RelativeMonadOnStructuredTypes.Construction {{discrete-𝟙-Σ-structure}}

module RelativeMonadOnStructuredTypes.NELWR
        (fe : Fun-Ext)
       where

open import DiscreteGraphicMonoids.AffineMonad fe

open 𝟙-Σ-structure discrete-𝟙-Σ-structure

instance
 𝕊-is-discrete' : {𝓤 : Universe} {𝓧 : 𝕊 𝓤} → is-discrete' ⟨ 𝓧 ⟩
 𝕊-is-discrete' {𝓤} {𝓧} = discrete-gives-discrete' (underlying-structure 𝓧)

NELWR : Relative-Monad {λ 𝓤 → 𝓤}
NELWR =
 record {
    functor = λ 𝓧 → List⁻⁺ ⟨ 𝓧 ⟩
  ; η = λ {𝓤} {𝓧} → η⁻⁺ {𝓤} {⟨ 𝓧 ⟩}
  ; ext = λ {𝓤} {𝓥} {𝓧} {𝓨} → ext⁻⁺ {𝓤} {𝓥} {⟨ 𝓧 ⟩} {⟨ 𝓨 ⟩}
  ; ext-η = λ {𝓤} {𝓧} → ext-η⁻⁺ {𝓤} {⟨ 𝓧 ⟩} {{𝕊-is-discrete' {𝓤} {𝓧}}}
  ; unit = λ {𝓤} {𝓥} {𝓧} {𝓨}
             → unit⁻⁺ {𝓤} {𝓥} {⟨ 𝓧 ⟩} {{𝕊-is-discrete' {𝓤} {𝓧}}} {⟨ 𝓨 ⟩}
  ; assoc = λ {𝓤} {𝓥} {𝓦} {𝓧} {𝓨} {𝓩}
             → assoc⁻⁺ {𝓤} {𝓥} {𝓦} {⟨ 𝓧 ⟩} {⟨ 𝓨 ⟩} {⟨ 𝓩 ⟩}
  }

NELWR-is-affine : is-affine NELWR
NELWR-is-affine = affine⁻⁺

\end{code}

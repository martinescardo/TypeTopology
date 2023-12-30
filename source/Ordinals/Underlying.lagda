Martin Escardo 3rd January 2023

Type-class for notation for underlying set and order of various kinds
of ordinals.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Ordinals.Underlying where

open import MLTT.Spartan
open import Ordinals.Notions

record Underlying {𝓤} (O : 𝓤 ⁺ ̇ ) : 𝓤 ⁺ ̇  where
 field
  ⟨_⟩              : O → 𝓤 ̇
  underlying-order : (α : O) → ⟨ α ⟩ → ⟨ α ⟩ → 𝓤 ̇

 underlying-weak-order : (α : O) → ⟨ α ⟩ → ⟨ α ⟩ → 𝓤 ̇
 underlying-weak-order α x y = ¬ (underlying-order α y x)

 underlying-porder : (α : O) → ⟨ α ⟩ → ⟨ α ⟩ → 𝓤 ̇
 underlying-porder α = extensional-po (underlying-order α)

 syntax underlying-order      α x y = x ≺⟨ α ⟩ y
 syntax underlying-weak-order α x y = x ≾⟨ α ⟩ y
 syntax underlying-porder     α x y = x ≼⟨ α ⟩ y

open Underlying {{...}} public

\end{code}

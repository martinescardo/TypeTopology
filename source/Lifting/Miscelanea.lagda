Tom de Jong 22nd May 2019

A few basic lemmas for working with partial elements of a type.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Lifting.Miscelanea (𝓣 : Universe) where

open import Lifting.Lifting 𝓣

module _ {𝓤 : Universe}
         {X : 𝓤 ̇ }
       where

 value-is-constant : (l : 𝓛 X) (d e : is-defined l) → value l d ＝ value l e
 value-is-constant l d e = ap (value l) (being-defined-is-prop l d e)

 ＝-of-values-from-＝ : {l m : 𝓛 X} {d : is-defined l} {e : is-defined m}
                    → l ＝ m → value l d ＝ value m e
 ＝-of-values-from-＝ {l} {m} {d} {e} refl = value-is-constant l d e

 ＝-to-is-defined : {l m : 𝓛 X} → l ＝ m → is-defined l → is-defined m
 ＝-to-is-defined e d = transport is-defined e d

\end{code}

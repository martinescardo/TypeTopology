Ayberk Tosun, started 7th December 2022

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.PropTrunc
open import MLTT.List hiding ([_])

module Locales.UniversalPropertyOfPatch
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import UF.Subsingletons
open import UF.Subsingleton-Combinators
open import UF.Subsingletons-FunExt

open AllCombinators pt fe

open import Locales.Frame pt fe
open import Locales.CompactRegular pt fe
open import Locales.BooleanAlgebra pt fe
open import Locales.PatchLocale pt fe

open PropositionalTruncation pt

\end{code}

\begin{code}

open Locale

module UniversalProperty (A : Locale (𝓤 ⁺) 𝓤 𝓤) (σ : is-spectral (𝒪 A) holds) where

 open PatchConstruction A σ renaming (Patch to Patch-A)

 ump-of-patch : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
              → is-stone (𝒪 X) holds
              → (f : X ─c→ A)
              → is-spectral-map (𝒪 A) (𝒪 X) f holds
              → is-contr (Σ f⁻ ꞉ (X ─c→ Patch-A) , f⁻ ＝ {!f ∘ ?!})
 ump-of-patch = {!!}

 𝕂 : BooleanAlgebra {!!} {!!}
 𝕂 = {!ℬ-patch!}

\end{code}

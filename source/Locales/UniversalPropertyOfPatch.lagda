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
open import Locales.PatchProperties pt fe

open PropositionalTruncation pt

\end{code}

\begin{code}

open Locale

module UniversalProperty (A : Locale (𝓤 ⁺) 𝓤 𝓤) (σ : is-spectral (𝒪 A) holds) where

 open PatchConstruction A σ renaming (Patch to Patch-A)
 open ClosedNucleus A σ

 ump-of-patch : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
              → is-stone (𝒪 X) holds
              → (𝒻 : X ─c→ A)
              → is-spectral-map (𝒪 A) (𝒪 X) 𝒻 holds
              → is-contr (Σ 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻ .pr₁ ‘ x ’))
 ump-of-patch X 𝕤 𝒻 μ = ∥∥-rec (being-singleton-is-prop fe) γ σ
  where
   γ : spectralᴰ (𝒪 A)
     → is-contr (Σ 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻ .pr₁ ‘ x ’))
   γ σᴰ = ({!!} , {!!}) , {!!}
    where
     open SmallPatchConstruction A σᴰ renaming (SmallPatch to Patchₛ-A)
     open BasisOfPatch A σᴰ

     𝒞𝓁ℴ𝓅 : {!!}
     𝒞𝓁ℴ𝓅 = {!!}

     𝒻⁻ : X ─c→ Patchₛ-A
     𝒻⁻ = {!!}

     𝕂 : BooleanAlgebra (𝓤 ⁺) {!!}
     𝕂 = (Σ x ꞉ ⟨ 𝒪 A ⟩ , is-clopen (𝒪 A) x holds)
       , ({!!} , {!!}) , {!!}

\end{code}

---
author:      "Ayberk Tosun"
start-date:  2023-10-26
---

Ayberk Tosun

Started on: 2023-10-26

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
-- open import UF.Subsingletons-FunExt
-- open import UF.Powerset-MultiUniverse

module DomainTheory.BasesAndContinuity.BoundedCompleteness
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥  : Universe) where

open import Slice.Family

open import DomainTheory.Basics.Dcpo                   pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥

open import Locales.Frame hiding (⟨_⟩)

open Universal   fe
open Implication fe
open Existential pt
open Conjunction

open Locale

open PropositionalTruncation pt

\end{code}

We first define the notion of a 𝓣-family having an upper bound.

\begin{code}

module DefinitionOfBoundedCompleteness (𝓓 : DCPO {𝓤} {𝓣}) where

\end{code}

We denote by `_⊑_` the informating ordering of the dcpo `𝓓`.

\begin{code}

 _⊑_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓣  ̇
 x ⊑ y = x ⊑⟨ 𝓓 ⟩ y

\end{code}

\begin{code}

 has-an-upper-bound : Fam 𝓣 ⟨ 𝓓 ⟩ → Ω (𝓤 ⊔ 𝓣)
 has-an-upper-bound (_ , ι) =
  Ǝ u ꞉ ⟨ 𝓓 ⟩ , is-upperbound (underlying-order 𝓓) u ι

\end{code}

We also define a reformulation of having an upper bound. The reason for this
reformulation is to have a version more suitable the notion of family that I use
(Ayberk Tosun), which is the one from `Slice.Family`. Moreover, it is also
convenient have a version of this notion that is packaged up with the proof of
propositional so that it can be defined as an `Ω`-valued function.

\begin{code}

 has-supₚ : Fam 𝓣 ⟨ 𝓓 ⟩ → Ω (𝓤 ⊔ 𝓣)
 has-supₚ (I , ι) = has-sup (underlying-order 𝓓) ι
                  , having-sup-is-prop _⊑_ (pr₁ (axioms-of-dcpo 𝓓) ) ι

\end{code}


Bounded completeness then says any family that has an upper bound, also has a
least upper bound.

\begin{code}

 bounded-complete : Ω (𝓤 ⊔ (𝓣 ⁺) ⊔ 𝓤)
 bounded-complete = Ɐ S ꞉ Fam 𝓣 ⟨ 𝓓 ⟩ , has-an-upper-bound S ⇒ has-supₚ S

\end{code}

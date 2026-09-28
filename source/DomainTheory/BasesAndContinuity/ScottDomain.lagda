---
title:       Scott domains
author:      Ayberk Tosun
start-date:  2023-10-26
---

Ayberk Tosun.

Started on 26 October 2023.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier

module DomainTheory.BasesAndContinuity.ScottDomain
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥  : Universe)
       where

open import Slice.Family

open import DomainTheory.Basics.Dcpo                   pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Bases      pt fe 𝓥

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

 _⊑_ : ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → 𝓣 ̇
 x ⊑ y = x ⊑⟨ 𝓓 ⟩ y

\end{code}

\begin{code}

 has-an-upper-bound : Fam 𝓣 ⟨ 𝓓 ⟩ → Ω (𝓤 ⊔ 𝓣)
 has-an-upper-bound (_ , ι) =
  Ǝ u ꞉ ⟨ 𝓓 ⟩ , is-upperbound (underlying-order 𝓓) u ι

\end{code}

We also define a reformulation `has-supₚ` of `has-sup` from
`DomainTheory.Basics.Dcpo`. The reason for this reformulation is to have a
version more suitable to use with notion of family that I (Ayberk) use, which is
the one from `Slice.Family`. Moreover, it is also convenient to have a version
of this notion that is packaged up with the proof of its propositionality so
that it can be defined directly as an `Ω`-valued function.

\begin{code}

 has-supₚ : Fam 𝓣 ⟨ 𝓓 ⟩ → Ω (𝓤 ⊔ 𝓣)
 has-supₚ (I , ι) = has-sup (underlying-order 𝓓) ι
                  , having-sup-is-prop _⊑_ (pr₁ (axioms-of-dcpo 𝓓)) ι

\end{code}

Bounded completeness then says that any family that has an upper bound also has
a least upper bound.

\begin{code}

 bounded-complete : Ω (𝓤 ⊔ 𝓣 ⁺)
 bounded-complete = Ɐ S ꞉ Fam 𝓣 ⟨ 𝓓 ⟩ , has-an-upper-bound S ⇒ has-supₚ S

\end{code}

We now proceed to define the notion of a Scott domain.

\begin{code}

module DefinitionOfScottDomain (𝓓 : DCPO {𝓤} {𝓣}) where

 open DefinitionOfBoundedCompleteness

 has-unspecified-small-compact-basisₚ : Ω (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓣)
 has-unspecified-small-compact-basisₚ = has-unspecified-small-compact-basis 𝓓
                                      , ∃-is-prop

 is-scott-domain : Ω (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓣 ⁺)
 is-scott-domain =
  has-unspecified-small-compact-basisₚ ∧ bounded-complete 𝓓

\end{code}

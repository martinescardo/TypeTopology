Ayberk Tosun, 29 September 2023

This module contains a definition of the Scott locale of a dcpo, using the definition of
dcpo from the `DomainTheory` development due to Tom de Jong.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Pi
open import MLTT.Spartan
open import Slice.Family
open import UF.Base
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.Univalence
open import Slice.Family

\end{code}

We assume the existence of propositional truncations as well as function extensionality.

\begin{code}

module Locales.ScottLocale.ScottLocalesOfAlgebraicDcpos
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓤  : Universe)
        where

open Universal fe
open Implication fe
open Existential pt
open Conjunction

open import Locales.Frame pt fe

open import DomainTheory.Basics.Dcpo pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤

open PropositionalTruncation pt

\end{code}

\begin{code}

module ScottLocaleConstruction (𝓓 : DCPO {𝓤 ⁺} {𝓤}) (hscb : has-specified-small-compact-basis 𝓓) (pe : propext 𝓤) where

 open import DomainTheory.Lifting.LiftingSet pt fe 𝓤 pe
 open DefnOfScottTopology 𝓓 𝓤

\end{code}

`𝒪ₛ` is the type of 𝓦-Scott-opens over dcpo `𝓓`.

\begin{code}

 𝕒 : structurally-algebraic 𝓓
 𝕒 = structurally-algebraic-if-specified-small-compact-basis 𝓓 hscb

\end{code}

We denote by `I` the index type of the basis:

\begin{code}

 I = pr₁ hscb
 β = pr₁ (pr₂ hscb)

 ℬ : Fam 𝓤 ⟨ 𝓓 ⟩∙
 ℬ = (I , β)

 𝒪ₛ-equality : (U V : 𝒪ₛ)
             → ((i j : I) → (ℬ [ i ]) ∈ₛ U  ＝ (ℬ [ j ]) ∈ₛ V)
             → U ＝ V
 𝒪ₛ-equality U V φ =
  to-subtype-＝ (holds-is-prop ∘ is-scott-open) {!pe ? ? ? ?!}
   where
    † : {!!}
    † = {!!}

\end{code}

These are ordered by inclusion.

\begin{code}

 open structurally-algebraic

 _⊆ₛ_ : 𝒪ₛ → 𝒪ₛ → Ω 𝓤
 (U , _) ⊆ₛ (V , _) = Ɐ i ꞉ I , U (ℬ [ i ]) ⇒ V (ℬ [ i ])

 ⊆ₛ-is-reflexive : is-reflexive _⊆ₛ_ holds
 ⊆ₛ-is-reflexive (U , δ) _ = id

 ⊆ₛ-is-transitive : is-transitive _⊆ₛ_ holds
 ⊆ₛ-is-transitive (U , δ) (V , ϵ) (W , ζ) p q x = q x ∘ p x

 -- ⊆ₛ-is-antisymmetric : is-antisymmetric _⊆ₛ_
 -- ⊆ₛ-is-antisymmetric {U} {V} p q =
 --  𝒪ₛ-equality
 --   U
 --   V
 --   (dfunext fe λ i → to-subtype-＝
 --     (λ _ → being-prop-is-prop fe)
 --     (pe
 --       (holds-is-prop {!!})
 --       (holds-is-prop {!!})
 --       {!p ?!}
 --       {!!}))

 -- ⊆ₛ-is-partial-order : is-partial-order 𝒪ₛ _⊆ₛ_
 -- ⊆ₛ-is-partial-order = (⊆ₛ-is-reflexive , ⊆ₛ-is-transitive) , ⊆ₛ-is-antisymmetric

\end{code}

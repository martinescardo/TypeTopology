\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import MLTT.Spartan
open import UF.PropTrunc
open import UF.FunExt
open import UF.Logic
open import UF.Subsingletons

module Locales.ClassificationOfScottOpens
        (𝓤  : Universe)
        (pt : propositional-truncations-exist)
        (pe : propext 𝓤)
        (fe : Fun-Ext) where

open Universal fe
open Implication fe
open Existential pt
open Conjunction

open import Locales.Frame pt fe
open import DomainTheory.Basics.Dcpo pt fe 𝓤 renaming (⟨_⟩ to ⟨_⟩∙)
open import DomainTheory.Topology.ScottTopology pt fe 𝓤
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.Lifting.LiftingSet pt fe
open import DomainTheory.Basics.Miscelanea pt fe 𝓤
open import Lifting.Lifting 𝓤

\end{code}

We first define the Sierpinski domain.

\begin{code}

𝕊 : DCPO⊥
𝕊 = 𝓛-DCPO⊥ 𝓤 pe (props-are-sets {X = 𝟙 {𝓤 ⁺}} 𝟙-is-prop)

\end{code}

\begin{code}

module _ {𝓓 : DCPO⊥ {𝓤 ⁺} {𝓤}} where

 to-predicate : DCPO⊥[ 𝓓 , 𝕊 ] → (⟪ 𝓓 ⟫ → Ω 𝓤)
 to-predicate (f , p) x = is-defined (f x) , being-defined-is-prop (f x)

 open DefnOfScottTopology (𝓓 ⁻) 𝓤

 predicate-is-upwards-closed : (𝒻 : DCPO⊥[ 𝓓 , 𝕊 ])
                             → is-upwards-closed (to-predicate 𝒻) holds
 predicate-is-upwards-closed 𝒻@(f , υ) x y p q =
  transport is-defined (μ x y q p) p
   where
    μ : is-monotone (𝓓 ⁻) (𝕊 ⁻) f
    μ = monotone-if-continuous (𝓓 ⁻) (𝕊 ⁻) 𝒻

\end{code}

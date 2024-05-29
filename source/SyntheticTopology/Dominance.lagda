---
title:                  Dominance and Phoa's principle in Synthetic Topology
authors:            [Martin Trucchi , Ayberk Tosun]
date-started:  2024-05-28
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import SyntheticTopology.SierpinskiObject 

module SyntheticTopology.Dominance
        (𝓤  𝓥 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Generalized-Sierpinski-Object fe pe pt 𝓤 𝓥)
        where

open import UF.Logic

open AllCombinators pt fe
open Sierpinski-notations fe pe pt 𝕊


\end{code}

We write down the Dominance Axiom and Phoa’s Principle.

First, the Dominance Axiom:

\begin{code}

openness-is-transitive : ((𝓤 ⁺) ⊔ 𝓥) ̇
openness-is-transitive = (u : Ω 𝓤)
                                         → (is-affirmable u) holds
                                         → (p : Ω 𝓤)
                                         → (u holds → (is-affirmable p) holds)
                                         → (is-affirmable (u ∧ p) ) holds

contains-top : Ω 𝓥
contains-top = is-affirmable ⊤

is-synthetic-dominance : (𝓤 ⁺ ⊔ 𝓥) ̇
is-synthetic-dominance = contains-top holds × openness-is-transitive

\end{code}

Phoa’s Principle:

\begin{code}

phoa’s-principle :  Ω (𝓤 ⁺ ⊔ 𝓥)
phoa’s-principle =
  Ɐ f ꞉ (Ω 𝓤 → Ω 𝓤) , Ɐ U ꞉ Ω 𝓤 , is-affirmable U ⇒ f U ⇔ (f ⊥ ∨  U) ∧ f ⊤

\end{code}

We also give a natural axiom saying that the Sierpinski object is being closed under
binary (and thus, finite if contains-top holds) meets :

\begin{code}

closed-under-binary-meets : Ω (𝓤 ⁺ ⊔ 𝓥)
closed-under-binary-meets =
 Ɐ P ꞉ Ω 𝓤 ,
  Ɐ Q ꞉ Ω 𝓤 ,
   ((is-affirmable P ∧ is-affirmable Q)
    ⇒ is-affirmable (P ∧ Q))

\end{code}

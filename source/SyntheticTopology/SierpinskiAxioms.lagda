---
title:        Axioms about the Sierpinski object
authors:      [Martin Trucchi , Ayberk Tosun]
date-started: 2024-05-28
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

module SyntheticTopology.SierpinskiAxioms
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

contains-top : Ω 𝓥
contains-top = is-open-proposition ⊤

openness-is-transitive : Ω ((𝓤 ⁺) ⊔ 𝓥)
openness-is-transitive =
 Ɐ u ꞉ (Ω 𝓤) ,
  (is-open-proposition u
   ⇒ (Ɐ p ꞉ (Ω 𝓤) ,
    (u ⇒ (is-open-proposition p))
     ⇒ (is-open-proposition (u ∧ p))))

is-synthetic-dominance : Ω (𝓤 ⁺ ⊔ 𝓥)
is-synthetic-dominance = contains-top ∧ openness-is-transitive

\end{code}

Phoa’s Principle:

Note that Phoa's principle concerns only functions from the Sierpinski object
to itself. Here we restricts to open propositions after, but it may not be the
correct way to do it.

\begin{code}

phoa’s-principle :  Ω (𝓤 ⁺ ⊔ 𝓥)
phoa’s-principle =
  Ɐ f ꞉ (Ω 𝓤 → Ω 𝓤) ,
   Ɐ U ꞉ Ω 𝓤 , is-open-proposition U ⇒ f U ⇔ (f ⊥ ∨ U) ∧ f ⊤

\end{code}

We also give a natural axiom saying that the Sierpinski object is being closed
under binary (and thus, finite if contains-top holds) meets :

\begin{code}

closed-under-binary-meets : Ω (𝓤 ⁺ ⊔ 𝓥)
closed-under-binary-meets =
 Ɐ P ꞉ Ω 𝓤 ,
  Ɐ Q ꞉ Ω 𝓤 ,
   ((is-open-proposition P ∧ is-open-proposition Q)
    ⇒ is-open-proposition (P ∧ Q))

\end{code}


Added by Martin Trucchi - 3rd June 2024.

The latter directly follows from openness-is-transitive. It is a particular
case in which both P and Q are known to be open.

\begin{code}

open-transitive-gives-cl-∧
 : (openness-is-transitive ⇒ closed-under-binary-meets) holds
open-transitive-gives-cl-∧ open-transitive P Q (open-P , open-Q) =
  open-transitive P open-P Q λ _ → open-Q

\end{code}


We define here the axiom of being a "standard topology", defined on 5.9 of [1]

\begin{code}

contains-bot : Ω 𝓥
contains-bot = is-open-proposition ⊥

closed-under-binary-joins : Ω ((𝓤 ⁺) ⊔ 𝓥)
closed-under-binary-joins =
 Ɐ P ꞉ Ω 𝓤 ,
  Ɐ Q ꞉ Ω 𝓤 ,
   ((is-open-proposition P ∧ is-open-proposition Q)
    ⇒ is-open-proposition (P ∨ Q))

is-standard : Ω ((𝓤 ⁺) ⊔ 𝓥)
is-standard = contains-bot ∧ closed-under-binary-joins

\end{code}


[1] : https://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf

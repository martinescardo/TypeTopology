\begin{code}

{-# OPTIONS --safe --without-K --exact-split --auto-inline --lossy-unification #-}

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
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Sierpinski-Object 𝓤 fe pe pt)
        where

open import UF.Logic

open AllCombinators pt fe
open Sierpinski-notations 𝓤 fe pe pt 𝕊


\end{code}

We are now ready to write down the Dominance Axiom and Phoa’s Principle.

First, the Dominance Axiom:

\begin{code}

openness-is-transitive :  (𝓤 ⁺) ̇
openness-is-transitive = (u : Ω 𝓤)
                                         → (is-affirmable u) holds
                                         → (p : Ω 𝓤)
                                         → (u holds → (is-affirmable p) holds)
                                         → (is-affirmable (u ∧ p) ) holds

contains-top : Ω (𝓤 ⁺)
contains-top = is-affirmable (⊤ {𝓤})

is-synthetic-dominance : (𝓤 ⁺) ̇
is-synthetic-dominance = contains-top holds × openness-is-transitive

\end{code}

Phoa’s Principle:

\begin{code}

phoa’s-principle : Ω (𝓤 ⁺)
phoa’s-principle =
  Ɐ f ꞉ (Ω 𝓤 → Ω 𝓤) , Ɐ U ꞉ Ω 𝓤 , is-affirmable U ⇒ f U ⇔ (f ⊥ ∨  U) ∧ f ⊤

\end{code}

Sierpinski being closed under finite meets :

\begin{code}

closed-under-binary-meets : Ω (𝓤 ⁺)
closed-under-binary-meets = Ɐ P ꞉ Ω 𝓤 , Ɐ Q ꞉ Ω 𝓤 , ((is-affirmable P ∧ is-affirmable Q) ⇒ is-affirmable (P ∧ Q))

\end{code}

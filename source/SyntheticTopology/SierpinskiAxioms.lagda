---
title:          Axioms about the Sierpinski object
authors:        ["Martin Trucchi" , "Ayberk Tosun"]
date-started:   2024-05-28
dates-modified: [2024-06-07]
---

We write down here various axioms for the Sierpinski object, defined in TODO.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.Logic
open import UF.Powerset
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

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations fe pe pt 𝕊

\end{code}

TODO : ADD REFERENCES

\section{Dominance axiom}

The dominance axiom is the most used axiom in our setting.

\begin{code}

contains-top : Ω 𝓥
contains-top = is-open-proposition ⊤

openness-is-transitive : Ω (𝓤 ⁺ ⊔ 𝓥)
openness-is-transitive =
 Ɐ u ꞉ Ω 𝓤 ,
  (is-open-proposition u
   ⇒ (Ɐ p ꞉ Ω 𝓤 ,
    (u ⇒ (is-open-proposition p))
     ⇒ (is-open-proposition (u ∧ p))))

is-synthetic-dominance : Ω (𝓤 ⁺ ⊔ 𝓥)
is-synthetic-dominance = contains-top ∧ openness-is-transitive

\end{code}

We also give a natural axiom saying that the Sierpinski object is being closed
under binary (and thus, finite if `contains-top` holds) meets :

\begin{code}

closed-under-binary-meets : Ω (𝓤 ⁺ ⊔ 𝓥)
closed-under-binary-meets =
 Ɐ p ꞉ Ω 𝓤 ,
  Ɐ q ꞉ Ω 𝓤 ,
   ((is-open-proposition p ∧ is-open-proposition q)
    ⇒ is-open-proposition (p ∧ q))

\end{code}

Added by Martin Trucchi - 3rd June 2024.

The latter directly follows from `openness-is-transitive`. It is a particular
case in which both `P` and `Q` are known to be `open-proposition`.

\begin{code}

open-transitive-gives-cl-∧
 : (openness-is-transitive ⇒ closed-under-binary-meets) holds
open-transitive-gives-cl-∧ open-transitive p q (open-p , open-q) =
  open-transitive p open-p q λ _ → open-q

\end{code}

\section{Phoa's principle}

Note that Phoa's principle concerns only functions from the Sierpinski object
to itself. Here we restricts to open propositions after, but it may not be the
correct way to do it.

The second argument to give to `phoa’s-principle` states that `f` sends
open propositions to open propositions. It could have been merged into the
third argument, having an (equivalent) condition looking like :
`Ɐ v ꞉ Ω 𝓤 ,
 is-open-proposition v ⇒ (is-open-proposition v) ∧ (f v ⇔ ((f ⊤ ∧ v) ∨ f ⊥)))`.

We did not choose the later because it is more confusing about the "true" nature
of `phoa’s-principle` statement.

\begin{code}

phoa’s-principle :  Ω (𝓤 ⁺ ⊔ 𝓥)
phoa’s-principle =
  Ɐ f ꞉ (Ω 𝓤 → Ω 𝓤) ,
   (Ɐ p ꞉ Ω 𝓤 , (is-open-proposition p ⇒ is-open-proposition (f p))) ⇒
    (Ɐ q ꞉ Ω 𝓤 , is-open-proposition q ⇒ f q ⇔ ((f ⊤ ∧ q) ∨ f ⊥))

\end{code}

As proved in TODO , `phoa’s-principle` implies that all endomaps of the
Sierpinski are monotonous.

\begin{code}

⇒-functor : (p p' q q' : Ω 𝓤)
      → ((p ⇔ p') holds)
      → ((q ⇔ q') holds)
      → ((p ⇒ q) holds)
      → ((p' ⇒ q') holds)

⇒-functor p p' q q' p-eq-p' q-eq-q' p-gives-q p'-holds =
 ⇔-transport pe q q' _holds q-eq-q'
   (p-gives-q (⇔-transport pe p' p _holds (⇔-swap pe p p' p-eq-p') p'-holds))

phoa’s-principle-gives-monotonous-maps
 : (phoa’s-principle ⇒
    (Ɐ f ꞉ (Ω 𝓤 → Ω 𝓤) ,
     (Ɐ u ꞉ Ω 𝓤 , (is-open-proposition u ⇒ is-open-proposition (f u))) ⇒
      (Ɐ p ꞉ Ω 𝓤 , is-open-proposition p ⇒
       (Ɐ q ꞉ Ω 𝓤 , is-open-proposition q ⇒
        (p ⇒ q) ⇒ (f p ⇒ f q))))) holds

phoa’s-principle-gives-monotonous-maps
 phoa-p f sierpinski-valued-f p open-p q open-q p-gives-q =
  ⇔-transport pe
              (((f ⊤ ∧ p) ∨ f ⊥) ⇒ ((f ⊤ ∧ q) ∨ f ⊥))
              (f p ⇒ f q)
              _holds
              (equiv₁ , equiv₂)
              †
   where
    equiv₁ : (((f ⊤ ∧ p ∨ f ⊥) ⇒ (f ⊤ ∧ q ∨ f ⊥)) ⇒ f p ⇒ f q) holds
    equiv₁ = ⇒-functor (f ⊤ ∧ p ∨ f ⊥)
                       (f p)
                       (f ⊤ ∧ q ∨ f ⊥)
                       (f q)
                       (⇔-swap pe (f p) (f ⊤ ∧ p ∨ f ⊥)
                                        (phoa-p f sierpinski-valued-f p open-p))
                       (⇔-swap pe (f q) (f ⊤ ∧ q ∨ f ⊥)
                                        (phoa-p f sierpinski-valued-f q open-q))

    equiv₂ : ((f p ⇒ f q) ⇒ (f ⊤ ∧ p ∨ f ⊥) ⇒ (f ⊤ ∧ q ∨ f ⊥)) holds
    equiv₂ = ⇒-functor (f p)
                       (f ⊤ ∧ p ∨ f ⊥)
                       (f q)
                       (f ⊤ ∧ q ∨ f ⊥)
                       (phoa-p f sierpinski-valued-f p open-p)
                       (phoa-p f sierpinski-valued-f q open-q)

    † : ((f ⊤ ∧ p ∨ f ⊥) ⇒ (f ⊤ ∧ q ∨ f ⊥)) holds
    † and-or-p = ∥∥-rec (holds-is-prop (f ⊤ ∧ q ∨ f ⊥))
                        (cases (λ (f-top-holds , p-holds) →
                                 ∣ inl (f-top-holds , p-gives-q p-holds)  ∣)
                               (∣_∣ ∘ inr))
                        and-or-p



\end{code}

\section{Standard topology}

We define here the axiom of being a `standard-topology`, defined on 5.9 of [1]
TODO : NICER CITATION
Note that not all "used" Sierpinski verify this
(e.g. : see paper haskell in TODO)

\begin{code}

contains-bot : Ω 𝓥
contains-bot = is-open-proposition ⊥

closed-under-binary-joins : Ω (𝓤 ⁺ ⊔ 𝓥)
closed-under-binary-joins =
 Ɐ p ꞉ Ω 𝓤 ,
  Ɐ q ꞉ Ω 𝓤 ,
   ((is-open-proposition p ∧ is-open-proposition q)
    ⇒ is-open-proposition (p ∨ q))

is-standard : Ω (𝓤 ⁺ ⊔ 𝓥)
is-standard = contains-bot ∧ closed-under-binary-joins

\end{code}

[1] : https://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf
[2] : Paper haskell

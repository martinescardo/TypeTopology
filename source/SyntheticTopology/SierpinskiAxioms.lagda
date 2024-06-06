---
title:        Axioms about the Sierpinski object
authors:      ['Martin Trucchi' , 'Ayberk Tosun']
date-started: 2024-05-28
dates-modified: [2024-06-06]
---

We write down here various axioms for the Sierpinski object, defined in TODO.

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
 Ɐ U ꞉ Ω 𝓤 ,
  (is-open-proposition U
   ⇒ (Ɐ P ꞉ Ω 𝓤 ,
    (U ⇒ (is-open-proposition P))
     ⇒ (is-open-proposition (U ∧ P))))

is-synthetic-dominance : Ω (𝓤 ⁺ ⊔ 𝓥)
is-synthetic-dominance = contains-top ∧ openness-is-transitive

\end{code}

We also give a natural axiom saying that the Sierpinski object is being closed
under binary (and thus, finite if `contains-top` holds) meets :

\begin{code}

closed-under-binary-meets : Ω (𝓤 ⁺ ⊔ 𝓥)
closed-under-binary-meets =
 Ɐ P ꞉ Ω 𝓤 ,
  Ɐ Q ꞉ Ω 𝓤 ,
   ((is-open-proposition P ∧ is-open-proposition Q)
    ⇒ is-open-proposition (P ∧ Q))

\end{code}

Added by Martin Trucchi - 3rd June 2024.

The latter directly follows from `openness-is-transitive`. It is a particular
case in which both `P` and `Q` are known to be `open-proposition`.

\begin{code}

open-transitive-gives-cl-∧
 : (openness-is-transitive ⇒ closed-under-binary-meets) holds
open-transitive-gives-cl-∧ open-transitive P Q (open-P , open-Q) =
  open-transitive P open-P Q λ _ → open-Q

\end{code}

\section{Phoa's principle}

Note that Phoa's principle concerns only functions from the Sierpinski object
to itself. Here we restricts to open propositions after, but it may not be the
correct way to do it.

The second argument to give to `phoa’s-principle` states that `f` sends
open propositions to open propositions. It could have been merged into the
third argument, having an (equivalent) condition looking like :
`Ɐ V ꞉ Ω 𝓤 ,
 is-open-proposition V ⇒ (is-open-proposition V) ∧ (f V ⇔ ((f ⊤ ∧ V) ∨ f ⊥)))`.

We did not choose the later because it is more confusing about the "true" nature
of `phoa’s-principle` statement.

\begin{code}

phoa’s-principle :  Ω (𝓤 ⁺ ⊔ 𝓥)
phoa’s-principle =
  Ɐ f ꞉ (Ω 𝓤 → Ω 𝓤) ,
   (Ɐ U ꞉ Ω 𝓤 , (is-open-proposition U ⇒ is-open-proposition (f U))) ⇒
    (Ɐ V ꞉ Ω 𝓤 , is-open-proposition V ⇒ f V ⇔ ((f ⊤ ∧ V) ∨ f ⊥))

\end{code}

As proved in TODO , `phoa’s-principle` implies that all endomaps of the
Sierpinski are monotonous.

\begin{code}

⇒-functor : (P P' Q Q' : Ω 𝓤)
      → ((P ⇔ P') holds)
      → ((Q ⇔ Q') holds)
      → ((P ⇒ Q) holds)
      → ((P' ⇒ Q') holds)

⇒-functor P P' Q Q' P-eq-P' Q-eq-Q' P-gives-Q P'-holds =
 ⇔-transport pe Q Q' _holds Q-eq-Q'
   (P-gives-Q (⇔-transport pe P' P _holds (⇔-swap pe P P' P-eq-P') P'-holds))

phoa’s-principle-gives-monotonous-maps
 : (phoa’s-principle ⇒
    (Ɐ f ꞉ (Ω 𝓤 → Ω 𝓤) ,
     (Ɐ U ꞉ Ω 𝓤 , (is-open-proposition U ⇒ is-open-proposition (f U))) ⇒
      (Ɐ P ꞉ Ω 𝓤 , is-open-proposition P ⇒
       (Ɐ Q ꞉ Ω 𝓤 , is-open-proposition Q ⇒
        (P ⇒ Q) ⇒ (f P ⇒ f Q))))) holds

phoa’s-principle-gives-monotonous-maps
 phoa-p f sierpinski-valued-f P open-P Q open-Q P-gives-Q =
  ⇔-transport pe
              (((f ⊤ ∧ P) ∨ f ⊥) ⇒ ((f ⊤ ∧ Q) ∨ f ⊥))
              (f P ⇒ f Q)
              _holds
              (equiv₁ , equiv₂)
              †
   where
    equiv₁ : (((f ⊤ ∧ P ∨ f ⊥) ⇒ (f ⊤ ∧ Q ∨ f ⊥)) ⇒ f P ⇒ f Q) holds
    equiv₁ = ⇒-functor (f ⊤ ∧ P ∨ f ⊥)
                       (f P)
                       (f ⊤ ∧ Q ∨ f ⊥)
                       (f Q)
                       (⇔-swap pe (f P) (f ⊤ ∧ P ∨ f ⊥)
                                        (phoa-p f sierpinski-valued-f P open-P))
                       (⇔-swap pe (f Q) (f ⊤ ∧ Q ∨ f ⊥)
                                        (phoa-p f sierpinski-valued-f Q open-Q))

    equiv₂ : ((f P ⇒ f Q) ⇒ (f ⊤ ∧ P ∨ f ⊥) ⇒ (f ⊤ ∧ Q ∨ f ⊥)) holds
    equiv₂ = ⇒-functor (f P)
                       (f ⊤ ∧ P ∨ f ⊥)
                       (f Q)
                       (f ⊤ ∧ Q ∨ f ⊥)
                       (phoa-p f sierpinski-valued-f P open-P)
                       (phoa-p f sierpinski-valued-f Q open-Q)

    † : ((f ⊤ ∧ P ∨ f ⊥) ⇒ (f ⊤ ∧ Q ∨ f ⊥)) holds
    † and-or-P = ∥∥-rec (holds-is-prop (f ⊤ ∧ Q ∨ f ⊥))
                        (cases (λ (f-top-holds , P-holds) →
                                 ∣ inl (f-top-holds , P-gives-Q P-holds)  ∣)
                               (∣_∣ ∘ inr))
                        and-or-P



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
 Ɐ P ꞉ Ω 𝓤 ,
  Ɐ Q ꞉ Ω 𝓤 ,
   ((is-open-proposition P ∧ is-open-proposition Q)
    ⇒ is-open-proposition (P ∨ Q))

is-standard : Ω ((𝓤 ⁺) ⊔ 𝓥)
is-standard = contains-bot ∧ closed-under-binary-joins

\end{code}

[1] : https://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf
[2] : Paper haskell

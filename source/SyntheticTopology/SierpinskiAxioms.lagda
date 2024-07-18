---
title:          Axioms about the Sierpinski object
authors:        ["Martin Trucchi" , "Ayberk Tosun"]
date-started:   2024-05-28
dates-modified: [2024-06-07]
---

We write down here various axioms for the Sierpinski object, defined in [1].

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


\section{Standard topology}

We define here the axiom of being a `standard-topology`, defined on 5.9 of [2].

Note that not all "used" Sierpiński verify this (for example, see the Sierpiński
defined in [3])

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

\section{Phoa's principle}

\begin{code}

phoa’s-principle : contains-top holds → contains-bot holds → Ω (𝓤 ⁺ ⊔ 𝓥)
phoa’s-principle ct cb =
  Ɐ f ꞉ (Ωₒ → Ωₒ) ,
    (Ɐ (q , open-q) ꞉ Ωₒ , pr₁ (f (q , open-q))
      ⇔ ((pr₁ (f (⊤ , ct)) ∧ q) ∨ pr₁ (f (⊥ , cb))))

\end{code}

As proved in [1] , `phoa’s-principle` implies that all endomaps of the
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
 : (ct : contains-top holds) → (cb : contains-bot holds) →
  (phoa’s-principle ct cb ⇒
    (Ɐ f ꞉ (Ωₒ → Ωₒ) ,
      (Ɐ (p , open-p) ꞉ Ωₒ , (Ɐ (q , open-q) ꞉ Ωₒ ,
        (p ⇒ q) ⇒ (pr₁ (f (p , open-p)) ⇒ pr₁ (f (q , open-q))))))) holds

phoa’s-principle-gives-monotonous-maps
 ct cb phoa-p f (p , open-p) (q , open-q) p-gives-q =
  ⇔-transport pe
              ((((pr₁ (f (⊤ , ct))) ∧ p) ∨ (pr₁ (f (⊥ , cb))))
               ⇒ (((pr₁ (f (⊤ , ct))) ∧ q) ∨ (pr₁ (f (⊥ , cb)))))
              ((pr₁ (f (p , open-p))) ⇒ (pr₁ (f (q , open-q))))
              _holds
              (equiv₁ , equiv₂)
              †
   where
    equiv₁ : (((pr₁ (f (⊤ , ct)) ∧ p ∨ (pr₁ (f (⊥ , cb))))
             ⇒ (pr₁ (f (⊤ , ct)) ∧ q ∨ pr₁ (f (⊥ , cb))))
                ⇒ pr₁ (f (p , open-p)) ⇒ pr₁ (f (q , open-q))) holds
    equiv₁ = ⇒-functor ((pr₁ (f (⊤ , ct))) ∧ p ∨ (pr₁ (f (⊥ , cb))))
                       ((pr₁ (f (p , open-p))))
                       ((pr₁ (f (⊤ , ct))) ∧ q ∨ (pr₁ (f (⊥ , cb))))
                       ((pr₁ (f (q , open-q))))
                       (⇔-swap pe ((pr₁ (f (p , open-p))))
                               ((pr₁ (f (⊤ , ct))) ∧ p ∨ (pr₁ (f (⊥ , cb))))
                                        (phoa-p f (p , open-p)))
                       (⇔-swap pe ((pr₁ (f (q , open-q))))
                         ((pr₁ (f (⊤ , ct))) ∧ q ∨ (pr₁ (f (⊥ , cb))))
                                        (phoa-p f (q , open-q)))

    equiv₂ : (((pr₁ (f (p , open-p))) ⇒ (pr₁ (f (q , open-q))))
             ⇒ ((pr₁ (f (⊤ , ct))) ∧ p ∨ (pr₁ (f (⊥ , cb))))
             ⇒ ((pr₁ (f (⊤ , ct))) ∧ q ∨ (pr₁ (f (⊥ , cb))))) holds
    equiv₂ = ⇒-functor ((pr₁ (f (p , open-p))))
                       ((pr₁ (f (⊤ , ct))) ∧ p ∨ (pr₁ (f (⊥ , cb))))
                       ((pr₁ (f (q , open-q))))
                       ((pr₁ (f (⊤ , ct))) ∧ q ∨ (pr₁ (f (⊥ , cb))))
                       (phoa-p f (p , open-p))
                       (phoa-p f (q , open-q))

    † : (((pr₁ (f (⊤ , ct))) ∧ p ∨ (pr₁ (f (⊥ , cb))))
     ⇒ ((pr₁ (f (⊤ , ct))) ∧ q ∨ (pr₁ (f (⊥ , cb))))) holds
    † and-or-p =
     ∥∥-rec (holds-is-prop ((pr₁ (f (⊤ , ct))) ∧ q ∨ (pr₁ (f (⊥ , cb)))))
            (cases (λ (f-top-holds , p-holds) →
                                   ∣ inl (f-top-holds , p-gives-q p-holds)  ∣)
                                   (∣_∣ ∘ inr))
                        and-or-p

\end{code}

\section{References}

- [1]: Davorin Lesňik. *Synthetic Topology and Constructive Metric Spaces*.

  PhD Thesis, 2010

  https://doi.org/10.48550/arXiv.2104.10399

- [2]: Martín Escardó. *Topology via higher-order intuitionistic logic*

  Unpublished notes, Pittsburgh, 2004

  https://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf

- [3]: Martín Escardó. *Synthetic topology of data types and classical spaces*.

  ENTCS, Elsevier, volume 87, pages 21-156, November 2004.

  https://www.cs.bham.ac.uk/~mhe/papers/entcs87.pdf

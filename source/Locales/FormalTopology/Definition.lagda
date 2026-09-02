---
title: Definition of Formal Topology
author: Ayberk Tosun
date-started: 2026-07-06
date-completed: 2026-08-26
---

This module defines the notions of formal topology and quasi formal topology,
following [1] as a reference.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc

module Locales.FormalTopology.Definition
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

open import Locales.Frame pt fe hiding (⟨_⟩)
open import MLTT.Spartan
open import Notation.UnderlyingType
open import UF.Logic
open import UF.Powerset
open import UF.Sets
open import UF.SubtypeClassifier

open AllCombinators pt fe
open PropositionalSubsetInclusionNotation fe

\end{code}

\section{Quasi formal topology}

We define the notion of quasi formal topology as in Definition 2.1 of [1].

The rule that Negri calls _reflexivity_:

\begin{code}

satisfies-cover-reflexivity : {A : 𝓤 ̇ } → (A → 𝓟 A → Ω 𝓤) → Ω (𝓤 ⁺)
satisfies-cover-reflexivity {_} {A} _◁_ = Ɐ a ꞉ A , Ɐ U ꞉ 𝓟 A , a ∈ₚ U ⇒ a ◁ U

\end{code}

The rule that Negri calls _transitivity_:

\begin{code}

satisfies-cover-transitivity : {A : 𝓤 ̇ } → (A → 𝓟 A → Ω 𝓤) → Ω (𝓤 ⁺)
satisfies-cover-transitivity {_} {A} _◁_ =
 Ɐ a ꞉ A , Ɐ U ꞉ 𝓟 A , Ɐ V ꞉ 𝓟 A , a ◁ U ⇒ U ⊆ₚ (_◁ V) ⇒ a ◁ V

\end{code}

We are now ready to define the notion of _quasi formal topology_, exactly as
defined in Definition 2.1 of [1].

\begin{code}

Quasi-Formal-Topology-Structure : 𝓤 ̇ → 𝓤 ⁺ ̇
Quasi-Formal-Topology-Structure {𝓤} A =
 Σ _◁_ ꞉ (A → 𝓟 A → Ω 𝓤) ,
    is-set A
  × (satisfies-cover-reflexivity _◁_ holds)
  × (satisfies-cover-transitivity _◁_ holds)

Quasi-Formal-Topology : (𝓤 : Universe) → 𝓤 ⁺ ̇
Quasi-Formal-Topology 𝓤 = Σ A ꞉ 𝓤 ̇ , Quasi-Formal-Topology-Structure A

\end{code}

\subsection{Named projections for quasi formal topologies}

Named projections for the `Quasi-Formal-Topology` type.

\begin{code}

carrier-of-quasi-formal-topology : Quasi-Formal-Topology 𝓤 → 𝓤 ̇
carrier-of-quasi-formal-topology (A , _) = A

instance
 Underlying-Type-Quasi-Formal-Topology
  : Underlying-Type (Quasi-Formal-Topology 𝓤) (𝓤 ̇)
 Underlying-Type-Quasi-Formal-Topology =
  record { ⟨_⟩ = carrier-of-quasi-formal-topology }

carrier-of-quasi-formal-topology-is-set
 : (𝒜 : Quasi-Formal-Topology 𝓤)
 → is-set ⟨ 𝒜 ⟩
carrier-of-quasi-formal-topology-is-set {𝓤} (A , _ , σ , _) = σ

cover-of-quasi-formal-topology
 : (𝒜 : Quasi-Formal-Topology 𝓤)
 → ⟨ 𝒜 ⟩
 → 𝓟 ⟨ 𝒜 ⟩
 → Ω 𝓤
cover-of-quasi-formal-topology (_ , _◁_ , _) = _◁_

infix 5 cover-of-quasi-formal-topology
syntax cover-of-quasi-formal-topology 𝒜 a U = a ◁Q[ 𝒜 ] U

reflexivity-of-quasi-cover
 : (𝒜 : Quasi-Formal-Topology 𝓤)
 → satisfies-cover-reflexivity (λ a U → a ◁Q[ 𝒜 ] U) holds
reflexivity-of-quasi-cover (_ , _ , _ , β , _) = β

transitivity-of-quasi-cover
 : (𝒜 : Quasi-Formal-Topology 𝓤)
 → satisfies-cover-transitivity (λ a U → a ◁Q[ 𝒜 ] U) holds
transitivity-of-quasi-cover (_ , _ , _ , _ , γ) = γ

\end{code}

\subsection{Basic properties of quasi formal topologies}

We previously used the relation `U ⊆ (_◁ V)`. We now define the syntax
as an abbreviation for this `U ◁Q⁺[ 𝒜 ] V`.

\begin{code}

cover-plus-of-quasi-formal-topology
 : (𝒜 : Quasi-Formal-Topology 𝓤)
 → 𝓟 ⟨ 𝒜 ⟩
 → 𝓟 ⟨ 𝒜 ⟩
 → Ω 𝓤
cover-plus-of-quasi-formal-topology 𝒜 U V = U ⊆ₚ (λ - → - ◁Q[ 𝒜 ] V)

infix 5 cover-plus-of-quasi-formal-topology
syntax cover-plus-of-quasi-formal-topology 𝒜 U V = U ◁Q⁺[ 𝒜 ] V

transitivity-of-quasi-cover-plus
 : (𝒜 : Quasi-Formal-Topology 𝓤)
 → (Ɐ U V W ꞉ 𝓟 ⟨ 𝒜 ⟩ , U ◁Q⁺[ 𝒜 ] V ⇒ V ◁Q⁺[ 𝒜 ] W ⇒ U ◁Q⁺[ 𝒜 ] W) holds
transitivity-of-quasi-cover-plus 𝒜 U V W p q a h =
 transitivity-of-quasi-cover 𝒜 a V W † q
  where
   † : (a ◁Q[ 𝒜 ] V) holds
   † = p a h

\end{code}

The `_◁⁺_` relation is reflexive.

\begin{code}

reflexivity-of-quasi-cover-plus
 : (𝒜 : Quasi-Formal-Topology 𝓤)
 → (Ɐ U ꞉ 𝓟 ⟨ 𝒜 ⟩ , U ◁Q⁺[ 𝒜 ] U) holds
reflexivity-of-quasi-cover-plus 𝒜 U a = reflexivity-of-quasi-cover 𝒜 a U

\end{code}

Two subsets of a quasi formal topology are called _cover equivalent_ if they
cover each other. We define the syntax `U ＝[ 𝒜 ]＝ V` for this.

\begin{code}

cover-equivalence-of-quasi-formal-topology
 : (𝒜 : Quasi-Formal-Topology 𝓤)
 → 𝓟 ⟨ 𝒜 ⟩
 → 𝓟 ⟨ 𝒜 ⟩
 → Ω 𝓤
cover-equivalence-of-quasi-formal-topology 𝒜 U V =
 (U ◁Q⁺[ 𝒜 ] V) ∧ (V ◁Q⁺[ 𝒜 ] U)

infix 5 cover-equivalence-of-quasi-formal-topology
syntax cover-equivalence-of-quasi-formal-topology 𝒜 U V = U =[ 𝒜 ]= V

\end{code}

\subsection{Cover reasoning}

We define the `Quasi-Cover-Reasoning` module for writing chains of cover
transitivity in a pretty way.

\begin{code}

module Quasi-Cover-Reasoning (𝒜 : Quasi-Formal-Topology 𝓤) where

 _◁⟨_⟩_ : (a : ⟨ 𝒜 ⟩) {U V : 𝓟 ⟨ 𝒜 ⟩}
        → (a ◁Q[ 𝒜 ] U) holds
        → (U ◁Q⁺[ 𝒜 ] V) holds
        → (a ◁Q[ 𝒜 ] V) holds
 a ◁⟨ p ⟩ q = transitivity-of-quasi-cover 𝒜 a _ _ p q

 _◁⁺⟨_⟩_ : (U : 𝓟 ⟨ 𝒜 ⟩) {V W : 𝓟 ⟨ 𝒜 ⟩}
        → (U ◁Q⁺[ 𝒜 ] V) holds
        → (V ◁Q⁺[ 𝒜 ] W) holds
        → (U ◁Q⁺[ 𝒜 ] W) holds
 U ◁⁺⟨ p ⟩ q = transitivity-of-quasi-cover-plus 𝒜 U _ _ p q

 _＝⟨_⟩c_ : (U : 𝓟 ⟨ 𝒜 ⟩) {V W : 𝓟 ⟨ 𝒜 ⟩}
          → U ＝ V → (V ◁Q⁺[ 𝒜 ] W) holds → (U ◁Q⁺[ 𝒜 ] W) holds
 _ ＝⟨ p ⟩c q = transport (λ - → (- ◁Q⁺[ 𝒜 ] _) holds) (p ⁻¹) q

 _■ : (U : 𝓟 ⟨ 𝒜 ⟩) → (U ◁Q⁺[ 𝒜 ] U) holds
 _■ = reflexivity-of-quasi-cover-plus 𝒜

 infixr 0 _◁⟨_⟩_
 infixr 0 _◁⁺⟨_⟩_
 infixr 0 _＝⟨_⟩c_
 infix  1 _■

\end{code}

\section{Formal topology}

A formal topology is a quasi formal topology equipped with a partial order,
satisfying the additional axioms of _left_ and _right_. These are the last two
rules given in Definition 2.1 of [1].

We first define the condition that Negri [1] calls _left_:

\begin{code}

satisfies-cover-left-rule : {A : 𝓤 ̇} → (A → A → Ω 𝓤) → (A → 𝓟 A → Ω 𝓤) → Ω (𝓤 ⁺)
satisfies-cover-left-rule {_} {A} _⊑_ _◁_ =
 Ɐ a b ꞉ A , Ɐ U ꞉ 𝓟 A , b ⊑ a ⇒ a ◁ U ⇒ b ◁ U

\end{code}

Some notation for downward closures of sets as well as the intersection of
downward closures.

\begin{code}

module Downward-Closure-Intersection-Syntax {A : 𝓤 ̇} (_⊑_ : A → A → Ω 𝓤) where

 ↓_ : 𝓟 A → 𝓟 A
 ↓ U = λ a → Ǝₚ u ꞉ A , (u ∈ₚ U ∧ a ⊑ u)

 _⊓_ : 𝓟 A → 𝓟 A → 𝓟 A
 U ⊓ V = (↓ U) ∩ (↓ V)

 infix 6 _⊓_
 infix 7 ↓_

\end{code}

Now, we define the condition that Negri calls _right_:

\begin{code}

satisfies-cover-right-rule : {A : 𝓤 ̇}
                           → (A → A → Ω 𝓤)
                           → (A → 𝓟 A → Ω 𝓤)
                           → Ω (𝓤 ⁺)
satisfies-cover-right-rule {_} {A} _⊑_ _◁_ =
 Ɐ a ꞉ A , Ɐ U V ꞉ 𝓟 A , a ◁ U ⇒ a ◁ V ⇒ a ◁ (U ⊓ V)
  where
   open Downward-Closure-Intersection-Syntax _⊑_ using (_⊓_)

\end{code}

We are now ready to define the notion of formal topology. Unlike Negri, we also
require the order in consideration to be antisymmetric.

\begin{code}

Formal-Topology-Structure : 𝓤 ̇ → 𝓤 ⁺ ̇
Formal-Topology-Structure {𝓤} A =
 Σ _⊑_ ꞉ (A → A → Ω 𝓤) ,
  Σ _◁_ ꞉ (A → 𝓟 A → Ω 𝓤) ,
     (is-reflexive _⊑_ holds)
   × (is-transitive _⊑_ holds)
   × (is-antisymmetric _⊑_)
   × (satisfies-cover-reflexivity _◁_ holds)
   × (satisfies-cover-transitivity _◁_ holds)
   × (satisfies-cover-left-rule _⊑_ _◁_ holds)
   × (satisfies-cover-right-rule _⊑_ _◁_ holds)

Formal-Topology : (𝓤 : Universe) → 𝓤 ⁺ ̇
Formal-Topology 𝓤 = Σ A ꞉ 𝓤 ̇ , Formal-Topology-Structure A

\end{code}

\subsection{Named projections for formal topologies}

\begin{code}

carrier-of-formal-topology : Formal-Topology 𝓤 → 𝓤 ̇
carrier-of-formal-topology (A , _) = A

instance
 Underlying-Type-Formal-Topology : Underlying-Type (Formal-Topology 𝓤) (𝓤 ̇)
 Underlying-Type-Formal-Topology = record { ⟨_⟩ = carrier-of-formal-topology }

order-of-formal-topology : (𝒜 : Formal-Topology 𝓤) → ⟨ 𝒜 ⟩ → ⟨ 𝒜 ⟩ → Ω 𝓤
order-of-formal-topology (_ , _⊑_ , _) = _⊑_

infix 5 order-of-formal-topology
syntax order-of-formal-topology 𝒜 a b = a ⊑[ 𝒜 ] b

cover-of-formal-topology : (𝒜 : Formal-Topology 𝓤)
                         → ⟨ 𝒜 ⟩ → 𝓟 ⟨ 𝒜 ⟩ → Ω 𝓤
cover-of-formal-topology (_ , _ , _◁_ , _) = _◁_

infix 5 cover-of-formal-topology
syntax cover-of-formal-topology 𝒜 a U = a ◁[ 𝒜 ] U

reflexivity-of-order
 : (𝒜 : Formal-Topology 𝓤)
 → is-reflexive (order-of-formal-topology 𝒜) holds
reflexivity-of-order (_ , _ , _ , β , _) = β

transitivity-of-order
 : (𝒜 : Formal-Topology 𝓤)
 → is-transitive (order-of-formal-topology 𝒜) holds
transitivity-of-order (_ , _ , _ , _ , γ , _) = γ

antisymmetry-of-order
 : (𝒜 : Formal-Topology 𝓤)
 → is-antisymmetric (order-of-formal-topology 𝒜)
antisymmetry-of-order (_ , _ , _ , _ , _ , δ , _) = δ

cover-satisfies-left-rule
 : (𝒜 : Formal-Topology 𝓤)
 → satisfies-cover-left-rule
    (order-of-formal-topology 𝒜)
    (cover-of-formal-topology 𝒜)
     holds
cover-satisfies-left-rule (_ , _ , _ , _ , _ , _ , _ , _ , η , _) = η

cover-satisfies-right-rule
 : (𝒜 : Formal-Topology 𝓤)
 → satisfies-cover-right-rule
    (order-of-formal-topology 𝒜)
    (cover-of-formal-topology 𝒜)
     holds
cover-satisfies-right-rule (_ , _ , _ , _ , _ , _ , _ , _ , _ , θ) = θ

\end{code}

The sethood of the carrier of a formal topology follows from the fact it is
equipped with a partial order.

\begin{code}

carrier-of-formal-topology-is-set : (𝒜 : Formal-Topology 𝓤) → is-set ⟨ 𝒜 ⟩
carrier-of-formal-topology-is-set {𝓤} (A , _⊑_ , _ , β , γ , δ , _) =
 carrier-of-[ P ]-is-set
  where
   P : Poset 𝓤 𝓤
   P = A , _⊑_ , (β , γ) , δ

\end{code}

The underlying poset of a formal topology.

\begin{code}

underlying-poset-of-formal-topology : (𝒜 : Formal-Topology 𝓤) → Poset 𝓤 𝓤
underlying-poset-of-formal-topology {𝓤} (A , _⊑_ , _ , β , γ , δ , _) =
 A , _⊑_ , (β , γ) , δ

\end{code}

The underlying quasi formal topology of a formal topology.

\begin{code}

underlying-quasi-formal-topology : Formal-Topology 𝓤 → Quasi-Formal-Topology 𝓤
underlying-quasi-formal-topology 𝒜@(A , _ , _◁_ , _ , _ , _ , ρ , τ , _ , _) =
 A , _◁_ , carrier-of-formal-topology-is-set 𝒜 , ρ , τ

\end{code}

The `_◁⁺_` operation for formal topologies.

\begin{code}

cover-plus-of-formal-topology
 : (𝒜 : Formal-Topology 𝓤)
 → 𝓟 ⟨ 𝒜 ⟩
 → 𝓟 ⟨ 𝒜 ⟩
 → Ω 𝓤
cover-plus-of-formal-topology =
 cover-plus-of-quasi-formal-topology ∘ underlying-quasi-formal-topology

infix 5 cover-plus-of-formal-topology
syntax cover-plus-of-formal-topology 𝒜 U V = U ◁⁺[ 𝒜 ] V

transitivity-of-cover-plus
 : (𝒜 : Formal-Topology 𝓤)
 → (Ɐ U V W ꞉ 𝓟 ⟨ 𝒜 ⟩ , U ◁⁺[ 𝒜 ] V ⇒ V ◁⁺[ 𝒜 ] W ⇒ U ◁⁺[ 𝒜 ] W) holds
transitivity-of-cover-plus =
 transitivity-of-quasi-cover-plus ∘ underlying-quasi-formal-topology

\end{code}

[1]: Sara Negri. _Continuous domains as formal spaces_. Mathematical Structures
     in Computer Science, Volume 12, No. 1, pp. 19–52, 2002.
     DOI:10.1017/S0960129501003450

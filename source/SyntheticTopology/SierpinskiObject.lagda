---
title:          Definition of Sierpinski object synthetic topology
authors:        ["Ayberk Tosun", "Martin Trucchi"]
date-started:   2024-05-02
date-completed: 2024-05-31
dates-updated:  [2024-05-28, 2024-06-05 , 2024-06-07]
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

module SyntheticTopology.SierpinskiObject
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist) where

open import UF.Classifiers
open import UF.Embeddings
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Logic
open import UF.Subsingletons-FunExt
open import UF.Univalence
open import UF.UniverseEmbedding

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

What is a Sierpiński object? In Martín Escardó´s unpublished note [2],
a Sierpiński object is defined in the setting of a topos as a subobject of the
subobject classifier. This is also given in Definition 2.4 of Davorin Lesnik's
thesis [1], who took this unpublished note as a starting point for his PhD
thesis.

The purpose of this development is to develop these notions in the context of
HoTT/UF, where we look at subtypes of the subtype classifier. Because we work
predicatively, however, the definition of the notion of Sierpiński object is not
that straightforward in our setting.

In the impredicative setting of topos theory, one works with the topos of 𝓤-sets
over some universe 𝓤, and the Sierpiński object in that setting would translate
to:

\begin{code}

Sierpinski-Object₀ : (𝓤 : Universe) → 𝓤 ⁺  ̇
Sierpinski-Object₀ 𝓤 = Subtype' 𝓤 (Ω 𝓤)

\end{code}

However, many dominances that we are interested in do not fit this definition in
a predicative setting. For example, the largest possible dominance of `Ω 𝓤` is
𝓤⁺-set rather than a 𝓤-set. Accordingly, we generalize the universes in the
notion of Sierpiński object as follows:

\begin{code}

Generalized-Sierpinski-Object : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺  ̇
Generalized-Sierpinski-Object 𝓤 𝓥 = Ω 𝓤 → Ω 𝓥

\end{code}

We think that in most cases, our dominances will be of the form `Ω 𝓤 → Ω (𝓤 ⁺)`,
but because we can prove things in this general setting, we choose to work with
the generalized definition instead.

We define some notation to refer to components of a Sierpiński object.

In the module below, we assume the existence of a Sierpiński object `𝕊` and
define some notions _synthetically_, following the work of Martín Escardó (and
Davorin Lešnik).

\begin{code}

module Sierpinski-notations (𝕊 : Generalized-Sierpinski-Object 𝓤 𝓥) where

\end{code}

The propositions in `Ω` that fall in the subset `𝕊` are called _open
propositions_. We introduce suggestive terminology accordingly.

The type of open proposition is noted Ωₒ

\begin{code}

 is-open-proposition : Ω 𝓤 → Ω 𝓥
 is-open-proposition = 𝕊

 Ωₒ : 𝓤 ⁺ ⊔ 𝓥  ̇
 Ωₒ = Σ p ꞉ Ω 𝓤 , is-open-proposition p holds

\end{code}

Here, we only work with sets.

We defined some combinators for the sake of notational simplicity in the module
SetCombinators.

To define this and some related notions, we work in a module parameterized by an
hSet `𝒳`. We adopt the convention of using calligraphic letters `𝒳`, `𝒴`, ...
for inhabitants of the type `hSet`.

\begin{code}

 module _ (𝒳 : hSet 𝓤) where

\end{code}

We denote by `X` the underlying set of `𝒳`.

\begin{code}

  private
   X = underlying-set 𝒳

\end{code}

A subset of a set is said to be `intrinsically open` if it is a predicate
defined by open propositions.

\begin{code}

  is-intrinsically-open : 𝓟 X → Ω (𝓤 ⊔ 𝓥)
  is-intrinsically-open P = Ɐ x ꞉ X , is-open-proposition (x ∈ₚ P)

\end{code}

For convenience, we write down the subtype of open propositions (= subset) of a
set `X`

\begin{code}

  𝓞 : 𝓤 ⁺ ⊔ 𝓥  ̇
  𝓞 = Σ P ꞉ 𝓟 X , is-intrinsically-open P holds

  underlying-prop : 𝓞 → 𝓟 X
  underlying-prop = pr₁

\end{code}

We also prove the following convenient lemma.

\begin{code}

 ⇔-open
  : (p q : Ω 𝓤)
  → ((p ⇔ q) ⇒ is-open-proposition p ⇒ is-open-proposition q) holds
 ⇔-open p q = ⇔-transport pe p q (_holds ∘ is-open-proposition)

\end{code}

\section{References}

- [1]: Davorin Lesňik. *Synthetic Topology and Constructive Metric Spaces*.

  PhD Thesis, 2010

  https://doi.org/10.48550/arXiv.2104.10399

- [2]: Martín Escardó. *Topology via higher-order intuitionistic logic*

  Unpublished notes, Pittsburgh, 2004

  https://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf

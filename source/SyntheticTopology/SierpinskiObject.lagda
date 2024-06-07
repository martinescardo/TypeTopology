---
title:          Definition of Sierpinski object synthetic topology
authors:        ["Ayberk Tosun", "Martin Trucchi"]
date-started:   2024-05-02
date-completed: 2024-05-31
dates-updated:  [2024-05-28, 2024-06-05]
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
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

What is a Sierpiński object? In Martín Escardó´s unpublished note [_Topology via
higher-order intuitionistic logic_][1], a Sierpiński object is defined in the
setting of a topos as a subobject of the subobject classifier. This is also
given in Definition 2.4 of Davorin Lesnik's thesis, who took this unpublished
note as a starting point for his PhD thesis.

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

\begin{code}

 is-open-proposition : Ω 𝓤 → Ω 𝓥
 is-open-proposition = 𝕊

\end{code}

Here, we only work with sets.

We define some combinators for the sake of notational simplicity.

Note : for `imageₛ` , the fact that `(X , sX)` is a set is not useful, but
we define it this way to keep the coherence between the arguments. 

\begin{code}

 _×ₛ_ : hSet 𝓤 → hSet 𝓤 → hSet 𝓤
 _×ₛ_ (X , sX) (Y , sY) = (X × Y) , ×-is-set sX sY

 Πₛ : ((X , sX) : hSet 𝓤) → (X → hSet 𝓤) → hSet 𝓤
 Πₛ (X , sX) f = Π (underlying-set ∘ f) , Π-is-set fe (pr₂ ∘ f)

 imageₛ : ((X , sX) : hSet 𝓤) → ((Y , sY) : hSet 𝓤) → (X → Y) → hSet 𝓤 
 imageₛ (X , sX) (Y , sY) f =
  (image f , Σ-is-set sY λ y → props-are-sets ∃-is-prop)

 Ωₛ : Ω 𝓤 → hSet 𝓤
 Ωₛ p = (p holds , props-are-sets (holds-is-prop p))

\end{code}

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

  is-intrinsically-open : (X → Ω 𝓤) → Ω (𝓤 ⊔ 𝓥)
  is-intrinsically-open P = Ɐ x ꞉ X , is-open-proposition (P x)

\end{code}

For convenience, we write down the subtype of open propositions (= subset) of a
set `X`

\begin{code}

  𝓞 : 𝓤 ⁺ ⊔ 𝓥  ̇
  𝓞 = Σ P ꞉ (X → Ω 𝓤) , is-intrinsically-open P holds

  underlying-prop : 𝓞 → (X → Ω 𝓤)
  underlying-prop = pr₁

\end{code}

We also prove the following convenient lemma.

\begin{code}

 ⇔-open
  : (P Q : Ω 𝓤)
  → ((P ⇔ Q) ⇒ is-open-proposition P ⇒ is-open-proposition Q) holds
 ⇔-open P Q = ⇔-transport pe P Q (_holds ∘ is-open-proposition)

\end{code}

[1]: https://www.cs.bham.ac.uk/~mhe/papers/pittsburgh.pdf

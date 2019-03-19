---
layout: default
title : Introduction to Univalent Foundations of Mathematics with Agda
date : 2019-03-04
---
## <a name="lecturenotes">Introduction to Univalent Foundations of Mathematics with Agda</a>

<!--
\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module Inhabitation where

open import Universes
open import MLTT-Agda
open import HoTT-UF-Agda
open import FunExt
\end{code}
-->

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="truncation"></a> Subsingleton truncation

The following is Voevosky's approach to saying that a type is
inhabited in such a way that the statement of inhabitation is a
subsingleton, using funext.

\begin{code}
is-inhabited : 𝓤 ̇ → 𝓤 ⁺ ̇
is-inhabited {𝓤} X = (P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → P
\end{code}

This says that if we have a function from `X` to a subsingleton `P`, then
`P` must have a point. So this fails when `X=𝟘`. Considering `P=𝟘`, we conclude
that `¬¬ X` if `X` is inhabited, which says that `X` is non-empty. However,
in the absence of excluded middle, [inhabitation is stronger than
double negation](https://lmcs.episciences.org/3217).

For simplicity in the formulation of the theorems, we assume global
`dfunext`.

\begin{code}
global-dfunext : 𝓤ω
global-dfunext = ∀ 𝓤 𝓥 → dfunext 𝓤 𝓥

inhabitation-is-a-subsingleton : global-dfunext → (X : 𝓤 ̇ ) → is-subsingleton (is-inhabited X)
inhabitation-is-a-subsingleton {𝓤} fe X =
  Π-is-subsingleton (fe (𝓤 ⁺) 𝓤)
    λ P → Π-is-subsingleton (fe 𝓤 𝓤)
           (λ (s : is-subsingleton P)
                 → Π-is-subsingleton (fe 𝓤 𝓤) (λ (f : X → P) → s))

pointed-is-inhabited : {X : 𝓤 ̇ } → X → is-inhabited X
pointed-is-inhabited x = λ P s f → f x

inhabited-recursion : (X P : 𝓤 ̇ ) → is-subsingleton P → (X → P) → is-inhabited X → P
inhabited-recursion X P s f φ = φ P s f
\end{code}

Although we [don't necessarily have](Appendix.html#moreexercices) that
`¬¬ P → P`, we do have that `is-inhabited P → P`:

\begin{code}
inhabited-gives-pointed-for-subsingletons : (P : 𝓤 ̇ ) → is-subsingleton P → is-inhabited P → P
inhabited-gives-pointed-for-subsingletons P s = inhabited-recursion P P s id

inhabited-functorial : global-dfunext → (X : 𝓤 ⁺ ̇ ) (Y : 𝓤 ̇ )
                     → (X → Y) → is-inhabited X → is-inhabited Y
inhabited-functorial fe X Y f = inhabited-recursion
                                  X
                                  (is-inhabited Y)
                                  (inhabitation-is-a-subsingleton fe Y)
                                  (pointed-is-inhabited ∘ f)

\end{code}

This universe assignment for functoriality is fairly restrictive, but is the only possible one.

With this notion, we can define the image of a function as follows:

\begin{code}
∃ : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → (𝓤 ⊔ 𝓥)⁺ ̇
∃ {𝓤} {𝓥} {X} A = is-inhabited (Σ \(x : X) → A x)

image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
image f = Σ \(y : codomain f) → ∃ \(x : domain f) → f x ≡ y
\end{code}

*Exercise.* An attempt to define the image of `f` without the
inhabitation predicate would be to take it to be
`Σ \(y : codomain f) → Σ \(x : domain f) → f x ≡ y`. Show that this
type is equivalent to `X`. This is similar to what happens in set
theory: the graph of any function is isomorphic to its domain.


We can define the restriction and corestriction of a function to its
image as follows:

\begin{code}
restriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
            → image f → Y
restriction f (y , _) = y

corestriction : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
              → X → image f
corestriction f x = f x , pointed-is-inhabited (x , refl (f x))
\end{code}

And we can define the notion of surjection as follows:
\begin{code}
is-surjection : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → (𝓤 ⊔ 𝓥)⁺ ̇
is-surjection f = (y : codomain f) → ∃ \(x : domain f) → f x ≡ y
\end{code}

*Exercise.* The type `(y : codomain f) → Σ \(x : domain f) → f x ≡ y`
 is equivalent to the type `has-section f`, which is stronger than
 saying that `f` is a surjection.

There are two problems with this definition of inhabitation:

  * Inhabitation has values in the next universe.

  * We can eliminate into propositions of the same universe only.

In particular, it is not possible to show that the map `X →
is-inhabited X` is a surjection, or that `X → Y` gives `is-inhabited X
→ is-inhabited Y`.

There are two proposed ways to solve this:

  * Voevodsky works with certain [resizing
    rules](http://www.math.ias.edu/vladimir/files/2011_Bergen.pdf) for
    subsingletons. At the time of writing, the (relative) consistency
    of the system with such rules is an open question.

  * The HoTT book works with certain higher inductive types (HIT's).
    This is the same approach of taken by cubical Agda.

A third possibility is to work with propositional truncations
[axiomatially](https://lmcs.episciences.org/3217), which is compatible
with the above two proposals. We write this axiom as a record type
rather than as an iterated `Σ-type` for simplicity, where we use the
HoTT-book notation `∥ X ∥` for the inhabitation of `X`,
called the propositional truncation of `X`:

\begin{code}
record propositional-truncations-exist : 𝓤ω where
 field
  ∥_∥ : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  ∥∥-is-a-prop : {𝓤 : Universe} {X : 𝓤 ̇ } → is-prop ∥ X ∥
  ∣_∣ : {𝓤 : Universe} {X : 𝓤 ̇ } → X → ∥ X ∥
  ∥∥-rec : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } {P : 𝓥 ̇ } → is-prop P → (X → P) → ∥ X ∥ → P
\end{code}

This is the approach we adopt in our [personal Agda
development](http://www.cs.bham.ac.uk/~mhe/agda-new/).

*Exercise*. If `X` and `Y` are types obtained by summing `x-` and
  `y`-many copies of the type `𝟙`, respectively, as in `𝟙 + 𝟙 + ... + 𝟙` , where `x`
  and `y` are natural numbers, then `∥ X = Y ∥ = (x ≡ y)` and the type
  `X ≡ X` has `x!` elements.

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="choice"></a> The univalent axiom of choice

For the moment see [this](http://www.cs.bham.ac.uk/~mhe/agda-new/UF-Choice.html).

[<sub>Table of contents ⇑</sub>](toc.html#contents)
### <a name="sip"></a> Structure of identity principle

For the moment, see [this](http://www.cs.bham.ac.uk/~mhe/agda-new/UF-StructureIdentityPrinciple.html).

[<sub>Table of contents ⇑</sub>](toc.html#contents) [<sub>Appendix ⇓ </sub>](Appendix.html)

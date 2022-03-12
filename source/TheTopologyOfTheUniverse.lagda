

  T h e   i n t r i n s i c   t o p o l o g y   o f   a
  M a r t i n - L o f   u n i v e r s e


    Martin Escardo, University of Birmingham, UK.

    February 2012, last updated 2 May 2014 to make it way more
    conceptual and concise.

    This is a proof in intensional Martin-Lof type theory,
    extended with the propositional axiom of extensionality as a
    postulate, written in Agda notation. The K-rule or UIP axiom
    are not used, except in a few instances where they can be
    proved. The proof type-checks in Agda 2.6.1.


A b s t r a c t. We show that a Martin-Lof universe `a la Russell
is topologically indiscrete in a precise sense defined below. As a
corollary, we derive Rice's Theorem for the universe: it has no
non-trivial, decidable, extensional properties.


I n t r o d u c t i o n

This universe indiscreteness theorem may be surprising, because
types like the Cantor space of infinite binary sequences are far
from indiscrete in the sense considered here, as they have plenty
of decidable properties. The Cantor space also fails to be
discrete, because it doesn't have decidable equality, and this
fact shows up in the proof of Rice's Theorem.

We need to postulate the axiom of extensionality, but nothing else
(the univalence axiom would give a slightly sharper result). In
particular, Brouwerian continuity axioms are not postulated, even
though this is about topology in constructive mathematics.

We show that the universe U, in Agda notation, is indiscrete, in
the sense that every sequence of types converges to any desired
type. Convergence is defined using ℕ∞, the generic convergent
sequence, constructed in the module GenericConvergentSequence, but
briefly introduced below.

For the sake of motivation, let's define convergence for sequences
of elements of types first.

We say that a sequence x : ℕ → X in a type X converges to a limit
x∞ : X if one can construct a "limiting sequence" x' : ℕ∞ → X such
that

     x n = x' (under n)
      x∞ = x' ∞

where under : ℕ → ℕ∞ (standing for "underline") is the embedding
of ℕ into ℕ∞. It is easy to see that every function of any two
types now becomes automatically continuous in the sense that it
preserves limits, without considering any model or any continuity
axiom within type theory. The collection of convergent sequences
defined above constitutes the intrinsic topology of the type X.

This is motivated as follows. There is an interpretation of type
theory (Johnstone's topological topos) in which types are spaces
and all functions are continuous. In this interpretation, ℕ is the
discrete space of natural numbers and the space ℕ∞ is the
one-point compactification of ℕ. Moreover, in this interpretation,
convergence defined in the above sense coincides with topological
convergence.

Using a general construction by Streicher, assuming a Grothendieck
universe in set theory, one can build a space in the topological
topos that is the interpretation of the universe.  Voevodsky asked
what the topology of this interpretation of the Martin-Lof
universe is. The answer is that its topological reflection is indiscrete:

  http://www.cs.bham.ac.uk/~mhe/papers/universe-indiscrete.pdf
  http://www.sciencedirect.com/science/article/pii/S0168007216300409

  M.H. Escardo and T. Streicher. The intrinsic topology of Martin-Lof
  universes. Version of Feb 2016. In Annals of Pure and Applied Logic,
  Volume 167, Issue 9, September 2016, Pages 794-805.

A space is indiscrete if the only open sets are the empty set and
the whole space. It is an easy exercise, if one knows basic
topology, to show that this is equivalent to saying that every
sequence converges to any point.

The appropriate notion of equality for elements of the universe
U of types is isomorphism. Hence we reformulate the above
definition for limits of sequences of types as follows.

We say that a sequence of types X : ℕ → U converges to a limit
X∞ : U if one can find a "limiting sequence" X' : ℕ∞ → U such
that

     X n ≅ X' (under n)
      X∞ ≅ X' ∞

If one assumes the univalence axiom, one can replace the
isomorphisms by equalities to get an equivalent notion. But notice
that in the topological topos isomorphism is not the same thing as
equality.

In this Agda module we show that every sequence of types converges
to any type whatsoever. This explains, in particular, why there
can't be non-trivial extensional functions U → ₂, where ₂ is the
discrete type of binary numbers. Such functions are the
(continuous characteristic functions of) clopen sets of the
universe, and indiscreteness shows that there can be only two of
them, so to speak. This is Rice's Theorem for the universe U.

(NB. The auxiliary modules develop much more material than we need
(and many silly things on the way - apologies).)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-FunExt

module TheTopologyOfTheUniverse (fe : FunExt) where

open import SpartanMLTT
open import UF-Equiv
open import GenericConvergentSequence
open import InjectiveTypes fe
open import CanonicalMapNotation

\end{code}


The current proof was added 28 December 2017, after adding the map
under𝟙 : ℕ + 1 → ℕ∞, and all the lemmas required for showing it is an
embedding. The original proofs were more convoluted, but the proof
here retains the original ideas moved to the universe injectivity
theorems and the fact that under𝟙 is an embedding (and the various
lemmas needed to establish that).

\begin{code}

Universe-Indiscreteness-Theorem : (X : ℕ → 𝓤 ̇ ) (X∞ : 𝓤 ̇ )

  → Σ Y ꞉ (ℕ∞ → 𝓤 ̇ ), ((i : ℕ) → Y (ι i) ≃ X i)  ×  (Y ∞ ≃ X∞)

Universe-Indiscreteness-Theorem {𝓤} X X∞ = Y , (λ i → a (inl i)) , (a (inr ⋆))
 where
  X' : ℕ + 𝟙 → 𝓤 ̇
  X' = cases X (λ _ → X∞)

  Y : ℕ∞ → 𝓤 ̇
  Y = X' / ι𝟙

  a : (z : ℕ + 𝟙) → Y (ι𝟙 z) ≃ X' z
  a z = Π-extension-property X' ι𝟙 (ι𝟙-is-embedding (fe 𝓤₀ 𝓤₀)) z

\end{code}

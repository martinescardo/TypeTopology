Martin Escardo, started 2014.

An unformalized version of part of this development was published in
Mathematical Structures in Computer Science, Cambridge University
Press, 5th January 2021. https://doi.org/10.1017/S0960129520000225

See the file InjectiveTypes.Article for an explanation of the role of
the file InjectiveTypes.Blackboard, and, more importantly, for an
explanation of the published paper.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module InjectiveTypes.index where

import InjectiveTypes.Article
import InjectiveTypes.Blackboard
\end{code}

The following have been done after the above article was published.

\begin{code}

import InjectiveTypes.CounterExamples
import InjectiveTypes.InhabitedTypesTaboo

\end{code}

Injectivity plays a major role in the construction of "searchable" or
"compact" types:

\begin{code}

import TypeTopology.index
import Ordinals.index

\end{code}

The following has applications to (in)decomposability.  Injective
types have non-trivial decidable properties if and only if weak
excluded middle (the decidability of all negative propositions) holds.

\begin{code}

import InjectiveTypes.OverSmallMaps
import Taboos.Decomposability

\end{code}

Since the above publication, a number of new examples of injective
types have been found, including the following:

 * The type of ordinals.
 * The type of iterative multisets.
 * The type of iterative sets.
 * The type of pointed types.
 * The type of ∞-magmas.
 * The type of pointed ∞-magmas.
 * The type of monoids.

(And the type of iterative ordinals is injective, simply because it is
equivalent to that of ordinals.)

\begin{code}

import Ordinals.Injectivity
import Iterative.Multisets-Addendum
import Iterative.Sets-Addendum
import Iterative.Ordinals
import InjectiveTypes.MathematicalStructures
import InjectiveTypes.Sigma
import InjectiveTypes.MathematicalStructuresMoreGeneral

\end{code}

With Tom de Jong we prove more things about resizing, and in
particular we show that previous results about injectivity are tight
with respect to the universe levels, and that no small type with two
distinct points can be injective without Ω¬¬-resizing.

\begin{code}

open import InjectiveTypes.Resizing

\end{code}

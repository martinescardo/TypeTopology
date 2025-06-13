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

The following gives equivalent formulations of algebraic injective and
flabby structure.

\begin{code}

import InjectiveTypes.Repackaging

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

The following has an application to (in)decomposability.  Injective
types have non-trivial decidable properties if and only if weak
excluded middle (the decidability of all negative propositions) holds.

It also has an application to get a characterization of the
algebraically injective types as the restracts of the algebras of the
lifting monad (also known as the partial-map classifier monad).

\begin{code}

import InjectiveTypes.OverSmallMaps
import Taboos.Decomposability
import InjectiveTypes.CharacterizationViaLifting

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
import InjectiveTypes.PointedDcpos
import InjectiveTypes.Subtypes

\end{code}

With Tom de Jong we prove more things about resizing, and in
particular we show that previous results about injectivity are tight
with respect to the universe levels, and that no small type with two
distinct points can be injective without Ω¬¬-resizing.

\begin{code}

import InjectiveTypes.Resizing

\end{code}

We explore a factorization system of embeddings and fiberwise algebraically
injective maps in the following file.

\begin{code}

import InjectiveTypes.WeakFactorizationSystem

\end{code}

And Martin Escardo explores a closer relation between algebraic
injectivity and algebras of the partial-map classifier (aka lifting)
monad in these two files.

\begin{code}

import InjectiveTypes.Algebra
import gist.InjectivesVersusAlgebras

\end{code}

Eventually the second file will be deleted after it is moved to the
first, in a suitable form.

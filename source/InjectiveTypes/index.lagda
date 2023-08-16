Martin Escardo, started 2014.

An unformalized version of part of this development was published in
Mathematical Structures in Computer Science, Cambridge University
Press, 5th January 2021.  https://doi.org/10.1017/S0960129520000225

See the file `Article` for an explanation of the role of the file
`Blackboard`, and, more importantly, for an explanation of published
paper.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module InjectiveTypes.index where

import InjectiveTypes.Article
import InjectiveTypes.Blackboard

\end{code}

The following have been done after the above article was published.

\begin{code}

import InjectiveTypes.OverSmallMaps
import InjectiveTypes.MathematicalStructures

\end{code}

Since the above publication, a number of new results involving
injectivity have been found.

Here are some examples:

 * The type of ordinals is injective.
 * The type of iterative multisets is injective.
 * The type of iterative sets is injective.

(And the type of iterative ordinals is injective, simply because it is
equivalent to that of ordinals.)

\begin{code}

import Ordinals.Injectivity
import Iterative.Multisets-Addendum
import Iterative.Sets-Addendum
import Iterative.Ordinals

\end{code}

Injective types have non-trivial decidable properties if and only if
weak excluded middle (the decidability of all negative propositions)
holds.

\begin{code}

import Taboos.Decomposability

\end{code}

Injectivity plays a major role in the construction of "searchable" or
"compact" types.

\begin{code}

import TypeTopology.index
import Ordinals.index

\end{code}

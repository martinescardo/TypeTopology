
   Various new theorems in
   constructive univalent mathematics
   written in Agda

   Tested with Agda 2.6.2.2 and the release candidate 2 of Agda 2.6.3

   Martin Escardo and collaborators, 2010--2022--∞
   Continuously evolving.

   https://github.com/martinescardo/TypeTopology

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

import index -- of safe modules
import Unsafe.index
import Redirection.index

\end{code}

There are only three, peripheral, unsafe modules. One of them is to get
a contradiction from type-in-type. The other two assume
(meta-theoretically) the Brouwerian axiom "all functions are
continuous" to prove a countable Tychonoff theorem and a form of the
compactness of the Cantor type/space.

Most modules rely on concepts and ingredients from univalent
mathematics. However, instead of postulating these non-existing
ingredients, we take them as assumptions (for single
definitions/construction/theorems/proofs or for whole modules via
module parameters). These ingredients do exist in the new cubical
Agda.


   Various new theorems in
   constructive univalent mathematics
   written in Agda

   Tested with Agda 2.6.3

   Martin Escardo and collaborators, 2010--2023--∞
   Continuously evolving.

   https://github.com/martinescardo/TypeTopology

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

import index              -- Of safe modules.
import Unsafe.index
import Redirection.index
import Pigeon.index       -- Uses non-termination check for bar recursion.

\end{code}

There are only four, peripheral, unsafe modules. One of them is to get
a contradiction from type-in-type. The other two assume
(meta-theoretically) the Brouwerian axiom "all functions are
continuous" to prove a countable Tychonoff theorem and a form of the
compactness of the Cantor type/space. The last one interfaces with
Haskell to be able to compile Agda files which print.

Most modules rely on concepts and ingredients from univalent
mathematics. However, instead of postulating these non-existing
ingredients, we take them as assumptions (for single
definitions/construction/theorems/proofs or for whole modules via
module parameters). These ingredients do exist in the new cubical
Agda.

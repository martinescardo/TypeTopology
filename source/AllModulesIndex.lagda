
   Various new theorems in
   constructive univalent mathematics
   written in Agda

   Tested with Agda 2.6.2.1.

   Martin Escardo, 2010--2022--∞
   Continuously evolving.

   https://github.com/martinescardo/TypeTopology

   A module dependency graph (updated manually from time to time) is
   available at https://www.cs.bham.ac.uk/~mhe/TypeTopology/dependency-graph.pdf

   Check our lecture notes (https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/)
   if you want to learn HoTT/UF and Agda:

   Click at the imported module names to navigate to them:

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

import index
import UnsafeModulesIndex

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
Agda, and we intend to eventually port this development to cubical
Agda. The only obstacle at the moment is that there is no pattern
matching on refl at present in cubical Agda, and hence we would need
to rewrite large portions of the code here to use J rather than
pattern matching on refl.

Martin Escardo, January 2020.

The Cantor-Schröder-Berntein Theorem, under the assumption of excluded
middle, generalized from sets to (homotopy) types. The result holds in
any boolean ∞-topos.

This says that if there is an embedding of a type X to a type Y, and
also from Y to X, then the types X and Y are equivalent.

The file CSB led to the publication

 [1] M. H. Escardo. The Cantor–Schröder–Bernstein Theorem for
     ∞-groupoids. Journal of Homotopy and Related Structures.
     June 2021, https://doi.org/10.1007/s40062-021-00284-6

After that, in 2025, Fredrik Bakke added the last two files, with a
version of CSB that

 1. weakens the assumption of excluded middle to WLPO, and
 2. on the other hand, requires stronger assumptions on the two embeddings.

Notice that (2) is absolutely necessary, in the presence of (1),
because Pradic and Brouwn previously showed that CSB for (even just
sets) implies excluded middle

 [2] Cécilia Pradic, Chad E. Brown. Cantor-Bernstein implies Excluded
     Middle. 2019, with later updates, https://arxiv.org/abs/1904.09193

\begin{code}

{-# OPTIONS --safe --without-K #-}

module CantorSchroederBernstein.index where

import CantorSchroederBernstein.CSB
import CantorSchroederBernstein.CSB-TheoryLabLunch
import CantorSchroederBernstein.CSB-WLPO
import CantorSchroederBernstein.PerfectImages

\end{code}

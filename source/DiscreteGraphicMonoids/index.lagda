Martin Escardo and Paulo Oliva, April 2024

Following Lawvere [1], we show that lists without repetitions over a
discrete type form the free discrete graphic monoid, where a monoid is
called graphic if it satisfies the identity xyx=xy.

From this we conclude, in a standard way, that lists without
repetitions form a monad.

We thank Jonas Frey for giving us this reference:

[1] F. William Lawvere. Display of graphs and their applications, as
    exemplified by 2-categories and the Hegelian "taco". Proceedings
    of the first international conference on algebraic methodology and
    software technology University of Iowa, May 22-24 1989, Iowa City,
    pp. 51-74.
    https://github.com/mattearnshaw/lawvere/blob/master/pdfs/1989-display-of-graphics-and-their-applications-exemplifed-by-2-categories-and-the-hegelian-taco.pdf

\begin{code}

{-# OPTIONS --safe --without-K #-}

module DiscreteGraphicMonoids.index where

import DiscreteGraphicMonoids.Type
import DiscreteGraphicMonoids.ListsWithoutRepetitions
import DiscreteGraphicMonoids.LWRDGM
import DiscreteGraphicMonoids.Free
import DiscreteGraphicMonoids.Monad
import DiscreteGraphicMonoids.AffineMonad
import DiscreteGraphicMonoids.ListsWithoutRepetitionsMore

\end{code}

1. The module Type defines the type of discrete graphic monoids.

2. The module ListsWithoutRepetitions investigates lists without
   repetitions over discrete types.

3. The module LWRDGM shows that lists without repetitions over a
   discrete type form a discrete graphic monoid.

4. The module Free shows that lists without repetitions over a discrete
   type form the free discrete graphic monoid.

5. The module Monad uses this, in a standard way, to show that lists
   without repetitions form a monad. (TODO. The algebras of the monad
   are, up to equivalence, the graphic monoids, again in a standard
   way.)

6. The module AffineMonad shows that non-empty lists without
   repetitions form an affine submonad of the above.

7. The module ListsWithoutRepetitionsMore includes additional facts
   about lists without repetitions that are not needed for our main
   results.

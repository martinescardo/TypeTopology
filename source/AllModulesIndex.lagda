   TypeTopology

   Various new theorems in
   constructive univalent mathematics
   written in Agda

   Martin Escardo and collaborators, 2010--2025--∞
   Continuously evolving.

   https://www.cs.bham.ac.uk/~mhe/TypeTopology/
   https://github.com/martinescardo/TypeTopology/

   Tested with Agda 2.7.0.1. (It may still work with Agda 2.6.4.3.)

\begin{code}

{-# OPTIONS --without-K --type-in-type --no-level-universe --no-termination-check --guardedness #-}

import index                                -- (1)
import GamesExperimental.index              -- (2)
import RelativeMonadOnStructuredTypes.index -- (2)
import Unsafe.index                         -- (3)
import InfinitePigeon.index                 -- (4)

\end{code}

(1) Of --safe modules using --level-universe.
(2) With --safe but --no-level-universe.
(3) Of unsafe modules.
(4) Disables termination check for bar recursion.

See the module index for an explanation of the philosophy of TypeTopology.

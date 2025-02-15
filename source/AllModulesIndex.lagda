   TypeTopology

   Various new theorems in
   constructive univalent mathematics
   written in Agda

   Tested with Agda 2.7.0.1. (It may still work with Agda 2.6.4.3.)

   Martin Escardo and collaborators, 2010--2025--∞
   Continuously evolving.

   https://www.cs.bham.ac.uk/~mhe/TypeTopology/
   https://github.com/martinescardo/TypeTopology/

\begin{code}

{-# OPTIONS --without-K --type-in-type --no-level-universe --no-termination-check --guardedness #-}

import index                    -- Of --safe modules using --level-universe.
import GamesExperimental.index  -- With --safe but --no-level-universe.
import Unsafe.index             -- Of unsafe modules.
import InfinitePigeon.index     -- Disables termination check for bar recursion.

\end{code}

See the module index for an explanation of the philosophy of TypeTopology.

   TypeTopology

   Various new theorems in
   constructive univalent mathematics
   written in Agda

   Tested with Agda 2.6.4.3 and 2.7.0

   Martin Escardo and collaborators, 2010--2024--∞
   Continuously evolving.

   https://github.com/martinescardo/TypeTopology

\begin{code}

{-# OPTIONS --without-K --type-in-type --no-level-universe --no-termination-check #-}

import index                    -- Of --safe modules using --level-universe.
import GamesExperimental.index  -- With --safe but --no-level-universe.
import Unsafe.index             -- Of unsafe modules.
import InfinitePigeon.index     -- Disables termination check for bar recursion.

\end{code}

See the module index for an explanation of the philosophy of TypeTopology.

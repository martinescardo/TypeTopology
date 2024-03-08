   TypeTopology

   Various new theorems in
   constructive univalent mathematics
   written in Agda

   Tested with Agda 2.6.4.1

   Martin Escardo and collaborators, 2010--2024--∞
   Continuously evolving.

   https://githubn.com/martinescardo/TypeTopology

\begin{code}

{-# OPTIONS --without-K --no-level-universe #-}

import index                    -- Of --safe modules using --level-universe.
import GamesExperimental.index  -- With --safe but --no-level-universe.
import Unsafe.index             -- Of unsafe modules.
import InfinitePigeon.index     -- Disables termination check for bar recursion.

\end{code}

See the module index for an explanation of the philosophy of TypeTopology.

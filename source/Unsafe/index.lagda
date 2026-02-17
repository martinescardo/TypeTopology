\begin{code}

{-# OPTIONS --without-K --type-in-type --no-termination-check --guardedness #-}

module Unsafe.index where

import Unsafe.CantorCompact      -- uses CountableTychonoff
import Unsafe.CoNat-Equiv        -- uses Coinductive records
import Unsafe.CountableTychonoff -- uses TERMINATING
import Unsafe.Type-in-Type-False -- uses --type-in-type
import Unsafe.Haskell            -- uses Haskell features as postulates
import Games.Main                -- uses Haskell features as postulates

\end{code}

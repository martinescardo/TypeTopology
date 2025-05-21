Martin Escardo and Paulo Oliva, 2-27 July 2021,

Same as MonadOnTypes but with more general universes (MGU), and also
using the flag --no-level-universe.

\begin{code}

{-# OPTIONS --safe --without-K --no-level-universe #-}

module MonadOnTypesMGU.index where

import MonadOnTypesMGU.J                       -- Selection monad.
import MonadOnTypesMGU.K                       -- Continuation (or quantifier) monad.
import MonadOnTypesMGU.JK                      -- Relationship between the two mondas.
import MonadOnTypesMGU.Monad                   -- (Automatically strong, wild) monads on suitable types.
import MonadOnTypesMGU.Reader
import MonadOnTypesMGU.NonEmptyList

\end{code}

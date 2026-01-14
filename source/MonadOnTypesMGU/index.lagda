Martin Escardo and Paulo Oliva, originally 2-27 July 2021, with the
generalization performed in March 2024.

Same as MonadOnTypes but with more general universes (MGU), and also
using the flag no-level-universe, so that we can have a type X in a
universe 𝓤 with T X in a universe ℓ 𝓤. For example, for the list
monad, we have ℓ 𝓤 = 𝓤, but for the powerset monad we have ℓ 𝓤 = 𝓤⁺.

\begin{code}

{-# OPTIONS --safe --without-K --no-level-universe #-}

module MonadOnTypesMGU.index where

import MonadOnTypesMGU.J             -- Selection monad.
import MonadOnTypesMGU.J-transf      -- Selection monad.
import MonadOnTypesMGU.K             -- Continuation (or quantifier) monad.
import MonadOnTypesMGU.JK            -- Relationship between the two mondas.
import MonadOnTypesMGU.Monad         -- (Automatically strong, wild) monads on suitable types.
import MonadOnTypesMGU.Reader
import MonadOnTypesMGU.NonEmptyList

\end{code}

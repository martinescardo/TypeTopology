Martin Escardo and Paulo Oliva, originally 2-27 July 2021, with the
generalization performed in March 2024.

Same as MonadOnTypes but with more general universes (MGU), so that we
can have a type X in a universe 𝓤 with T X in a universe ℓ 𝓤. For
example, for the list monad, we have ℓ 𝓤 = 𝓤, but for the powerset
monad we have ℓ 𝓤 = 𝓤⁺.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MonadOnTypesMGU.index where

import MonadOnTypesMGU.J                  -- Selection monad.
import MonadOnTypesMGU.J-transf           -- A selection monad transformer.
import MonadOnTypesMGU.J-transf-variation -- Selection monad transformer
import MonadOnTypesMGU.K                  -- Continuation (or quantifier) monad.
import MonadOnTypesMGU.JK                 -- Relationship between the two monads.
import MonadOnTypesMGU.Monad              -- (Automatically strong, wild) monads on types.
import MonadOnTypesMGU.Reader
import MonadOnTypesMGU.NonEmptyList

\end{code}

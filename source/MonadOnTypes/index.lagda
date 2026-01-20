Martin Escardo and Paulo Oliva, originally 2-27 July 2021, with the
generalization performed in March 2024.

Same as MonadOnTypes but with more general universes (MGU), so that we
can have a type X in a universe 𝓤 with T X in a universe ℓ 𝓤. For
example, for the list monad, we have ℓ 𝓤 = 𝓤, but for the powerset
monad we have ℓ 𝓤 = 𝓤⁺.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MonadOnTypes.index where

import MonadOnTypes.J                  -- Selection monad.
import MonadOnTypes.J-transf           -- A selection monad transformer.
import MonadOnTypes.J-transf-variation -- Selection monad transformer
import MonadOnTypes.K                  -- Continuation (or quantifier) monad.
import MonadOnTypes.JK                 -- Relationship between the two monads.
import MonadOnTypes.List
import MonadOnTypes.Construction       -- (Automatically strong, wild) monads on types.
import MonadOnTypes.Reader
import MonadOnTypes.NonEmptyList

\end{code}

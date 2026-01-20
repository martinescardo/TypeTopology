Martin Escardo and Paulo Oliva, 2023-2024


\begin{code}

{-# OPTIONS --safe --without-K #-}

module MonadOnTypes.index where

import MonadOnTypes.J                       -- Selection monad.
import MonadOnTypes.J-transf                -- A selection monad transformer.
import MonadOnTypes.J-transf-variation      -- Another selection monad transformer.
import MonadOnTypes.K                       -- Continuation (or quantifier) monad.
import MonadOnTypes.JK                      -- Relationship between the two monads.
import MonadOnTypes.Construction            -- (Automatically strong, wild) monads on types.
import MonadOnTypes.Reader                  -- Reader monad.
import MonadOnTypes.List                    -- List monad.
import MonadOnTypes.NonEmptyList            -- Non-empty list monad.
import MonadOnTypes.NonEmptyListOriginal    -- Non-empty list monad, original version.

\end{code}

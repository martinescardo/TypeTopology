Martin Escardo and Paulo Oliva, 2023-2024


\begin{code}

{-# OPTIONS --safe --without-K #-}

module MonadOnTypesLSU.index where

import MonadOnTypesLSU.J                       -- Selection monad.
import MonadOnTypesLSU.J-transf                -- A selection monad transformer.
import MonadOnTypesLSU.J-transf-variation      -- Another selection monad transformer.
import MonadOnTypesLSU.K                       -- Continuation (or quantifier) monad.
import MonadOnTypesLSU.JK                      -- Relationship between the two monads.
import MonadOnTypesLSU.Construction            -- (Automatically strong, wild) monads on types.
import MonadOnTypesLSU.Reader                  -- Reader monad.
import MonadOnTypesLSU.List                    -- List monad.
import MonadOnTypesLSU.NonEmptyList            -- Non-empty list monad.
import MonadOnTypesLSU.NonEmptyListOriginal    -- Non-empty list monad, original version.

\end{code}

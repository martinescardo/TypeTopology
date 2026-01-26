Martin Escardo and Paulo Oliva, originally 2-27 July 2021, with
generalizations and additions 2024-2026.

(Wild) monads on types, with a parameter ℓ : Universe → Universe, so that we
can have a type X in a universe 𝓤 with T X in a universe ℓ 𝓤. For
example, for the list monad, we have ℓ 𝓤 = 𝓤, but for the powerset
monad we have ℓ 𝓤 = 𝓤⁺.

They are wild because we don't consider coherence conditions in the
sense of HoTT/UF or higher category theory.

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

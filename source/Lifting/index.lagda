Martin Escardo, 2018-2019 with later additions.

The lifting (aka partial-map classifier) monad.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Lifting.index where

import Lifting.Algebras
import Lifting.Construction
import Lifting.EmbeddingDirectly
import Lifting.EmbeddingViaSIP
import Lifting.Identity
import Lifting.IdentityViaSIP
import Lifting.Miscelanea                               -- By Tom de Jong 2019
import Lifting.Miscelanea-PropExt-FunExt                -- By Tom de Jong 2019
import Lifting.Monad
import Lifting.MonadVariation
import Lifting.Set
import Lifting.Size
import Lifting.UnivalentWildCategory
import Lifting.TwoAlgebrasOnOmega
import Lifting.AnAlgebraWhichIsNotAlwaysFree
import Lifting.AnAlgebraWhichIsNotAlwaysFree-blackboard -- (*)
import Lifting.PowersOfOmegaAreFreeAlgebras
import Lifting.ProductsOfFreeAlgebrasAreFree

\end{code}

(*) This file is almost superseded by
    Lifting.AnAlgebraWhichIsNotAlwaysFree, which has a stronger result
    with a simpler proof. It is still interesting because (1) it has
    additional information, and (2) it illustrates how we use
    TypeTopology as a blackboard to think about mathematical ideas and
    develop them.

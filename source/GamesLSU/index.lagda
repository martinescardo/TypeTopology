Martin Escardo and Paulo Oliva, 2-27 July 2021, with more additions later.

Refactored and slightly improved October 2022, and then again in April
2023 with many additions.


In this folder we work in the first universe 𝓤₀, also called type. In the folder GamesMGU, we work with more general universes. However, this folder should be kept, because we have published papers that work with the less general universe assignment and point to this folder. Going forward, however, we should only work in GamesMGU, and the folder Games should be frozen, except for minor corrections of typos etc., or clarification.

TODO. Maybe the following can be deleted, as they haven't been submitted for publication yet:

 * GamesLSU.alpha-beta
 * GamesLSU.FiniteHistoryDependentMonadic

But this new file

 * GamesLSU.OptimalPlays

doesn't yet have the generalized universes, and maybe we should generalize them and move the file to GamesMGU.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module GamesLSU.index where

import GamesLSU.Alternative             -- Alternative definition of games.
import GamesLSU.Constructor             -- For simplifying the construction of games.
import GamesLSU.Examples                -- Miscelaneous small examples.
import GamesLSU.FiniteHistoryDependent  -- Theory of finite history dependent games.
import GamesLSU.FiniteHistoryDependentMonadic
                                        -- With additional monad for irrational players.
import GamesLSU.TicTacToe0
import GamesLSU.TicTacToe1              -- Like TicTacToe0 but using GamesLSU.Constructor.
import GamesLSU.TicTacToe2              -- More efficient and less elegant version.
import GamesLSU.TypeTrees               -- Dependent type trees.
import GamesLSU.alpha-beta              -- Many new things for efficiency.
import GamesLSU.Discussion
import GamesLSU.OptimalPlays            -- Computes the list of all optimal plays of a game.

-- import GamesLSU.Main                 -- To be able to compile for efficieny.
                                        -- Can't be imported here as it's not --safe.
                                        -- This is for Agda compilation to Haskell of
                                        -- examples to be able to run them more efficiently.

\end{code}

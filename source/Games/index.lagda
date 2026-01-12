Martin Escardo and Paulo Oliva, 2-27 July 2021, with more additions later.

Refactored and slightly improved October 2022, and then again in April
2023 with many additions.


In this folder we work in the first universe 𝓤₀, also called type. In the folder GamesMGU, we work with more general universes. However, this folder should be kept, because we have published papers that work with the less general universe assignment and point to this folder. Going forward, however, we should only work in GamesMGU, and the folder Games should be frozen, except for minor corrections of typos etc., or clarification.

TODO. Maybe the following can be deleted, as they haven't been submitted for publication yet:

 * Games.alpha-beta
 * Games.FiniteHistoryDependentMonadic

But this new file

 * Games.OptimalPlays

doesn't yet have the generalized universes, and maybe we should generalize them and move the file to GamesMGU.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Games.index where

import Games.Alternative             -- Alternative definition of games.
import Games.Constructor             -- For simplifying the construction of games.
import Games.Examples                -- Miscelaneous small examples.
import Games.FiniteHistoryDependent  -- Theory of finite history dependent games.
import Games.FiniteHistoryDependentMonadic
                                     -- With additional monad for irrational players.
import Games.TicTacToe0
import Games.TicTacToe1              -- Like TicTacToe0 but using Games.Constructor.
import Games.TicTacToe2              -- More efficient and less elegant version.
import Games.TypeTrees               -- Dependent type trees.
import Games.alpha-beta              -- Many new things for efficiency.
import Games.Discussion
import Games.OptimalPlays            -- Computes the list of all optimal plays of a game.

-- import Games.Main                 -- To be able to compile for efficieny.
                                     -- Can't be imported here as it's not --safe.
                                     -- This is for Agda compilation to Haskell of
                                     -- examples to be able to run them more efficiently.

\end{code}

Martin Escardo, Paulo Oliva, March - April 2023

This file is mostly for efficiency. See the tests with tic-tac-toe at
the end of this file with the various possibilities offered here.

We incorporate alpha-beta pruning to our previous work on finite
history-dependent games using the selection and continuous monads (in
the module GamesExperimental.FiniteHistoryDependent). But we do much more than
just that.

We define a minimax game (R , Xt, q , ϕt) to be a two-player game with
alternating quantifiers min and max (or max and min).

Part 0 (module minimax). In order to make the calculation of the
optimal outcome more efficient, we assume that the types of moves in
the game tree Xt are listed. Moreover, we add alpha-beta pruned
selection functions (indicated by the symbol "†").

Part 1. We transform such a minimax game G into a game G' so that we
can read off optimal *plays* of G from optimal *outcomes* of G'. This
requires the construction of a new R' and new quantifiers max' and
min', and a proof that optimal outcomes of G' give optimal plays of G.

Part 2. We then add α-β-pruning to G', to get a game G⋆, by further
modifying min' and max' to get min⋆ and max⋆, but keeping R' the
same. This requires a proof that G' and G⋆ have the same optimal
outcome. Of course, the α-β-pruning is done for the sake of
efficiency. By combining this with Part 1, we obtain an efficient way
to play the original game G optimally, with a proof of
correctness. (But we don't prove efficiency theorems.)

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

open import MLTT.Spartan hiding (J)

\end{code}

Part 0.

We now define standard minimax games.

\begin{code}

module GamesMGU.alpha-beta-examples where

open import MLTT.Athenian
open import MLTT.Fin
open import Naturals.Order
open import UF.FunExt

\end{code}

Example from Wikipedia:
https://en.wikipedia.org/wiki/Alpha%E2%80%93beta_pruning

\begin{code}

module example-from-wikipedia where

 open import GamesMGU.alpha-beta {𝓤₀} {𝓤₀} ℕ _<ℕ_ <-decidable public

 wikipedia-tree : 𝑻
 wikipedia-tree =
  Fin 3 ∷
   λ _ → Fin 2 ∷
          λ _ → Fin 2 ∷
                 λ _ → Fin 3 ∷
                        λ _ → []


 wikipedia-tree-is-listed⁺ : structure listed⁺ wikipedia-tree
 wikipedia-tree-is-listed⁺ =
  Fin-listed⁺ 2 ,
   λ _ → Fin-listed⁺ 1 ,
          λ _ → Fin-listed⁺ 1 ,
                 λ _ → Fin-listed⁺ 2 ,
                        λ _ → ⟨⟩

 wikipedia-q : Path wikipedia-tree → ℕ
 wikipedia-q (𝟎 , 𝟎 , 𝟎 , 𝟎 , ⟨⟩) = 5
 wikipedia-q (𝟎 , 𝟎 , 𝟎 , _ , ⟨⟩) = 6
 wikipedia-q (𝟎 , 𝟎 , 𝟏 , 𝟎 , ⟨⟩) = 7
 wikipedia-q (𝟎 , 𝟎 , 𝟏 , 𝟏 , ⟨⟩) = 4
 wikipedia-q (𝟎 , 𝟎 , 𝟏 , 𝟐 , ⟨⟩) = 5
 wikipedia-q (𝟎 , 𝟏 , _ , _ , ⟨⟩) = 3
 wikipedia-q (𝟏 , 𝟎 , 𝟎 , _ , ⟨⟩) = 6
 wikipedia-q (𝟏 , 𝟎 , 𝟏 , 𝟎 , ⟨⟩) = 6
 wikipedia-q (𝟏 , 𝟎 , 𝟏 , _ , ⟨⟩) = 9
 wikipedia-q (𝟏 , 𝟏 , _ , _ , ⟨⟩) = 7
 wikipedia-q (𝟐 , 𝟎 , _ , _ , ⟨⟩) = 5
 wikipedia-q (𝟐 , _ , _ , _ , ⟨⟩) = 9

 module _ where

  open minimax

  wikipedia-G : Game ℕ
  wikipedia-G = G wikipedia-tree wikipedia-tree-is-listed⁺ wikipedia-q

  wikipedia-optimal-play : Path wikipedia-tree
  wikipedia-optimal-play = optimal-play wikipedia-tree wikipedia-tree-is-listed⁺ wikipedia-q

 wikipedia-optimal-outcome : ℕ
 wikipedia-optimal-outcome = optimal-outcome ℕ wikipedia-G

 wikipedia-optimal-outcome＝ : wikipedia-optimal-outcome ＝ 6
 wikipedia-optimal-outcome＝ = refl

 {- Comment out because it is slow:

 wikipedia-optimal-play＝ : wikipedia-optimal-play ＝ (𝟏 , 𝟎 , 𝟎 , 𝟎 , ⟨⟩)
 wikipedia-optimal-play＝ = refl
 -}

\end{code}

Example from Wikipedia again.

\begin{code}

module example-from-wikipedia' where

 open example-from-wikipedia

 wikipedia-G' : Game (ℕ × Path wikipedia-tree)
 wikipedia-G' = G' wikipedia-tree wikipedia-tree-is-listed⁺ wikipedia-q
  where
   open minimax'

 wikipedia-optimal-outcome' : ℕ × Path wikipedia-tree
 wikipedia-optimal-outcome' = optimal-outcome (ℕ × Path wikipedia-tree) wikipedia-G'

 wikipedia-optimal-outcome＝' : wikipedia-optimal-outcome' ＝ (6 , 𝟏 , 𝟎 , 𝟎 , 𝟎 , ⟨⟩)
 wikipedia-optimal-outcome＝' = refl

\end{code}

module example-from-wikipedia' where


 wikipedia-G⋆ : Game (ℕ × ℕ → ℕ × Path wikipedia-tree)
 wikipedia-G⋆ = G⋆
  where
   open minimax⋆
         ℕ
         0 10
         _<ℕ_
         <-decidable
         wikipedia-tree
         wikipedia-tree-is-listed⁺
         wikipedia-q

 wikipedia-optimal-outcome⋆ : ℕ × ℕ → ℕ × Path wikipedia-tree
 wikipedia-optimal-outcome⋆ = optimal-outcome (ℕ × ℕ → ℕ × Path wikipedia-tree) wikipedia-G⋆

 wikipedia-optimal-outcome＝⋆ : wikipedia-optimal-outcome⋆ (0 , 10)
                             ＝ (6 , 𝟏 , 𝟎 , 𝟎 , 𝟎 , ⟨⟩)
 wikipedia-optimal-outcome＝⋆ = refl

\end{code}

Two versions of tic-tac-toe.

\begin{code}

module tic-tac-toe where

 open import GamesMGU.alpha-beta {𝓤₀} {𝓤₀} ℕ _<ℕ_ <-decidable

 module _ {X : 𝓤₀ ̇ }
        where

  open list-util

  perm-tree : {n : ℕ} → Vector' X n → 𝑻
  perm-tree {0}        ([] , _) = []
  perm-tree {succ n} v@(xs , _) = type-from-list xs
                                ∷ λ (_ , m) → perm-tree {n} (delete v m)

  perm-tree-is-listed⁺ : {n : ℕ}
                           (v : Vector' X n)
                         → structure listed⁺ (perm-tree {n} v)
  perm-tree-is-listed⁺ {0}      ([]         , _) = ⟨⟩
  perm-tree-is-listed⁺ {succ n} (xs@(y ∷ _) , p) = ((y , in-head) , type-from-list-is-listed xs)
                                                   :: λ (_ , m) → perm-tree-is-listed⁺ {n}
                                                                   (delete (xs , p) m)

  remove-proofs : (n : ℕ) (v : Vector' X n)
                → Path (perm-tree v)
                → List X
  remove-proofs 0 _ _    = []
  remove-proofs (succ n) moves ((m , m-is-in-moves) :: ms)  =
   m ∷ remove-proofs n (delete moves m-is-in-moves) ms

 open list-util {𝓤₀} {ℕ}

 module version₁ where

  Move = ℕ -- We use 0 , ⋯ , 8 only

  all-moves : Vector' Move 9
  all-moves = (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ []) , refl

  TTT-tree : 𝑻
  TTT-tree = perm-tree all-moves

  TTT-tree-is-listed⁺ : structure listed⁺ TTT-tree
  TTT-tree-is-listed⁺ = perm-tree-is-listed⁺ all-moves

  R      = ℕ -- We use 0 (minimizer player wins) , 1 (draw) , 2 (maximizer player wins)
  Board  = List Move × List Move -- Moves of maximizer, respectively minimizer, player so far

  initial-board : Board
  initial-board = [] , []

  wins : List Move → Bool
  wins =
   some-contained ((0  ∷ 1  ∷ 2 ∷ [])
                 ∷ (3  ∷ 4  ∷ 5 ∷ [])
                 ∷ (6  ∷ 7  ∷ 8 ∷ [])
                 ∷ (0  ∷ 3  ∷ 6 ∷ [])
                 ∷ (1  ∷ 4  ∷ 7 ∷ [])
                 ∷ (2  ∷ 5  ∷ 8 ∷ [])
                 ∷ (0  ∷ 4  ∷ 8 ∷ [])
                 ∷ (2  ∷ 4  ∷ 6 ∷ [])
                 ∷ [])

  value : Board → R
  value (x , o) = if wins x then 2 else if wins o then 0 else 1

  data Player : 𝓤₀ ̇ where
   X O : Player

  maximizing-player : Player
  maximizing-player = X

  TTT-q : Path TTT-tree → R
  TTT-q ms = value (g ms)
   where
    h : (n : ℕ) (moves : Vector' Move n) → Path (perm-tree moves) → Player → Board → Board
    h 0 _ _ _  board = board
    h (succ n) moves ((m , m-is-in-moves) :: ms) X (x , o) =
      if wins o
      then (x , o)
      else h n (delete moves m-is-in-moves) ms O (insert m x , o)
    h (succ n) moves ((m , m-is-in-moves) :: ms) O (x , o) =
      if wins x
      then (x , o)
      else h n (delete moves m-is-in-moves) ms X (x , insert m o)

    g : Path TTT-tree → Board
    g ms = h 9 all-moves ms maximizing-player initial-board

  TTT-G : Game R
  TTT-G = G TTT-tree TTT-tree-is-listed⁺ TTT-q
   where
    open minimax

  TTT-optimal-outcome : R
  TTT-optimal-outcome = optimal-outcome R TTT-G

  TTT-G' : Game (R × Path TTT-tree)
  TTT-G' = G' TTT-tree TTT-tree-is-listed⁺ TTT-q
   where
    open minimax'

  TTT-optimal-outcome' : R × Path TTT-tree
  TTT-optimal-outcome' = optimal-outcome (R × Path TTT-tree) TTT-G'

  TTT-G⋆ : Game (R × R → R × Path TTT-tree)
  TTT-G⋆ = G⋆ TTT-tree TTT-tree-is-listed⁺ TTT-q 0 2
   where
    open minimax⋆

  TTT-optimal-outcome⋆ : R × Path TTT-tree
  TTT-optimal-outcome⋆ = optimal-outcome (R × R → R × Path TTT-tree) TTT-G⋆ (0 , 2)


  TTT-optimal-play : Path TTT-tree
  TTT-optimal-play = optimal-play TTT-tree TTT-tree-is-listed⁺ TTT-q
   where
    open minimax

  TTT-optimal-play† : Fun-Ext → Path TTT-tree
  TTT-optimal-play† fe = optimal-play† TTT-tree TTT-tree-is-listed⁺ TTT-q fe 0 2
   where
    open minimax

 module version₂  where

  Move = ℕ × ℕ

  all-moves : Vector' Move 9
  all-moves = ((0 , 0) ∷ (0 , 1) ∷ (0 , 2)
             ∷ (1 , 0) ∷ (1 , 1) ∷ (1 , 2)
             ∷ (2 , 0) ∷ (2 , 1) ∷ (2 , 2) ∷ []) ,
            refl

  TTT-tree : 𝑻
  TTT-tree = perm-tree all-moves

  TTT-tree-is-listed⁺ : structure listed⁺ TTT-tree
  TTT-tree-is-listed⁺ = perm-tree-is-listed⁺ all-moves

  data Player : 𝓤₀ ̇ where
   X O : Player

  opponent : Player → Player
  opponent X = O
  opponent O = X

  maximizing-player : Player
  maximizing-player = X

  R      = ℕ -- We use 0 (minimizer player wins) , 1 (draw) , 2 (maximizer player wins)
  Grid   = Move
  Matrix = Grid → Maybe Player
  Board  = Player × Matrix

  initial-board : Board
  initial-board = O , (λ _ → Nothing)

  wins : Board → Bool
  wins (p , A) = line || col || diag
   where
    _is_ : Maybe Player → Player → Bool
    Nothing is _ = false
    Just X  is X = true
    Just O  is X = false
    Just X  is O = false
    Just O  is O = true

    infix 30 _is_

    l₀ = A (0 , 0) is p && A (0 , 1) is p && A (0 , 2) is p
    l₁ = A (1 , 0) is p && A (1 , 1) is p && A (1 , 2) is p
    l₂ = A (2 , 0) is p && A (2 , 1) is p && A (2 , 2) is p

    c₀ = A (0 , 0) is p && A (1 , 0) is p && A (2 , 0) is p
    c₁ = A (0 , 1) is p && A (1 , 1) is p && A (2 , 1) is p
    c₂ = A (0 , 2) is p && A (1 , 2) is p && A (2 , 2) is p

    d₀ = A (0 , 0) is p && A (1 , 1) is p && A (2 , 2) is p
    d₁ = A (0 , 2) is p && A (1 , 1) is p && A (2 , 0) is p

    line = l₀ || l₁ || l₂
    col  = c₀ || c₁ || c₂
    diag = d₀ || d₁

  value : Board → R
  value b@(X , _) = if wins b then 2 else 1
  value b@(O , _) = if wins b then 0 else 1

  update : Move → Board → Board
  update (i₀ , j₀) (player , A) = (player' , A')
   where
    player' = opponent player

    A' : Matrix
    A' (i , j) = if (i == i₀) && (j == j₀) then Just player' else A (i , j)

  TTT-q : Path TTT-tree → R
  TTT-q ms = value (g ms)
   where
    h : (n : ℕ) (moves : Vector' Move n) → Path (perm-tree moves) → Board → Board
    h 0 _ _  board = board
    h (succ n) moves ((m , m-is-in-moves) :: ms) board =
      if wins board
      then board
      else h n (delete moves m-is-in-moves) ms (update m board)

    g : Path TTT-tree → Board
    g ms = h 9 all-moves ms initial-board

  TTT-G : Game R
  TTT-G = G TTT-tree TTT-tree-is-listed⁺ TTT-q
   where
    open minimax

  TTT-optimal-outcome : R
  TTT-optimal-outcome = optimal-outcome R TTT-G

  TTT-G' : Game (R × Path TTT-tree)
  TTT-G' = G' TTT-tree TTT-tree-is-listed⁺ TTT-q
   where
    open minimax'

  TTT-optimal-outcome' : R × Path TTT-tree
  TTT-optimal-outcome' = optimal-outcome (R × Path TTT-tree) TTT-G'

  TTT-G⋆ : Game (R × R → R × Path TTT-tree)
  TTT-G⋆ = G⋆ TTT-tree TTT-tree-is-listed⁺ TTT-q 0 2
   where
    open minimax⋆

  TTT-optimal-outcome⋆ : R × Path TTT-tree
  TTT-optimal-outcome⋆ = optimal-outcome (R × R → R × Path TTT-tree) TTT-G⋆ (0 , 2)

\end{code}

Slow. 28 minutes in a MacBook Air M1
 TTT-optimal-outcome＝⋆ : TTT-optimal-outcome⋆
                       ＝ (1 , ((0 :: in-head)
                            :: ((4 :: in-tail (in-tail (in-tail in-head)))
                            :: ((1 :: in-head)
                            :: ((2 :: in-head)
                            :: ((6 :: in-tail (in-tail in-head))
                            :: ((3 :: in-head)
                            :: ((5 :: in-head)
                            :: ((7 :: in-head)
                            :: ((8 :: in-head)
                            :: ⟨⟩))))))))))
 TTT-optimal-outcome＝⋆ = refl

This computes the optimal outcome using the standard minimax
algorithm with quantifiers:

\begin{code}

test : ℕ -- 22.7 seconds with `agda --compile` on a Mac M2
test = TTT-optimal-outcome
 where
  open tic-tac-toe
  open version₁

\end{code}

This is like test above, but using a different implementation of
the tic-tac-toe board:

\begin{code}

-test : ℕ -- 22.6 seconds with `agda --compile` on a Mac M2
-test = TTT-optimal-outcome
 where
  open tic-tac-toe
  open version₂


\end{code}

This tries to compute an optimal play using selection functions
without any optimization:

\begin{code}

testo : List ℕ -- It didn't finish in 7 hours  with `agda --compile` on a Mac M2
testo = remove-proofs _ all-moves TTT-optimal-play
 where
  open tic-tac-toe
  open version₁

\end{code}

This computes an optimal play using monadic selection functions,
with the reader monad, to implement alpha-beta prunning, which is a
new technique introduced in this file:

\begin{code}

test† : Fun-Ext → List ℕ -- 15 seconds with `agda --compile` on a Mac M2
test† fe = remove-proofs _ all-moves (TTT-optimal-play† fe)
 where
  open tic-tac-toe
  open version₁

\end{code}

This computes an optimal play using quantifiers, which is a new
technique introduced in this file:

\begin{code}

test' : List ℕ -- 22.7 seconds with `agda --compile` on a Mac M2
test' = remove-proofs _ all-moves (pr₂ TTT-optimal-outcome')
 where
  open tic-tac-toe
  open version₁

\end{code}

This is like test' above, but uses a different implementation of the
tic-tac-toe board:

\begin{code}

-test' : List (ℕ × ℕ) -- 27.7 seconds with `agda --compile` on a Mac M2
-test' = remove-proofs _ all-moves (pr₂ TTT-optimal-outcome')
 where
  open tic-tac-toe
  open version₂

\end{code}

This computes again an optimal play using monadic quantifiers, with
the reader monad, rather than selection functions, to implement
alpha-beta prunning, which is also a new thing in this file:

\begin{code}

test⋆ : List ℕ -- 2.8 seconds with `agda --compile` on a Mac M2
test⋆ = remove-proofs _ all-moves (pr₂ TTT-optimal-outcome⋆)
 where
  open tic-tac-toe
  open version₁

\end{code}

This is like test⋆ above, but uses a different implementation of
the tic-tac-toe board:

\begin{code}

-test⋆ : List (ℕ × ℕ) -- 3.3 seconds with `agda --compile` on a Mac M2
-test⋆ = remove-proofs _ all-moves (pr₂ TTT-optimal-outcome⋆)
 where
  open tic-tac-toe
  open version₂

\end{code}

So the alpha-beta prunned version is 8 times faster.

NB. The strictness option for compilation quadruples the run time.

TODO:

 * Formulate the correctness of G' and G⋆.
   (Actually done above in commented-out Agda code.)

 * Prove it!

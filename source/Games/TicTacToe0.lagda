Martin Escardo, Paulo Oliva, 27th October 2022

Implementation of tic-tac-toe using a general definition of finite
history dependent game.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Games.TicTacToe0 where

open import Fin.ArgMinMax
open import Fin.Topology
open import Fin.Type
open import Games.J
open import Games.K
open import Games.TypeTrees
open import MLTT.Athenian
open import MLTT.Spartan hiding (J)
open import TypeTopology.CompactTypes
open import TypeTopology.SigmaDiscreteAndTotallySeparated
open import UF.DiscreteAndSeparated

\end{code}

The type of outcomes:

\begin{code}

R : Type
R = Fin 3

open import Games.FiniteHistoryDependent R
open import Games.JK

\end{code}

The meaning of the outcomes:

\begin{code}

X-wins draw O-wins : R
X-wins = 𝟎
draw   = 𝟏
O-wins = 𝟐

\end{code}

In our conception of game, it is not necessary to specify the players,
but in this case it is convenient to do so:

\begin{code}

data Player : Type where
 X O : Player

opponent : Player → Player
opponent X = O
opponent O = X

value : Player → R
value X = X-wins
value O = O-wins

\end{code}

It is also convenient to have a type of boards:

\begin{code}

Grid   = Fin 3 × Fin 3
Matrix = Grid → Maybe Player
Board  = Player × Matrix

board₀ : Board
board₀ = X , (λ _ → Nothing)

\end{code}

Convention: in a board (p , A), the player p plays next.

\begin{code}

wins : Player → Matrix → Bool
wins p A = line || col || diag
 where
  _is_ : Maybe Player → Player → Bool
  Nothing is _ = false
  Just X  is X = true
  Just O  is X = false
  Just X  is O = false
  Just O  is O = true

  infix 30 _is_

  l₀ = A (𝟎 , 𝟎) is p && A (𝟎 , 𝟏) is p && A (𝟎 , 𝟐) is p
  l₁ = A (𝟏 , 𝟎) is p && A (𝟏 , 𝟏) is p && A (𝟏 , 𝟐) is p
  l₂ = A (𝟐 , 𝟎) is p && A (𝟐 , 𝟏) is p && A (𝟐 , 𝟐) is p

  c₀ = A (𝟎 , 𝟎) is p && A (𝟏 , 𝟎) is p && A (𝟐 , 𝟎) is p
  c₁ = A (𝟎 , 𝟏) is p && A (𝟏 , 𝟏) is p && A (𝟐 , 𝟏) is p
  c₂ = A (𝟎 , 𝟐) is p && A (𝟏 , 𝟐) is p && A (𝟐 , 𝟐) is p

  d₀ = A (𝟎 , 𝟎) is p && A (𝟏 , 𝟏) is p && A (𝟐 , 𝟐) is p
  d₁ = A (𝟎 , 𝟐) is p && A (𝟏 , 𝟏) is p && A (𝟐 , 𝟎) is p

  line = l₀ || l₁ || l₂
  col  = c₀ || c₁ || c₂
  diag = d₀ || d₁

\end{code}

The type of moves in a board:

\begin{code}

Move : Board → Type
Move (_ , A) = Σ g ꞉ Grid , A g ＝ Nothing

\end{code}

The type of grids has decidable equality (it is discrete) and
decidable quantification (it is compact).  The type of moves in a
board is decidable (either empty or pointed) and also has decidable
quantification.

\begin{code}

Grid-is-discrete : is-discrete Grid
Grid-is-discrete = ×-is-discrete Fin-is-discrete Fin-is-discrete

Grid-compact : is-Compact Grid {𝓤₀}
Grid-compact = ×-is-Compact Fin-Compact Fin-Compact

Move-decidable : (b : Board) → is-decidable (Move b)
Move-decidable (_ , A) = Grid-compact
                          (λ g → A g ＝ Nothing)
                          (λ g → Nothing-is-isolated' (A g))

Move-compact : (b : Board) → is-Compact (Move b)
Move-compact (x , A) = complemented-subset-of-compact-type
                        Grid-compact
                        (λ g → Nothing-is-isolated' (A g))
                        (λ g → Nothing-is-h-isolated' (A g))
\end{code}

Update a matrix by playing a move:

\begin{code}

update : (p : Player) (A : Matrix) → Move (p , A) → Matrix
update p A (g , _) g' with (Grid-is-discrete g g')
...                        | inl _ = Just p
...                        | inr _ = A g'

\end{code}

Update a board by playing a move:

\begin{code}

play : (b : Board) → Move b → Board
play (p , A) m = opponent p , update p A m

\end{code}

The game tree, with a bound on which we perform induction:

\begin{code}

tree : Board → ℕ → 𝑻
tree b         0        = []
tree b@(p , A) (succ k) with wins (opponent p) A | Move-decidable b
...                        | true  | _     = []
...                        | false | inl _ = Move b ∷ (λ (m : Move b) → tree (play b m) k)
...                        | false | inr _ = []

\end{code}

The outcome function:

\begin{code}

outcome : (b : Board) (k : ℕ) → Path (tree b k) → R
outcome b 0 ⟨⟩ = draw
outcome b@(p , A) (succ k) ms with wins (opponent p) A | Move-decidable b
outcome b@(p , A) (succ k) ⟨⟩        | true  | _     = value (opponent p)
outcome b@(p , A) (succ k) (m :: ms) | false | inl _ = outcome (play b m) k ms
outcome b@(p , A) (succ k) ⟨⟩        | false | inr _ = draw

\end{code}

Selection functions for players, namely argmin for X and argmax for O:

\begin{code}

open J-definitions R

selection : (p : Player) {M : Type} → M → is-Compact M {𝓤₀} → J M
selection X m κ p = pr₁ (compact-argmin p κ m)
selection O m κ p = pr₁ (compact-argmax p κ m)

\end{code}

And their derived quantifiers:

\begin{code}

open K-definitions R
open JK R

quantifier : Player → {M : Type} → is-Compact M → is-decidable M → K M
quantifier p κ (inl m) = overline (selection p m κ)
quantifier p κ (inr _) = λ _ → draw

\end{code}

The quantifier tree for the game:

\begin{code}

quantifiers : (b : Board) (k : ℕ) → 𝓚 (tree b k)
quantifiers b 0 = ⟨⟩
quantifiers b@(p , A) (succ k) with wins (opponent p) A | Move-decidable b
... | true  | _     = ⟨⟩
... | false | inl _ = quantifier p (Move-compact b) (Move-decidable b)
                      :: (λ (m : Move b) → quantifiers (play b m) k)
... | false | inr _ = ⟨⟩
\end{code}

And finally the game by putting the above together:

\begin{code}

tic-tac-toe : Game
tic-tac-toe = game (tree board₀ 9) (outcome board₀ 9) (quantifiers board₀ 9)

r : R
r = optimal-outcome tic-tac-toe

\end{code}

The above computation takes too long, due to the use of brute-force
search in the definition of the game (the compactness conditions). A
more efficient one is in another file.

\begin{code}

selections : (b : Board) (k : ℕ) → 𝓙 (tree b k)
selections b 0 = ⟨⟩
selections b@(p , A) (succ k) with wins (opponent p) A | Move-decidable b
... | true  | _      = ⟨⟩
... | false | inl m₀ = selection p m₀ (Move-compact b)
                      :: (λ m → selections (play b m) k)
... | false | inr _  = ⟨⟩


p : Path (Xt tic-tac-toe)
p = sequenceᴶ (selections board₀ 9) (q tic-tac-toe)

\end{code}

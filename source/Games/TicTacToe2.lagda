Martin Escardo, Paulo Oliva, 2-27 July 2021

Example: Tic-tac-toe. We have two versions. The other version is in
another file.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}


module Games.TicTacToe2 where

open import MLTT.Spartan hiding (J)
open import MLTT.Fin
open import MLTT.List

data 𝟛 : Type where
 O-wins draw X-wins : 𝟛

open import Games.Constructor 𝟛
open import Games.FiniteHistoryDependent 𝟛
open import Games.TypeTrees
open import Games.J
open import MLTT.Athenian
open import TypeTopology.SigmaDiscreteAndTotallySeparated

open list-util

tic-tac-toe₂J : GameJ
tic-tac-toe₂J = build-GameJ draw Board transition 9 board₀
 where
  flip : 𝟛 → 𝟛
  flip O-wins = X-wins
  flip draw   = draw
  flip X-wins = O-wins

  data Player : Type where
   O X : Player

  Cell = Fin 9

  record Board : Type where
   pattern
   constructor board
   field
    next-player     : Player
    available-moves : List Cell
    X-moves         : List Cell
    O-moves         : List Cell

  open Board

  opponent-wins : Player → 𝟛
  opponent-wins X = O-wins
  opponent-wins O = X-wins

  winning : List Cell → Bool
  winning = some-contained ((𝟎 ∷ 𝟏 ∷ 𝟐 ∷ [])
                          ∷ (𝟑 ∷ 𝟒 ∷ 𝟓 ∷ [])
                          ∷ (𝟔 ∷ 𝟕 ∷ 𝟖 ∷ [])
                          ∷ (𝟎 ∷ 𝟑 ∷ 𝟔 ∷ [])
                          ∷ (𝟏 ∷ 𝟒 ∷ 𝟕 ∷ [])
                          ∷ (𝟐 ∷ 𝟓 ∷ 𝟖 ∷ [])
                          ∷ (𝟎 ∷ 𝟒 ∷ 𝟖 ∷ [])
                          ∷ (𝟐 ∷ 𝟒 ∷ 𝟔 ∷ [])
                          ∷ [])

  wins : Board → Bool
  wins (board O _ _  os) = winning os
  wins (board X _ xs  _) = winning xs

  board₀ : Board
  board₀ = board X (list-Fin 9) [] []

  Move : List Cell → Type
  Move xs = Σ c ꞉ Cell , ((c is-in xs) ＝ true)

\end{code}

The following definition of argmax is somewhat convoluted because it
is optimized for time, by minimizing the number of evaluations of the
predicate q:

\begin{code}

  argmax : (m : Cell) (ms : List Cell) → 𝟛 → (Move (m ∷ ms) → 𝟛) → Move (m ∷ ms)
  argmax m ms       X-wins  q = m , need m == m || (m is-in ms) ＝ true
                                    which-is-given-by ||-left-intro _ (==-refl m)

  argmax m []       r       q = m , need m == m || (m is-in []) ＝ true
                                    which-is-given-by ||-left-intro _ (==-refl m)

  argmax m (x ∷ xs) O-wins  q = ι γ
   where
    ι : Move (x ∷ xs) → Move (m ∷ x ∷ xs)
    ι (c , e) = c , need c == m || (c is-in (x ∷ xs)) ＝ true
                    which-is-given-by ||-right-intro {c == m} _ e

    q' : Move (x ∷ xs) → 𝟛
    q' m = q (ι m)

    a : (x == m) || ((x == x) || (x is-in xs)) ＝ true
    a = ||-right-intro {x == m} _ (||-left-intro _ (==-refl x))

    γ : Move (x ∷ xs)
    γ = argmax x xs (q (x , a)) q'

  argmax m us@(x ∷ ms) draw q = g us c
   where
    c : ((x == x) || (x is-in ms)) && (ms contained-in (x ∷ ms)) ＝ true
    c = &&-intro (||-left-intro _ (==-refl x)) (contained-lemma₁ x ms)

    g : (vs : List Cell) → vs contained-in us ＝ true → Move (m ∷ us)
    g []       c = m , need m == m || (m is-in (x ∷ ms)) ＝ true
                       which-is-given-by ||-left-intro _ (==-refl m)

    g (y ∷ vs) c = k (q (y , a))
     where
      a : (y == m) || ((y == x) || (y is-in ms)) ＝ true
      a = ||-right-intro {y == m} _ (pr₁ (&&-gives-× c))

      b : (vs contained-in (x ∷ ms)) ＝ true
      b = pr₂ (&&-gives-× c)

      k : 𝟛 → Move (m ∷ us)
      k X-wins = y , a
      k r      = g vs b

  open J-definitions 𝟛

  argmin : (m : Cell) (ms : List Cell) → 𝟛 → (Move (m ∷ ms) → 𝟛) → Move (m ∷ ms)
  argmin m ms r q = argmax m ms (flip r) (λ xs → flip (q xs))

  arg : Player → (ms : List Cell) → empty ms ＝ false →  J (Move ms)
  arg _ []       e q = 𝟘-elim (true-is-not-false e)
  arg X (m ∷ ms) e q = argmax m ms (q (m , ||-left-intro (m is-in ms) (==-refl m))) q
  arg O (m ∷ ms) e q = argmin m ms (q (m , ||-left-intro (m is-in ms) (==-refl m))) q

  play : (b : Board) → Move (available-moves b) → Board
  play (board X as xs os) (c , e) = board O (remove c as) (insert c xs) os
  play (board O as xs os) (c , e) = board X (remove c as) xs            (insert c os)

  transition : Board → 𝟛 + (Σ M ꞉ Type , (M → Board) × J M)
  transition b@(board next as xs os) =
   if wins b
   then inl (opponent-wins next)
   else Bool-equality-cases (empty as)
         (λ (_ : empty as ＝ true)  → inl draw)
         (λ (e : empty as ＝ false) → inr (Move as , play b , arg next as e))

tic-tac-toe₂ : Game
tic-tac-toe₂ = Game-from-GameJ tic-tac-toe₂J

t₂ : 𝟛
t₂ = optimal-outcome tic-tac-toe₂

s₂ : Path (Xt tic-tac-toe₂)
s₂ = strategic-path (selection-strategy (selections tic-tac-toe₂J) (q tic-tac-toe₂))

u₂ : Path (Xt tic-tac-toe₂)
u₂ = sequenceᴶ (selections tic-tac-toe₂J) (q tic-tac-toe₂)

l₂ : ℕ
l₂ = plength s₂

{- Slow

t₂-test : t₂ ＝ draw
t₂-test = refl

-}

{- Slow:

l₂-test : l₂ ＝ 9
l₂-test = refl

-}

{- slow

open import Athenian

u₂-test : s₂ ＝ (𝟎 :: refl)
           :: ((𝟒 :: refl)
           :: ((𝟏 :: refl)
           :: ((𝟐 :: refl)
           :: ((𝟔 :: refl)
           :: ((𝟑 :: refl)
           :: ((𝟓 :: refl)
           :: ((𝟕 :: refl)
           :: ((𝟖 :: refl)
           :: ⟨⟩))))))))
u₂-test = refl
-}

\end{code}

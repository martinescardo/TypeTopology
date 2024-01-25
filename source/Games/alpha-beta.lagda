Martin Escardo, Paulo Oliva, March - April 2023

This file is mostly for efficiency. See the tests with tic-tac-toe at
the end of this file with the various possibilities offered here.

We incorporate alpha-beta pruning to our previous work on finite
history-dependent games using the selection and continuous monads (in
the module Games.FiniteHistoryDependent). But we do much more than
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
open import MLTT.Fin
open import Games.FiniteHistoryDependent
open import Games.TypeTrees
open import Games.K
open import Games.J
open import MLTT.Athenian
open import UF.FunExt

\end{code}

Part 0.

We now define standard minimax games.

\begin{code}

module Games.alpha-beta where

module minimax
        (R : Type)
        (_<_ : R → R → Type)
        (δ : (r s : R) → is-decidable (r < s))
        (Xt : 𝑻)
        (Xt-is-listed⁺ : structure listed⁺ Xt)
        (q : Path Xt → R)
       where

 _≥_ : R → R → Type
 r ≥ s = ¬ (r < s)

\end{code}

After defining min and max, we can define the given game G from the
data given as module parameter.

\begin{code}

 max min : R → R → R

 max r s = Cases (δ r s)
            (λ (_ : r < s) → s)
            (λ (_ : r ≥ s) → r)

 min r s = Cases (δ s r)
            (λ (_ : s < r) → s)
            (λ (_ : s ≥ r) → r)

\end{code}

Part 0.

\begin{code}

 open K-definitions R

 Min Max : {X : Type} → listed⁺ X → K X
 Min (x₀ , xs , _) p = foldr (λ x → min (p x)) (p x₀) xs
 Max (x₀ , xs , _) p = foldr (λ x → max (p x)) (p x₀) xs

\end{code}

TODO. Min and Max do indeed compute the minimum and maximum
value of p : X → R (easy).

We now label the give tree Xt with the above Min and Max quantifiers
in an alternating fashion.

\begin{code}

 minmax maxmin : (Xt : 𝑻)
               → structure listed⁺ Xt
               → 𝓚 R Xt
 minmax []       ⟨⟩        = ⟨⟩
 minmax (X ∷ Xf) (ℓ :: ss) = Min ℓ :: (λ x → maxmin (Xf x) (ss x))

 maxmin []       ⟨⟩        = ⟨⟩
 maxmin (X ∷ Xf) (ℓ :: ss) = Max ℓ :: (λ x → minmax (Xf x) (ss x))

 G-quantifiers : 𝓚 R Xt
 G-quantifiers = maxmin Xt Xt-is-listed⁺

\end{code}

And with this we get the desired maxmin game.

\begin{code}

 G : Game R
 G = game Xt q G-quantifiers

\end{code}

Now we define selection functions for this game.

\begin{code}

 argmin argmax : {X : Type} → (X → R) → X → X → X

 argmin p x m = Cases (δ (p x) (p m))
                 (λ (_ : p x < p m) → x)
                 (λ (_ : p x ≥ p m) → m)

 argmax p x m = Cases (δ (p m) (p x))
                 (λ (_ : p m < p x) → x)
                 (λ (_ : p m ≥ p x) → m)

 open J-definitions R

 ArgMin ArgMax : {X : Type} → listed⁺ X → J X
 ArgMin (x₀ , xs , _) p = foldr (argmin p) x₀ xs
 ArgMax (x₀ , xs , _) p = foldr (argmax p) x₀ xs

\end{code}

TODO. Show that ArgMin and ArgMax are selection functions for the
quantifiers Min and Max (easy).

We now label the give tree Xt with the above ArgMin and ArgMax
quantifiers in an alternating fashion.

\begin{code}

 argminmax argmaxmin : (Xt : 𝑻)
                     → structure listed⁺ Xt
                     → 𝓙 R Xt
 argminmax []       ⟨⟩        = ⟨⟩
 argminmax (X ∷ Xf) (ℓ :: ℓf) = ArgMin ℓ :: (λ x → argmaxmin (Xf x) (ℓf x))

 argmaxmin []       ⟨⟩        = ⟨⟩
 argmaxmin (X ∷ Xf) (ℓ :: ℓf) = ArgMax ℓ :: (λ x → argminmax (Xf x) (ℓf x))

 G-selections : 𝓙 R Xt
 G-selections = argmaxmin Xt Xt-is-listed⁺

 G-strategy : Strategy R Xt
 G-strategy = selection-strategy R G-selections q

 optimal-play : Path Xt
 optimal-play = sequenceᴶ R G-selections q

\end{code}

TODO. Prove the lemma formulated as an assumption of the above module (easy).

\begin{code}

 module _ (lemma : _Attains_ R G-selections G-quantifiers)
          (fe : Fun-Ext)
        where

  theorem : is-optimal R G (selection-strategy R G-selections q)
  theorem = Selection-Strategy-Theorem R fe G G-selections lemma

  corollary : q optimal-play ＝ optimal-outcome R G
  corollary = selection-strategy-corollary R fe G G-selections lemma

\end{code}

We now define monadic selection functions with α-β-pruning, using the
reader monad, to speed-up the computation of the optimal play.

\begin{code}

 module _ (fe : Fun-Ext) (-∞ ∞ : R) where

  open import Games.Reader
  open import Games.Monad

  AB = R × R

  T : Type → Type
  T = functor (Reader AB)

  private
   NB : T R ＝ (AB → R)
   NB = refl

  q† : Path Xt → T R
  q† xs (α , β) = q xs

  ArgMin† ArgMax† : {X : Type} → List X → X → R → (X → T R) → T X

  ArgMin† []       x₀ r p (α , β) = x₀
  ArgMin† (x ∷ xs) x₀ r p (α , β) =
   case p x (α , β) of
    λ (s : R)
      → Cases (δ α s)
         (λ (_ : α < s)
               → Cases (δ s r)
                  (λ (_ : s < r) → ArgMin† xs x  s p (α , min β s))
                  (λ (_ : s ≥ r) → ArgMin† xs x₀ r p (α , β)))
         (λ (_ : α ≥ s)
               → x)

  ArgMax† []       x₀ r p (α , β) = x₀
  ArgMax† (x ∷ xs) x₀ r p (α , β) =
   case p x (α , β) of
    λ (s : R)
      → Cases (δ s β)
         (λ (_ : s < β)
               → Cases (δ r s)
                  (λ (_ : r < s) → ArgMax† xs x  s p (max α s , β))
                  (λ (_ : r ≥ s) → ArgMax† xs x₀ r p (α , β)))
         (λ (_ : s ≥ β)
               → x)

  𝓡 : Algebra (Reader AB) R
  𝓡 = record {
        structure-map = λ (t : AB → R) → t (-∞ , ∞) ;
        unit = λ x → refl ;
        assoc = λ x → refl
       }

  ρ : T R → R
  ρ = structure-map 𝓡

  open import Games.FiniteHistoryDependentTransformer
               fe
               (Reader AB)
               R
               𝓡

  argminmax† argmaxmin† : (Xt : 𝑻)
                        → structure listed⁺ Xt
                        → 𝓙𝓣 Xt
  argminmax† []       ⟨⟩                    = ⟨⟩
  argminmax† (X ∷ Xf) ((x₀ , xs , _) :: ss) =
   (λ (p : X → T R) → ArgMin† xs x₀ (ρ (p x₀)) p)
   :: (λ x → argmaxmin† (Xf x) (ss x))

  argmaxmin† []       ⟨⟩                    = ⟨⟩
  argmaxmin† (X ∷ Xf) ((x₀ , xs , _) :: ss) =
   (λ (p : X → T R) → ArgMax† xs x₀ (ρ (p x₀)) p)
   :: (λ x → argminmax† (Xf x) (ss x))

  G-selections† : 𝓙𝓣 Xt
  G-selections† = argmaxmin† Xt Xt-is-listed⁺

  optimal-play† : Path Xt
  optimal-play† = sequenceᴶᵀ G-selections† q† (-∞ , ∞)

\end{code}

TODO. Formulate and prove the correctness of the the optimal-play†.

Example from Wikipedia:
https://en.wikipedia.org/wiki/Alpha%E2%80%93beta_pruning

\begin{code}

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

 open import Naturals.Order
 open minimax
       ℕ
       _<ℕ_
       <-decidable
       wikipedia-tree
       wikipedia-tree-is-listed⁺
       wikipedia-q

 wikipedia-G : Game ℕ
 wikipedia-G = G

 wikipedia-optimal-play : Path wikipedia-tree
 wikipedia-optimal-play = optimal-play

wikipedia-optimal-outcome : ℕ
wikipedia-optimal-outcome = optimal-outcome ℕ wikipedia-G

wikipedia-optimal-outcome＝ : wikipedia-optimal-outcome ＝ 6
wikipedia-optimal-outcome＝ = refl

{- Comment out because it is slow:

wikipedia-optimal-play＝ : wikipedia-optimal-play ＝ (𝟏 , 𝟎 , 𝟎 , 𝟎 , ⟨⟩)
wikipedia-optimal-play＝ = refl
-}

\end{code}

Part 1.

Now we define G' which computes optimal strategies using quantifiers
with a modification of the outcome type to include paths.

\begin{code}

module minimax'
        (R : Type)
        (_<_ : R → R → Type)
        (δ : (r s : R) → is-decidable (r < s))
        (Xt : 𝑻)
        (Xt-is-listed⁺ : structure listed⁺ Xt)
        (q : Path Xt → R)
       where

 _≥_ : R → R → Type
 r ≥ s = ¬ (r < s)

 R' : Type
 R' = R × Path Xt

 q' : Path Xt → R'
 q' xs = q xs , xs

 max' min' : R' → R' → R'

 max' (r , xs) (s , ys)  = Cases (δ r s)
                            (λ (_ : r < s) → (s , ys))
                            (λ (_ : r ≥ s) → (r , xs))

 min' (r , xs) (s , ys)  = Cases (δ s r)
                            (λ (_ : s < r) → (s , ys))
                            (λ (_ : s ≥ r) → (r , xs))

 open K-definitions R'

 Min' Max' : {X : Type} → listed⁺ X → K X
 Min' (x₀ , xs , _) p = foldr (λ x → min' (p x)) (p x₀) xs
 Max' (x₀ , xs , _) p = foldr (λ x → max' (p x)) (p x₀) xs

 minmax' maxmin' : (Xt : 𝑻)
                 → structure listed⁺ Xt
                 → 𝓚 R' Xt
 minmax' []       ⟨⟩        = ⟨⟩
 minmax' (X ∷ Xf) (ℓ :: ℓf) = Min' ℓ :: (λ x → maxmin' (Xf x) (ℓf x))
 maxmin' []       ⟨⟩        = ⟨⟩
 maxmin' (X ∷ Xf) (ℓ :: ℓf) = Max' ℓ :: (λ x → minmax' (Xf x) (ℓf x))

 G' : Game R'
 G' = game Xt q' (maxmin' Xt Xt-is-listed⁺)

{- TODO.

 module _ where

  open minimax R _<_ δ Xt Xt-is-listed⁺ q

  theorem' : optimal-outcome R' G'
           ＝ (K-sequence R (maxmin Xt Xt-is-listed⁺) q ,
              sequenceᴶ R (argmaxmin Xt Xt-is-listed⁺) q)
  theorem' = {!!}
-}

\end{code}

Example from Wikipedia again.

\begin{code}

wikipedia-G' : Game (ℕ × Path wikipedia-tree)
wikipedia-G' = G'
 where
  open import Naturals.Order
  open minimax'
        ℕ
        _<ℕ_
        <-decidable
        wikipedia-tree
        wikipedia-tree-is-listed⁺
        wikipedia-q

wikipedia-optimal-outcome' : ℕ × Path wikipedia-tree
wikipedia-optimal-outcome' = optimal-outcome (ℕ × Path wikipedia-tree) wikipedia-G'

wikipedia-optimal-outcome＝' : wikipedia-optimal-outcome' ＝ (6 , 𝟏 , 𝟎 , 𝟎 , 𝟎 , ⟨⟩)
wikipedia-optimal-outcome＝' = refl

\end{code}

Now we define G⋆ which again using quantifiers, rather than selection
functions, to compute optimal strategies, but now using monadic
quantifiers with the reader monad to incorporate alpha-beta pruning.

\begin{code}

module minimax⋆
        (R : Type)
        (-∞ ∞ : R)
        (_<_ : R → R → Type)
        (δ : (r s : R) → is-decidable (r < s))
        (Xt : 𝑻)
        (Xt-is-listed⁺ : structure listed⁺ Xt)
        (q : Path Xt → R)
       where

 _≥_ : R → R → Type
 r ≥ s = ¬ (r < s)

 max min : R → R → R

 max r s = Cases (δ r s)
            (λ (_ : r < s) → s)
            (λ (_ : r ≥ s) → r)

 min r s = Cases (δ s r)
            (λ (_ : s < r) → s)
            (λ (_ : s ≥ r) → r)

 open import Games.Reader
 open import Games.Monad

 AB = R × R

 R⋆ : Type
 R⋆ = functor (Reader AB) (R × Path Xt)

 private
  NB : R⋆ ＝ (AB → R × Path Xt)
  NB = refl

 q⋆ : Path Xt → R⋆
 q⋆ xs (α , β) = q xs , xs

 max⋆ min⋆ : R⋆ → R⋆ → R⋆

 max⋆ r s αβ = Cases (δ (pr₁ (r αβ)) (pr₁ (s αβ)))
                (λ (_ : pr₁ (r αβ) < pr₁ (s αβ)) → s αβ)
                (λ (_ : pr₁ (r αβ) ≥ pr₁ (s αβ)) → r αβ)

 min⋆ r s αβ = Cases (δ (pr₁ (s αβ)) (pr₁ (r αβ)))
                (λ (_ : pr₁ (s αβ) < pr₁ (r αβ)) → s αβ)
                (λ (_ : pr₁ (s αβ) ≥ pr₁ (r αβ)) → r αβ)

 Min⋆ Max⋆ : {X : 𝓤 ̇ } → List X → (R × Path Xt) → (X → R⋆) → R⋆

 Min⋆ []       (t , zs) p (α , β) = (t , zs)
 Min⋆ (x ∷ xs) (t , zs) p (α , β) =
  case p x (α , β) of
   λ ((s , ys) : (R × Path Xt))
     → Cases (δ α s)
        (λ (_ : α < s)
              → Cases (δ s t)
                 (λ (_ : s < t) → Min⋆ xs (s , ys) p (α , min β s))
                 (λ (_ : s ≥ t) → Min⋆ xs (t , zs) p (α , β)))
        (λ (_ : α ≥ s)
              → (s , ys))

 Max⋆ []       (t , zs) p (α , β) = (t , zs)
 Max⋆ (x ∷ xs) (t , zs) p (α , β) =
  case p x (α , β) of
   λ ((s , ys) : (R × Path Xt))
     → Cases (δ s β)
        (λ (_ : s < β)
              → Cases (δ t s)
                 (λ (_ : t < s) → Max⋆ xs (s , ys) p (max α s , β))
                 (λ (_ : t ≥ s) → Max⋆ xs (t , zs) p (α , β)))
        (λ (_ : s ≥ β)
              → (s , ys))

 minmax⋆ maxmin⋆ : (Xt : 𝑻)
                 → structure listed⁺ Xt
                 → 𝓚 R⋆ Xt
 minmax⋆ []       ⟨⟩                    = ⟨⟩
 minmax⋆ (X ∷ Xf) ((x₀ , xs , _) :: ss) = (λ p → Min⋆ xs (p x₀ (-∞ , ∞)) p)
                                       :: (λ x → maxmin⋆ (Xf x) (ss x))
 maxmin⋆ []       ⟨⟩                    = ⟨⟩
 maxmin⋆ (X ∷ Xf) ((x₀ , xs , _) :: ss) = (λ p → Max⋆ xs (p x₀ (-∞ , ∞)) p)
                                       :: (λ x → minmax⋆ (Xf x) (ss x))

 G⋆ : Game R⋆
 G⋆ = game Xt q⋆ (maxmin⋆ Xt Xt-is-listed⁺)

{- TODO.

 module _ where

  open minimax' R _<_ δ Xt Xt-is-listed⁺ q

  theorem⋆₁ : pr₁ (optimal-outcome R⋆ G⋆ (-∞ , ∞)) ＝ pr₁ (optimal-outcome R' G')
  theorem⋆₁ = {!!}

  theorem⋆₂ : q (pr₂ (optimal-outcome R⋆ G⋆ (-∞ , ∞)))
           ＝ pr₁ (optimal-outcome R⋆ G⋆ (-∞ , ∞))
  theorem⋆₂ = {!!}
-}

wikipedia-G⋆ : Game (ℕ × ℕ → ℕ × Path wikipedia-tree)
wikipedia-G⋆ = G⋆
 where
  open import Naturals.Order
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

module _ {X : Type }
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

module tic-tac-toe where

 open list-util {𝓤₀} {ℕ}

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

 data Player : Type where
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
 TTT-G = G
  where
   open import Naturals.Order
   open minimax
         ℕ
         _<ℕ_
         <-decidable
         TTT-tree
         TTT-tree-is-listed⁺
         TTT-q

 TTT-optimal-outcome : R
 TTT-optimal-outcome = optimal-outcome R TTT-G

 TTT-G' : Game (R × Path TTT-tree)
 TTT-G' = G'
  where
   open import Naturals.Order
   open minimax'
         ℕ
         _<ℕ_
         <-decidable
         TTT-tree
         TTT-tree-is-listed⁺
         TTT-q

 TTT-optimal-outcome' : R × Path TTT-tree
 TTT-optimal-outcome' = optimal-outcome (R × Path TTT-tree) TTT-G'

 TTT-G⋆ : Game (R × R → R × Path TTT-tree)
 TTT-G⋆ = G⋆
  where
   open import Naturals.Order
   open minimax⋆
         ℕ
         0 2
         _<ℕ_
         <-decidable
         TTT-tree
         TTT-tree-is-listed⁺
         TTT-q

 TTT-optimal-outcome⋆ : R × Path TTT-tree
 TTT-optimal-outcome⋆ = optimal-outcome (R × R → R × Path TTT-tree) TTT-G⋆ (0 , 2)


 remove-proofs : (n : ℕ) (v : Vector' Move n)
               → Path (perm-tree v)
               → List Move
 remove-proofs 0 _ _    = []
 remove-proofs (succ n) moves ((m , m-is-in-moves) :: ms)  =
  m ∷ remove-proofs n (delete moves m-is-in-moves) ms

 TTT-optimal-play : Path TTT-tree
 TTT-optimal-play = optimal-play
  where
   open import Naturals.Order
   open minimax
         ℕ
         _<ℕ_
         <-decidable
         TTT-tree
         TTT-tree-is-listed⁺
         TTT-q

 TTT-optimal-play† : Fun-Ext → Path TTT-tree
 TTT-optimal-play† fe = optimal-play† fe 0 2
  where
   open import Naturals.Order
   open minimax
         ℕ
         _<ℕ_
         <-decidable
         TTT-tree
         TTT-tree-is-listed⁺
         TTT-q

module tic-tac-toe-variation where

 open list-util {𝓤₀} {ℕ}

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

 data Player : Type where
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
 TTT-G = G
  where
   open import Naturals.Order
   open minimax
         ℕ
         _<ℕ_
         <-decidable
         TTT-tree
         TTT-tree-is-listed⁺
         TTT-q

 TTT-optimal-outcome : R
 TTT-optimal-outcome = optimal-outcome R TTT-G

 TTT-G' : Game (R × Path TTT-tree)
 TTT-G' = G'
  where
   open import Naturals.Order
   open minimax'
         ℕ
         _<ℕ_
         <-decidable
         TTT-tree
         TTT-tree-is-listed⁺
         TTT-q

 TTT-optimal-outcome' : R × Path TTT-tree
 TTT-optimal-outcome' = optimal-outcome (R × Path TTT-tree) TTT-G'

 TTT-G⋆ : Game (R × R → R × Path TTT-tree)
 TTT-G⋆ = G⋆
  where
   open import Naturals.Order
   open minimax⋆
         ℕ
         0 2
         _<ℕ_
         <-decidable
         TTT-tree
         TTT-tree-is-listed⁺
         TTT-q

 TTT-optimal-outcome⋆ : R × Path TTT-tree
 TTT-optimal-outcome⋆ = optimal-outcome (R × R → R × Path TTT-tree) TTT-G⋆ (0 , 2)

 remove-proofs : (n : ℕ) (v : Vector' Move n) → Path (perm-tree v) → List Move
 remove-proofs 0 _ _    = []
 remove-proofs (succ n) moves ((m , m-is-in-moves) :: ms)  =
  m ∷ remove-proofs n (delete moves m-is-in-moves) ms

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

\end{code}

This is like test above, but using a different implementation of
the tic-tac-toe board:

\begin{code}

-test : ℕ -- 22.6 seconds with `agda --compile` on a Mac M2
-test = TTT-optimal-outcome
 where
  open tic-tac-toe-variation

\end{code}

This tries to compute an optimal play using selection functions
without any optimization:

\begin{code}

testo : List ℕ -- It didn't finish in 7 hours  with `agda --compile` on a Mac M2
testo = remove-proofs _ all-moves TTT-optimal-play
 where
  open tic-tac-toe

\end{code}

This computes an optimal play using monadic selection functions,
with the reader monad, to implement alpha-beta prunning, which is a
new technique introduced in this file:

\begin{code}

test† : Fun-Ext → List ℕ -- 15 seconds with `agda --compile` on a Mac M2
test† fe = remove-proofs _ all-moves (TTT-optimal-play† fe)
 where
  open tic-tac-toe

\end{code}

This computes an optimal play using quantifiers, which is a new
technique introduced in this file:

\begin{code}

test' : List ℕ -- 22.7 seconds with `agda --compile` on a Mac M2
test' = remove-proofs _ all-moves (pr₂ TTT-optimal-outcome')
 where
  open tic-tac-toe

\end{code}

This is like test' above, but uses a different implementation of the
tic-tac-toe board:

\begin{code}

-test' : List (ℕ × ℕ) -- 27.7 seconds with `agda --compile` on a Mac M2
-test' = remove-proofs _ all-moves (pr₂ TTT-optimal-outcome')
 where
  open tic-tac-toe-variation

\end{code}

This computes again an optimal play using monadic quantifiers, with
the reader monad, rather than selection functions, to implement
alpha-beta prunning, which is also a new thing in this file:

\begin{code}

test⋆ : List ℕ -- 2.8 seconds with `agda --compile` on a Mac M2
test⋆ = remove-proofs _ all-moves (pr₂ TTT-optimal-outcome⋆)
 where
  open tic-tac-toe

\end{code}

This is like test⋆ above, but uses a different implementation of
the tic-tac-toe board:

\begin{code}

-test⋆ : List (ℕ × ℕ) -- 3.3 seconds with `agda --compile` on a Mac M2
-test⋆ = remove-proofs _ all-moves (pr₂ TTT-optimal-outcome⋆)
 where
  open tic-tac-toe-variation

\end{code}

So the alpha-beta prunned version is 8 times faster.

NB. The strictness option for compilation quadruples the run time.

TODO:

 * Formulate the correctness of G' and G⋆.
   (Actually done above in commented-out Agda code.)

 * Prove it!

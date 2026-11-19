Martin Escardo and Paulo Oliva, originally March - April 2023, with the
proofs November 2026.

Part of the formalization, in Games.AlphaBeta.index, of the paper

  Martín Hötzel Escardó and Paulo Oliva.
  Alpha-Beta Pruning via Monadic Continuations.

The example game of Sections 2 and 3 of the paper.

This is the game tree of the Wikipedia article on alpha-beta pruning,
in its version of 14 October 2026,
https://en.wikipedia.org/w/index.php?oldid=1380302874, with
alternating maximizing and minimizing players, three, two, two and
three moves at the four rounds, and outcomes in the natural numbers.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

module Games.AlphaBeta.Examples where

open import MLTT.Spartan
open import MLTT.Fin
open import MLTT.List
open import Naturals.Order
open import OrderedTypes.DecidableStrictWeakOrder
open import Games.AlphaBeta.Player
open import Games.TypeTrees {𝓤₀}
open import MonadOnTypes.NonEmptyList using (List⁺)
open import Games.OptimalPlays {𝓤₀} {𝓤₀} ℕ using (is-optimal-play)

\end{code}

The usual order of the natural numbers is a decidable strict weak
order.

\begin{code}

ℕ-order : Decidable-Strict-Weak-Order ℕ 𝓤₀
ℕ-order = record
 { _<_            = _<ℕ_
 ; <-decidable    = <-decidable
 ; <-irreflexive  = not-less-than-itself
 ; <-transitive   = <-trans
 ; <-cotransitive = cotransitive
 }
 where
  cotransitive : (a b c : ℕ) → a <ℕ b → (a <ℕ c) + (c <ℕ b)
  cotransitive a b c l =
   Cases (<-decidable a c)
    inl
    (λ (n : ¬ (a <ℕ c)) →
      inr (≤-<-trans c a b (not-less-bigger-or-equal c a n) l))

\end{code}

The game tree, with the moves at each node listed in increasing order.

\begin{code}

wikipedia-tree : 𝑻
wikipedia-tree = Fin 3 ∷ λ _ → Fin 2 ∷ λ _ → Fin 2 ∷ λ _ → Fin 3 ∷ λ _ → []

two : List⁺ (Fin 2)
two = (𝟎 ∷ 𝟏 ∷ []) , cons-is-non-empty

three : List⁺ (Fin 3)
three = (𝟎 ∷ 𝟏 ∷ 𝟐 ∷ []) , cons-is-non-empty

wikipedia-nodes : structure Node wikipedia-tree
wikipedia-nodes = (maximizer , three)
               :: λ _ → (minimizer , two)
               :: λ _ → (maximizer , two)
               :: λ _ → (minimizer , three)
               :: λ _ → ⟨⟩

\end{code}

The outcome function q' of Section 2.2 of the paper. The outcomes
marked "can be pruned" are among those that the alpha-beta search does
not evaluate, and of the plays covered by a clause marked "can be
partially pruned", it evaluates some but not all.

\begin{code}

q : Path wikipedia-tree → ℕ
q (𝟎 , 𝟎 , 𝟎 , 𝟎 , ⟨⟩) = 5
q (𝟎 , 𝟎 , 𝟎 , _ , ⟨⟩) = 6
q (𝟎 , 𝟎 , 𝟏 , 𝟎 , ⟨⟩) = 7
q (𝟎 , 𝟎 , 𝟏 , 𝟏 , ⟨⟩) = 4
q (𝟎 , 𝟎 , 𝟏 , 𝟐 , ⟨⟩) = 5 -- can be pruned
q (𝟎 , 𝟏 , _ , _ , ⟨⟩) = 3 -- can be partially pruned
q (𝟏 , 𝟎 , 𝟎 , _ , ⟨⟩) = 6
q (𝟏 , 𝟎 , 𝟏 , 𝟎 , ⟨⟩) = 6
q (𝟏 , 𝟎 , 𝟏 , _ , ⟨⟩) = 9 -- can be pruned
q (𝟏 , 𝟏 , _ , _ , ⟨⟩) = 7 -- can be partially pruned
q (𝟐 , 𝟎 , _ , _ , ⟨⟩) = 5 -- can be partially pruned
q (𝟐 , _ , _ , _ , ⟨⟩) = 9 -- can be pruned
q (𝟎 , 𝟎 , 𝟏 , suc (suc (suc i)) , ⟨⟩) = 𝟘-elim (Fin-0-is-empty i)
q (𝟎 , 𝟎 , suc (suc i) , _ , ⟨⟩) = 𝟘-elim (Fin-0-is-empty i)
q (𝟎 , suc (suc i) , _ , _ , ⟨⟩) = 𝟘-elim (Fin-0-is-empty i)
q (𝟏 , 𝟎 , suc (suc i) , _ , ⟨⟩) = 𝟘-elim (Fin-0-is-empty i)
q (𝟏 , suc (suc i) , _ , _ , ⟨⟩) = 𝟘-elim (Fin-0-is-empty i)
q (suc (suc (suc i)) , _ , _ , _ , ⟨⟩) = 𝟘-elim (Fin-0-is-empty i)

\end{code}

The last six clauses make q total. Since Fin (succ n) is defined as
Fin n + 𝟙, Agda also asks for the cases suc (suc i) of Fin 2 and
suc (suc (suc i)) of Fin 3, with i in the empty type Fin 0.

The values of all outcomes lie strictly between 0 and 10, which we
use as the initial bounds of the alpha-beta search.

\begin{code}

q-bounds : (xs : Path wikipedia-tree) → (0 <ℕ q xs) × (q xs <ℕ 10)
q-bounds (i , j , k , l , ⟨⟩) = b i j k l
  where
   b : (i : Fin 3) (j : Fin 2) (k : Fin 2) (l : Fin 3)
     → (0 <ℕ q (i , j , k , l , ⟨⟩)) × (q (i , j , k , l , ⟨⟩) <ℕ 10)
   b 𝟎 𝟎 𝟎 𝟎 = ⋆ , ⋆
   b 𝟎 𝟎 𝟎 𝟏 = ⋆ , ⋆
   b 𝟎 𝟎 𝟎 𝟐 = ⋆ , ⋆
   b 𝟎 𝟎 𝟏 𝟎 = ⋆ , ⋆
   b 𝟎 𝟎 𝟏 𝟏 = ⋆ , ⋆
   b 𝟎 𝟎 𝟏 𝟐 = ⋆ , ⋆
   b 𝟎 𝟏 𝟎 𝟎 = ⋆ , ⋆
   b 𝟎 𝟏 𝟎 𝟏 = ⋆ , ⋆
   b 𝟎 𝟏 𝟎 𝟐 = ⋆ , ⋆
   b 𝟎 𝟏 𝟏 𝟎 = ⋆ , ⋆
   b 𝟎 𝟏 𝟏 𝟏 = ⋆ , ⋆
   b 𝟎 𝟏 𝟏 𝟐 = ⋆ , ⋆
   b 𝟏 𝟎 𝟎 𝟎 = ⋆ , ⋆
   b 𝟏 𝟎 𝟎 𝟏 = ⋆ , ⋆
   b 𝟏 𝟎 𝟎 𝟐 = ⋆ , ⋆
   b 𝟏 𝟎 𝟏 𝟎 = ⋆ , ⋆
   b 𝟏 𝟎 𝟏 𝟏 = ⋆ , ⋆
   b 𝟏 𝟎 𝟏 𝟐 = ⋆ , ⋆
   b 𝟏 𝟏 𝟎 𝟎 = ⋆ , ⋆
   b 𝟏 𝟏 𝟎 𝟏 = ⋆ , ⋆
   b 𝟏 𝟏 𝟎 𝟐 = ⋆ , ⋆
   b 𝟏 𝟏 𝟏 𝟎 = ⋆ , ⋆
   b 𝟏 𝟏 𝟏 𝟏 = ⋆ , ⋆
   b 𝟏 𝟏 𝟏 𝟐 = ⋆ , ⋆
   b 𝟐 𝟎 𝟎 𝟎 = ⋆ , ⋆
   b 𝟐 𝟎 𝟎 𝟏 = ⋆ , ⋆
   b 𝟐 𝟎 𝟎 𝟐 = ⋆ , ⋆
   b 𝟐 𝟎 𝟏 𝟎 = ⋆ , ⋆
   b 𝟐 𝟎 𝟏 𝟏 = ⋆ , ⋆
   b 𝟐 𝟎 𝟏 𝟐 = ⋆ , ⋆
   b 𝟐 𝟏 𝟎 𝟎 = ⋆ , ⋆
   b 𝟐 𝟏 𝟎 𝟏 = ⋆ , ⋆
   b 𝟐 𝟏 𝟎 𝟐 = ⋆ , ⋆
   b 𝟐 𝟏 𝟏 𝟎 = ⋆ , ⋆
   b 𝟐 𝟏 𝟏 𝟏 = ⋆ , ⋆
   b 𝟐 𝟏 𝟏 𝟐 = ⋆ , ⋆
   b (suc (suc (suc i))) j k l = 𝟘-elim (Fin-0-is-empty i)
   b i (suc (suc j)) k l = 𝟘-elim (Fin-0-is-empty j)
   b i j (suc (suc k)) l = 𝟘-elim (Fin-0-is-empty k)
   b i j k (suc (suc (suc l))) = 𝟘-elim (Fin-0-is-empty l)

q-is-above-0 : (xs : Path wikipedia-tree) → 0 <ℕ q xs
q-is-above-0 xs = pr₁ (q-bounds xs)

q-is-below-10 : (xs : Path wikipedia-tree) → q xs <ℕ 10
q-is-below-10 xs = pr₂ (q-bounds xs)

\end{code}

The exhaustive search and the alpha-beta search compute the optimal
outcome 6.

\begin{code}

import Games.AlphaBeta.ViaProductsOfQuantifiers

module E = Games.AlphaBeta.ViaProductsOfQuantifiers ℕ-order ℕ id

wikipedia-outcome : E.outcome wikipedia-tree wikipedia-nodes q ＝ 6
wikipedia-outcome = refl

wikipedia-outcome* : E.outcome* wikipedia-tree wikipedia-nodes q (0 , 10) ＝ 6
wikipedia-outcome* = refl

\end{code}

The alpha-beta search of the extended game computes the optimal
outcome together with the optimal play 1,0,0,0. At the node 1,0, the
two moves give outcomes with the same value 6, and the maximum keeps
the first of them.

\begin{code}

open import Games.AlphaBeta.OptimalPlays ℕ-order

wikipedia-αβ-outcome-and-play
 : αβ-outcome-and-play wikipedia-tree wikipedia-nodes q 0 10
 ＝ (6 , 𝟏 , 𝟎 , 𝟎 , 𝟎 , ⟨⟩)
wikipedia-αβ-outcome-and-play = refl

wikipedia-αβ-play-is-optimal
 : is-optimal-play
    (E.quantifier-tree wikipedia-nodes)
    q
    (play (αβ-outcome-and-play wikipedia-tree wikipedia-nodes q 0 10))
wikipedia-αβ-play-is-optimal =
 αβ-play-is-optimal wikipedia-tree wikipedia-nodes q 0 10
  q-is-above-0
  q-is-below-10

\end{code}

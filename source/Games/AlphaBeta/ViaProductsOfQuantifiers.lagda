Martin Escardo and Paulo Oliva, originally March - April 2023, with the
proofs November 2026.

Part of the formalization, in Games.AlphaBeta.index, of the paper

  Martín Hötzel Escardó and Paulo Oliva.
  Alpha-Beta Pruning via Monadic Continuations.

Correctness of the alpha-beta optimization (Theorem 1 of the paper).

A minimax game is given by a tree Xt of types of moves, as in the
module Games.TypeTrees, whose internal nodes are labelled by a
player, either the maximizer or the minimizer, together with a
non-empty list of the moves available at that node, and by an outcome
function q : Path Xt → R.

These are the games of Section 6.1 of the paper, in the generality of
the paper on games with dependent types cited there: the type of moves
at a round, and the number of rounds, may depend on the moves played
so far, and the player at each node is independent of the other
nodes.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import OrderedTypes.DecidableStrictWeakOrder

module Games.AlphaBeta.ViaProductsOfQuantifiers
        {𝓤 𝓣 : Universe}
        {V : 𝓤 ̇ }
        (O : Decidable-Strict-Weak-Order V 𝓣)
        (R : 𝓤 ̇ )
        (val : R → V)
       where

open import Games.AlphaBeta.Player public
open import Games.AlphaBeta.Minimizer O R val
open import Games.TypeTrees {𝓤}
open import MonadOnTypes.Definition using (η)
open import MonadOnTypes.K
open import MonadOnTypes.Reader

import Games.FiniteHistoryDependent

module G  = Games.FiniteHistoryDependent {𝓤} {𝓤} R
module G* = Games.FiniteHistoryDependent {𝓤} {𝓤} (T R)

open Decidable-Strict-Weak-Order O
open K-definitions {𝓤} {R} using (K)

\end{code}

The quantifiers and their alpha-beta versions.

\begin{code}

quantifier : {X : 𝓤 ̇ } → Node X → K X
quantifier (maximizer , xs) = φmax xs
quantifier (minimizer , xs) = φmin xs

quantifier* : {X : 𝓤 ̇ } → Node X → (X → T R) → T R
quantifier* (maximizer , xs) = φ*max xs
quantifier* (minimizer , xs) = φ*min xs

quantifier-tree : {Xt : 𝑻} → structure Node Xt → G.𝓚 Xt
quantifier-tree {[]}     ⟨⟩        = ⟨⟩
quantifier-tree {X ∷ Xf} (n :: nf) =
 quantifier n :: (λ x → quantifier-tree (nf x))

quantifier*-tree : {Xt : 𝑻} → structure Node Xt → G*.𝓚 Xt
quantifier*-tree {[]}     ⟨⟩        = ⟨⟩
quantifier*-tree {X ∷ Xf} (n :: nf) =
 quantifier* n :: (λ x → quantifier*-tree (nf x))

\end{code}

The game G and its monadic version G*, which performs the alpha-beta
optimization, and their optimal outcomes out(G) and out*(G*), the
latter as a function of the bounds (α , β). The outcome function of
G* is the composition of q with the unit of the reader monad.

\begin{code}

module _ (Xt : 𝑻)
         (nt : structure Node Xt)
         (q  : Path Xt → R)
       where

 G : G.Game
 G = G.game Xt q (quantifier-tree nt)

 G* : G*.Game
 G* = G*.game Xt (η (Reader (V × V)) ∘ q) (quantifier*-tree nt)

 outcome : R
 outcome = G.optimal-outcome G

 outcome* : V × V → R
 outcome* = G*.optimal-outcome G*

\end{code}

The induction step of the proof of Theorem 1 applies to both players.

\begin{code}

quantifier-is-αβ-approximated-by-quantifier*
 : {X : 𝓤 ̇ }
   (n  : Node X)
   (p  : X → R)
   (p* : X → T R)
 → ((x : X) → (p x) is-αβ-approximated-by (p* x))
 → (quantifier n p) is-αβ-approximated-by (quantifier* n p*)
quantifier-is-αβ-approximated-by-quantifier* (maximizer , xs) p p* h =
 φmax-is-αβ-approximated-by-φ*max p p* h xs
quantifier-is-αβ-approximated-by-quantifier* (minimizer , xs) p p* h =
 φmin-is-αβ-approximated-by-φ*min p p* h xs

\end{code}

Theorem 1 of the paper. For all bounds α and β,

 (i)   out(G) ≤ α implies out*(G*)(α , β) ≤ α,
 (ii)  out(G) ≥ β implies out*(G*)(α , β) ≥ β,
 (iii) α < out(G) < β implies out*(G*)(α , β) = out(G),

where the inequalities compare values under val, and the equation in
(iii) is an equation of outcomes. The proof is by induction on the
game tree.

\begin{code}

theorem : (Xt : 𝑻)
          (nt : structure Node Xt)
          (q  : Path Xt → R)
        → (outcome Xt nt q) is-αβ-approximated-by (outcome* Xt nt q)
theorem []       ⟨⟩        q = λ α β → id , id , (λ _ _ → refl)
theorem (X ∷ Xf) (n :: nf) q     =
 quantifier-is-αβ-approximated-by-quantifier* n
  (λ x → outcome  (Xf x) (nf x) (subpred q x))
  (λ x → outcome* (Xf x) (nf x) (subpred q x))
  (λ x → theorem (Xf x) (nf x) (subpred q x))

\end{code}

The outcome out(G) has every property that all the outcomes q(xs)
have, since it is one of them.

\begin{code}

quantifier-preserves : {X : 𝓤 ̇ } (Q : R → 𝓦 ̇ ) (n : Node X) (p : X → R)
                     → ((x : X) → Q (p x))
                     → Q (quantifier n p)
quantifier-preserves Q (maximizer , xs) = Max.φmax-preserves Q xs
quantifier-preserves Q (minimizer , xs) = Min.φmax-preserves Q xs

quantifier-is-attained : {X : 𝓤 ̇ } (n : Node X) (p : X → R)
                       → Σ x ꞉ X , quantifier n p ＝ p x
quantifier-is-attained (maximizer , xs) = Max.φmax-is-attained xs
quantifier-is-attained (minimizer , xs) = Min.φmax-is-attained xs

outcome-preserves : (Q : R → 𝓦 ̇ )
                    (Xt : 𝑻)
                    (nt : structure Node Xt)
                    (q  : Path Xt → R)
                  → ((xs : Path Xt) → Q (q xs))
                  → Q (outcome Xt nt q)
outcome-preserves Q []       ⟨⟩        q a = a ⟨⟩
outcome-preserves Q (X ∷ Xf) (n :: nf) q a =
 quantifier-preserves Q n
  (λ x → outcome (Xf x) (nf x) (subpred q x))
  (λ x → outcome-preserves Q (Xf x) (nf x) (subpred q x) (λ xs → a (x :: xs)))

\end{code}

Hence, if the values of all outcomes lie strictly between two bounds
-∞ and ∞, the alpha-beta search started with these bounds computes
the optimal outcome of the game.

\begin{code}

corollary : (Xt : 𝑻)
            (nt : structure Node Xt)
            (q  : Path Xt → R)
            (-∞ ∞ : V)
          → ((xs : Path Xt) → -∞ < val (q xs))
          → ((xs : Path Xt) → val (q xs) < ∞)
          → outcome* Xt nt q (-∞ , ∞) ＝ outcome Xt nt q
corollary Xt nt q -∞ ∞ a b =
 αβ-approximation-exact (theorem Xt nt q) -∞ ∞
  (outcome-preserves (λ r → -∞ < val r) Xt nt q a)
  (outcome-preserves (λ r → val r < ∞) Xt nt q b)

\end{code}

If the outcome computed by the alpha-beta search lies strictly between
the bounds, then it is the optimal outcome.

\begin{code}

corollary' : (Xt : 𝑻)
             (nt : structure Node Xt)
             (q  : Path Xt → R)
             (α β : V)
           → α < val (outcome* Xt nt q (α , β))
           → val (outcome* Xt nt q (α , β)) < β
           → outcome* Xt nt q (α , β) ＝ outcome Xt nt q
corollary' Xt nt q α β a b = αβ-approximation-exact h α β a' b'
 where
  h = theorem Xt nt q

  a' : α < val (outcome Xt nt q)
  a' = Cases (<-decidable α (val (outcome Xt nt q)))
        id
        (λ (n : val (outcome Xt nt q) ≤ α) →
          𝟘-elim (αβ-approximation-at-most-α h α β n a))

  b' : val (outcome Xt nt q) < β
  b' = Cases (<-decidable (val (outcome Xt nt q)) β)
        id
        (λ (n : β ≤ val (outcome Xt nt q)) →
          𝟘-elim (αβ-approximation-at-least-β h α β n b))

\end{code}

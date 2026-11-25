Martin Escardo and Paulo Oliva, November 2026.

This is an Agda companion for the paper

   Alpha-Beta Pruning via Monadic Continuations
   --------------------------------------------

   Martín Hötzel Escardó and Paulo Oliva
   https://doi.org/10.48550/arXiv.2611.32320

This file follows the definitions, lemmas and theorems of the paper
above, in the same order and with the same numbering, including the
claims made in its prose, so that a reader of the paper can walk this
file alongside it. The name of each entry is the number the item has
in the paper, and the comment before it is the LaTeX label of that
item.

The main theorems of the paper are stated in the module
Games.AlphaBeta.Summary, which displays every definition that their
statements use.

Claims that the paper makes in running prose, outside proofs, appear
here too, under names beginning with Prose. Each of them is named in
the LaTeX source by \claim{name}, placed where the claim is made, and
the names are written out in order to the file
alpha-beta-pruning.claims when the paper is typeset, so that the two
lists can be compared. Claims about the number of plays evaluated and
about the order in which outcomes are evaluated are recorded as
comments, since they are not formalizable here.

As in Section 4 of the paper, values form a type V with a decidable
strict weak order, and outcomes form a type R with a valuation
val : R → V. These are the parameters of this module. The examples
here take V = ℕ. In Sections 2 to 4 of the paper, R = V and val is the
identity, and in Section 5, where outcomes are pairs of a value and a
play, R = V × Path Xt and val is the first projection. A game is
given by a tree of types of moves, as in the module Games.TypeTrees,
whose internal nodes are labelled by either player. These are the
history-dependent games of Section 6.1 of the paper, in the generality
of the paper on games with dependent types cited there.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import OrderedTypes.DecidableStrictWeakOrder
open import MLTT.List-Properties

module Games.AlphaBeta.Article
        {𝓤 𝓣 : Universe}
        {V : 𝓤 ̇ }
        (O : Decidable-Strict-Weak-Order V 𝓣)
        (R : 𝓤 ̇ )
        (val : R → V)
       where

open import Games.TypeTrees {𝓤}
open import MLTT.Fin using (𝟎 ; 𝟏)
open import MLTT.List
open import MonadOnTypes.NonEmptyList using (List⁺ ; underlying-list⁺)

open import Games.AlphaBeta.Player
open import Games.AlphaBeta.Maximizer O R val
open import Games.AlphaBeta.Minimizer O R val
 using (φmin ; φ*min ; swap ; module Min ; φmin-is-αβ-approximated-by-φ*min)
open import Games.AlphaBeta.ViaProductsOfQuantifiers O R val
 using (outcome ; outcome* ; theorem ; corollary ; corollary' ;
        quantifier-is-αβ-approximated-by-quantifier*)

import Games.AlphaBeta.ViaProductsOfQuantifiers
import Games.AlphaBeta.Examples
import Games.AlphaBeta.OptimalPlays
import Games.OptimalPlays

open Decidable-Strict-Weak-Order O
open Decidable-Strict-Weak-Order (opposite O) using () renaming (_≤_ to _≤ᵒᵖ_)

\end{code}

Section 1. Introduction.

The introduction displays the type K_R X ≡ (X → R) → R of the
continuation monad, whose elements are called quantifiers, which is K
in the module MonadOnTypes.K, and the reader monad T X = R × R → X,
which is T in the module Games.AlphaBeta.Maximizer, with V × V in place
of R × R, as in Section 4 of the paper.

Contribution (2) of the introduction: the alpha-beta search computes
the same optimal outcome as the exhaustive search. This is
Corollary 1 below.

\begin{code}

-- claim same-optimal-outcome
Prose-same-optimal-outcome
 : (Xt : 𝑻)
   (nt : structure Node Xt)
   (q  : Path Xt → R)
   (-∞ ∞ : V)
 → ((xs : Path Xt) → -∞ < val (q xs))
 → ((xs : Path Xt) → val (q xs) < ∞)
 → outcome* Xt nt q (-∞ , ∞) ＝ outcome Xt nt q
Prose-same-optimal-outcome = corollary

\end{code}

Contribution (3) of the introduction: the continuation monad computes
optimal plays when the type of outcomes is extended to include the
play that leads to the outcome. The game here has outcomes in V, and
the extended game has outcomes in V × Path Xt, compared by their first
components, and outcome function q' xs = (q xs , xs). The second
component of the optimal outcome of the extended game is an optimal
play of the original game, in the sense of the module
Games.OptimalPlays. The same holds for the alpha-beta search, by the
entry Prose-alpha-beta-optimal-play below.

\begin{code}

module _ (Xt : 𝑻)
         (nt : structure Node Xt)
         (q  : Path Xt → V)
       where

 open import Games.OptimalPlays {𝓤} {𝓤} V using (is-optimal-play)
 open Games.AlphaBeta.OptimalPlays O
  using (value ; play ; q' ; optimal-play-of-extended-game)

 -- claim optimal-plays-via-outcomes
 Prose-optimal-plays-via-outcomes
  : is-optimal-play
     (Games.AlphaBeta.ViaProductsOfQuantifiers.quantifier-tree O V id nt)
     q
     (play (Games.AlphaBeta.ViaProductsOfQuantifiers.outcome
             O (V × Path Xt) value Xt nt (q' Xt nt q)))
 Prose-optimal-plays-via-outcomes = optimal-play-of-extended-game Xt nt q

\end{code}

Section 2. Exhaustive search via the continuation monad.

The game tree of Section 2.2 is Games.AlphaBeta.Examples.wikipedia-tree,
with nodes labelled by Games.AlphaBeta.Examples.wikipedia-nodes, and
outcome function Games.AlphaBeta.Examples.q. The Haskell quantifiers
phiMax and phiMin of Section 2.1 are φmax and φmin, and the Haskell
global quantifier bigPhi of Section 2.3 is
Games.AlphaBeta.ViaProductsOfQuantifiers.quantifier-tree, sequenced by
sequenceᴷ of the module Games.FiniteHistoryDependent, which is the
product of quantifiers of Remark 1.

The claim at the end of Section 2 is that the exhaustive search
computes the optimal outcome 6 of the example. That all 36 plays are
explored is a claim about the evaluation of the Haskell program, and
is not formalized.

\begin{code}

-- claim exhaustive-outcome
Prose-exhaustive-outcome
 : Games.AlphaBeta.ViaProductsOfQuantifiers.outcome
    Games.AlphaBeta.Examples.ℕ-order ℕ id
    Games.AlphaBeta.Examples.wikipedia-tree
    Games.AlphaBeta.Examples.wikipedia-nodes
    Games.AlphaBeta.Examples.q
 ＝ 6
Prose-exhaustive-outcome = Games.AlphaBeta.Examples.wikipedia-outcome

\end{code}

Section 3. Adding alpha-beta pruning via the reader monad.

The Haskell quantifiers phiMax and phiMin of Section 3.1 are φ*max and
φ*min, and the global quantifier of Section 3.2 is
Games.AlphaBeta.ViaProductsOfQuantifiers.quantifier*-tree.

The claim at the end of Section 3 is that the alpha-beta search,
started with the bounds 0 and 10, computes the optimal outcome 6 of
the example. The Haskell code uses the bounds -1000 and 1000, which
aren't natural numbers. That only 18 plays are considered is a claim
about the evaluation of the Haskell program, and is not formalized.

\begin{code}

-- claim alpha-beta-outcome
Prose-alpha-beta-outcome
 : Games.AlphaBeta.ViaProductsOfQuantifiers.outcome*
    Games.AlphaBeta.Examples.ℕ-order ℕ id
    Games.AlphaBeta.Examples.wikipedia-tree
    Games.AlphaBeta.Examples.wikipedia-nodes
    Games.AlphaBeta.Examples.q
    (0 , 10)
 ＝ 6
Prose-alpha-beta-outcome = Games.AlphaBeta.Examples.wikipedia-outcome*

\end{code}

Section 4. Correctness of alpha-beta optimization.

The quantifiers φ_min, φ_max, φ*_min and φ*_max are φmin, φmax, φ*min
and φ*max, the product of quantifiers is sequenceᴷ, as in Remark 1,
and the outcomes out(G) and out*_{α,β}(G) are outcome and outcome*, as
functions of the game tree, its labelling and the outcome function.
For a subgame G_s, the outcome function q_s is subpred q x of the
module Games.TypeTrees, for a single move x, and repeated for longer
partial plays.

Definition 1. The function ℓ, the function takeUntil, which is
take-until here, and the maximum max⁺ of a non-empty list. The maximum
keeps the first of two outcomes with the same value, which matters for
Section 5. The function φ*min is defined from φ*max for the opposite
order, with the bounds swapped.

\begin{code}

-- def-alpha-beta-quantifiers
Definition-1 : {X : 𝓤 ̇ } → List⁺ X → (X → T R) → T R
Definition-1 = φ*max

Definition-1-ℓ : {X : 𝓤 ̇ } → (X → T R) → List X → T (List R)
Definition-1-ℓ = ℓ

Definition-1-take-until : {A : 𝓤 ̇ } (P : A → 𝓦 ̇ )
                        → ((a : A) → is-decidable (P a))
                        → List A → List A
Definition-1-take-until = take-until

Definition-1-max : List⁺ R → R
Definition-1-max = max⁺

Definition-1-min : {X : 𝓤 ̇ } → List⁺ X → (X → T R) → T R
Definition-1-min = φ*min

\end{code}

The claim that dual results hold for φ*min. By Definition 1, every
result about φ*max gives a result about φ*min. In particular, the
induction step of the proof of Theorem 1 for the maximizing player
gives the induction step for the minimizing player.

\begin{code}

-- claim min-dual-to-max
Prose-min-dual-to-max : {X : 𝓤 ̇ } (xs : List⁺ X) (p : X → T R) (α β : V)
                      → φ*min xs p (α , β)
                      ＝ Min.φ*max xs (λ x → p x ∘ swap) (β , α)
Prose-min-dual-to-max xs p α β = refl

Prose-min-dual-to-max'
 : {X : 𝓤 ̇ }
   (p  : X → R)
   (p* : X → T R)
 → ((x : X) → (p x) is-αβ-approximated-by (p* x))
 → (xs : List⁺ X) → (φmin xs p) is-αβ-approximated-by (φ*min xs p*)
Prose-min-dual-to-max' = φmin-is-αβ-approximated-by-φ*min

\end{code}

Lemma 1. The list αs p β α xs pairs each member xᵢ of xs with αᵢ,
which is α for i = 0, and max(αᵢ₋₁ , val(p(xᵢ₋₁)(αᵢ₋₁ , β))) otherwise,
as defined before Lemma 1 in the paper.

\begin{code}

-- lemma-alpha-list
Lemma-1 : {X : 𝓤 ̇ } (p : X → T R) (xs : List X) (α β : V)
        → ℓ p xs (α , β) ＝ map (λ (x , a) → p x (a , β)) (αs p β α xs)
Lemma-1 = ℓ-characterization

\end{code}

Lemma 2. In (ii), "for some i" is formulated as membership of the pair
(xᵢ , αᵢ) in the list αs p β α xs.

\begin{code}

-- main-lemma (i)
Lemma-2-i : {X : 𝓤 ̇ }
            (p : X → T R)
            (α β : V)
            (xs : List X)
          → All (λ x → val (p x (α , β)) ≤ α) xs
          → All (λ (_ , a) → a ＝ α) (αs p β α xs)
Lemma-2-i = all-αs-are-α

Lemma-2-i' : {X : 𝓤 ̇ }
             (p : X → T R)
             (α β : V)
             (xs : List⁺ X)
           → All (λ x → val (p x (α , β)) ≤ α) (underlying-list⁺ xs)
           → val (φ*max xs p (α , β)) ≤ α
Lemma-2-i' = φ*max-is-at-most-α

-- main-lemma (ii)
Lemma-2-ii : {X : 𝓤 ̇ }
             (p : X → T R)
             (α β : V)
             (xs : List⁺ X)
             (x : X)
             (a : V)
           → member (x , a) (αs p β α (underlying-list⁺ xs))
           → β ≤ val (p x (a , β))
           → β ≤ val (φ*max xs p (α , β))
Lemma-2-ii = φ*max-is-at-least-β

\end{code}

The claim that the dual lemmas hold for φ*min and a sequence βᵢ.
These are Lemmas 1 and 2 for the opposite order, where β plays the
role of α, as in the entry Prose-min-dual-to-max above.

\begin{code}

-- claim dual-lemmas
Prose-dual-lemmas : {X : 𝓤 ̇ } (p : X → T R) (xs : List X) (β α : V)
                  → Min.ℓ p xs (β , α)
                  ＝ map (λ (x , b) → p x (b , α)) (Min.αs p α β xs)
Prose-dual-lemmas = Min.ℓ-characterization

Prose-dual-lemmas' : {X : 𝓤 ̇ }
                     (p : X → T R)
                     (β α : V)
                     (xs : List X)
                   → All (λ x → val (p x (β , α)) ≤ᵒᵖ β) xs
                   → All (λ (_ , b) → b ＝ β) (Min.αs p α β xs)
Prose-dual-lemmas' = Min.all-αs-are-α

Prose-dual-lemmas'' : {X : 𝓤 ̇ }
                      (p : X → T R)
                      (β α : V)
                      (xs : List⁺ X)
                    → All (λ x → val (p x (β , α)) ≤ᵒᵖ β)
                          (underlying-list⁺ xs)
                    → val (Min.φ*max xs p (β , α)) ≤ᵒᵖ β
Prose-dual-lemmas'' = Min.φ*max-is-at-most-α

Prose-dual-lemmas''' : {X : 𝓤 ̇ }
                       (p : X → T R)
                       (β α : V)
                       (xs : List⁺ X)
                       (x : X)
                       (b : V)
                     → member (x , b)
                        (Min.αs p α β (underlying-list⁺ xs))
                     → α ≤ᵒᵖ val (p x (b , α))
                     → α ≤ᵒᵖ val (Min.φ*max xs p (β , α))
Prose-dual-lemmas''' = Min.φ*max-is-at-least-β

\end{code}

Theorem 1. The theorem is stated for every game, and so in particular
for every subgame G_s. The inequalities compare values under val, and
the equation of (iii) is an equation of outcomes. The relation
_is-αβ-approximated-by_ of the module Games.AlphaBeta.Maximizer collects
the three clauses.

\begin{code}

module _ (Xt : 𝑻)
         (nt : structure Node Xt)
         (q  : Path Xt → R)
         (α β : V)
       where

 -- thm-main (i)
 Theorem-1-i : val (outcome Xt nt q) ≤ α → val (outcome* Xt nt q (α , β)) ≤ α
 Theorem-1-i = αβ-approximation-at-most-α (theorem Xt nt q) α β

 -- thm-main (ii)
 Theorem-1-ii : β ≤ val (outcome Xt nt q) → β ≤ val (outcome* Xt nt q (α , β))
 Theorem-1-ii = αβ-approximation-at-least-β (theorem Xt nt q) α β

 -- thm-main (iii)
 Theorem-1-iii : α < val (outcome Xt nt q)
               → val (outcome Xt nt q) < β
               → outcome* Xt nt q (α , β) ＝ outcome Xt nt q
 Theorem-1-iii = αβ-approximation-exact (theorem Xt nt q) α β

\end{code}

Corollary 1. Part (a) is the corollary of the module
Games.AlphaBeta.ViaProductsOfQuantifiers, whose proof uses that out(G)
is one of the values of q, which is outcome-preserves there.

\begin{code}

module _ (Xt : 𝑻)
         (nt : structure Node Xt)
         (q  : Path Xt → R)
         (α β : V)
       where

 -- cor-bounds (a)
 Corollary-1-a : ((t : Path Xt) → α < val (q t))
               → ((t : Path Xt) → val (q t) < β)
               → outcome* Xt nt q (α , β) ＝ outcome Xt nt q
 Corollary-1-a = corollary Xt nt q α β

 -- cor-bounds (b)
 Corollary-1-b : α < val (outcome* Xt nt q (α , β))
               → val (outcome* Xt nt q (α , β)) < β
               → outcome* Xt nt q (α , β) ＝ outcome Xt nt q
 Corollary-1-b = corollary' Xt nt q α β

\end{code}

The proof of Theorem 1 is by induction on the game tree, and the induction step,
for either player, is the following.

\begin{code}

Theorem-1-induction-step
 : {X : 𝓤 ̇ }
   (n  : Node X)
   (p  : X → R)
   (p* : X → T R)
 → ((x : X) → (p x) is-αβ-approximated-by (p* x))
 → (Games.AlphaBeta.ViaProductsOfQuantifiers.quantifier O R val n p)
   is-αβ-approximated-by
   (Games.AlphaBeta.ViaProductsOfQuantifiers.quantifier* O R val n p*)
Theorem-1-induction-step = quantifier-is-αβ-approximated-by-quantifier*

\end{code}

For the maximizing player, the three cases of the proof in the paper
are part₁, part₂ and part₃ of the module Games.AlphaBeta.Maximizer,
where y ∷ ys is the list of moves at the position, p gives the optimal
outcomes of the subgames, and p* their monadic outcomes. Case (i)
applies Lemma 2(i), that is, Lemma-2-i' above, and case (ii) applies
Lemma 2(ii), that is, Lemma-2-ii. Case (iii) is by induction on the list
of moves, with k the index at which the maximum is attained first. The
case of the minimizing player is dual, by the entry
Prose-min-dual-to-max'.

\begin{code}

module _ {X : 𝓤 ̇ }
         (p  : X → R)
         (p* : X → T R)
         (h  : (x : X) → (p x) is-αβ-approximated-by (p* x))
         (β : V)
         (ys : List X)
         (y : X)
         (α : V)
       where

 private
  xs : List⁺ X
  xs = (y ∷ ys) , cons-is-non-empty

 Theorem-1-case-i : val (φmax xs p) ≤ α → val (φ*max xs p* (α , β)) ≤ α
 Theorem-1-case-i = part₁ p p* h β ys y α

 Theorem-1-case-ii : β ≤ val (φmax xs p) → β ≤ val (φ*max xs p* (α , β))
 Theorem-1-case-ii = part₂ p p* h β ys y α

 Theorem-1-case-iii : α < val (φmax xs p)
                    → val (φmax xs p) < β
                    → φ*max xs p* (α , β) ＝ φmax xs p
 Theorem-1-case-iii = part₃ p p* h β ys y α

\end{code}

Section 5. Computing optimal plays.

The extended type of outcomes is V × Path Xt, the extended outcome
function is Games.AlphaBeta.OptimalPlays.q', and the modified Haskell
quantifier phiMax is φ*max for the valuation
Games.AlphaBeta.OptimalPlays.value, the first projection. The Haskell
function pickMax corresponds to max⁺, which also keeps the first of
two outcomes with the same value.

Definition 2 and Corollary 2. The values are the outcomes of the
original game, so that its valuation is the identity, and the extended
game has outcomes in V × Path Xt with valuation the first projection.

\begin{code}

module _ (Xt : 𝑻)
         (nt : structure Node Xt)
         (q  : Path Xt → V)
       where

 open import Games.OptimalPlays {𝓤} {𝓤} V using (is-optimal-play)
 open Games.AlphaBeta.OptimalPlays O
  using (value ; q' ; extended-game-gives-optimal-play ;
         αβ-search-agrees-with-exhaustive-search)

 private
  outcome₀ : V
  outcome₀ = Games.AlphaBeta.ViaProductsOfQuantifiers.outcome O V id Xt nt q

 -- def-optimal-play
 Definition-2 : Path Xt → 𝓤 ̇
 Definition-2 =
  is-optimal-play
   (Games.AlphaBeta.ViaProductsOfQuantifiers.quantifier-tree O V id nt) q

 -- cor-optimal-plays
 Corollary-2
  : Σ t ꞉ Path Xt , (Games.AlphaBeta.ViaProductsOfQuantifiers.outcome
                      O (V × Path Xt) value Xt nt (q' Xt nt q)
                     ＝ (outcome₀ , t))
                  × Definition-2 t
 Corollary-2 = extended-game-gives-optimal-play Xt nt q

 Corollary-2'
  : (α β : V)
  → α < outcome₀
  → outcome₀ < β
  → Games.AlphaBeta.ViaProductsOfQuantifiers.outcome* O (V × Path Xt) value
     Xt nt (q' Xt nt q) (α , β)
  ＝ Games.AlphaBeta.ViaProductsOfQuantifiers.outcome O (V × Path Xt) value
     Xt nt (q' Xt nt q)
 Corollary-2' = αβ-search-agrees-with-exhaustive-search Xt nt q

\end{code}

The claim of Section 5 is that the alpha-beta search of the extended
game computes the optimal outcome of the original game together with
an optimal play.

\begin{code}

module _ (Xt : 𝑻)
         (nt : structure Node Xt)
         (q  : Path Xt → V)
         (-∞ ∞ : V)
         (a : (xs : Path Xt) → -∞ < q xs)
         (b : (xs : Path Xt) → q xs < ∞)
       where

 open import Games.OptimalPlays {𝓤} {𝓤} V using (is-optimal-play)
 open Games.AlphaBeta.OptimalPlays O
  using (value ; play ; αβ-outcome-and-play ; αβ-outcome-is-optimal ;
         αβ-play-is-optimal)

 -- claim alpha-beta-optimal-play
 Prose-alpha-beta-optimal-play
  : value (αβ-outcome-and-play Xt nt q -∞ ∞)
  ＝ Games.AlphaBeta.ViaProductsOfQuantifiers.outcome O V id Xt nt q
 Prose-alpha-beta-optimal-play = αβ-outcome-is-optimal Xt nt q -∞ ∞ a b

 Prose-alpha-beta-optimal-play'
  : is-optimal-play
     (Games.AlphaBeta.ViaProductsOfQuantifiers.quantifier-tree O V id nt)
     q
     (play (αβ-outcome-and-play Xt nt q -∞ ∞))
 Prose-alpha-beta-optimal-play' = αβ-play-is-optimal Xt nt q -∞ ∞ a b

\end{code}

For the example of Section 2, the alpha-beta search of the extended
game computes the outcome 6 and the play 1,0,0,0. The Haskell code of
Section 5 of the paper computes the same. Correctness of plays depends
on the Haskell function pickMax keeping the first of two outcomes with
the same value. If it keeps the last one instead, an outcome returned
by a pruned subgame, whose value is only a bound for the value of the
subgame, can displace an earlier outcome of the same value, and the
alpha-beta search can then return a play that isn't optimal.

\begin{code}

-- claim alpha-beta-optimal-play-example
Prose-alpha-beta-optimal-play-example
 : Games.AlphaBeta.OptimalPlays.αβ-outcome-and-play
    Games.AlphaBeta.Examples.ℕ-order
    Games.AlphaBeta.Examples.wikipedia-tree
    Games.AlphaBeta.Examples.wikipedia-nodes
    Games.AlphaBeta.Examples.q
    0 10
 ＝ (6 , 𝟏 , 𝟎 , 𝟎 , 𝟎 , ⟨⟩)
Prose-alpha-beta-optimal-play-example =
 Games.AlphaBeta.Examples.wikipedia-αβ-outcome-and-play

module OP₀ = Games.OptimalPlays {𝓤₀} {𝓤₀} ℕ

Prose-alpha-beta-optimal-play-example'
 : OP₀.is-optimal-play
    (Games.AlphaBeta.ViaProductsOfQuantifiers.quantifier-tree
      Games.AlphaBeta.Examples.ℕ-order ℕ id
      Games.AlphaBeta.Examples.wikipedia-nodes)
    Games.AlphaBeta.Examples.q
    (Games.AlphaBeta.OptimalPlays.play Games.AlphaBeta.Examples.ℕ-order
      (Games.AlphaBeta.OptimalPlays.αβ-outcome-and-play
        Games.AlphaBeta.Examples.ℕ-order
        Games.AlphaBeta.Examples.wikipedia-tree
        Games.AlphaBeta.Examples.wikipedia-nodes
        Games.AlphaBeta.Examples.q
        0 10))
Prose-alpha-beta-optimal-play-example' =
 Games.AlphaBeta.Examples.wikipedia-αβ-play-is-optimal

\end{code}

Section 6. History-dependent games.

Section 6.1. The games of this formalization are the history-dependent
games of Section 6.1 of the paper, in the generality of the paper on
games with dependent types, as explained at the beginning of this
file, and Theorem 1 and Corollaries 1 and 2 are proved above for all
such games.

Section 6.2. Alpha-beta search of Tic-Tac-Toe.

The Tic-Tac-Toe game is not formalized here. The module
deprecated.alpha-beta has a version of it, and its optimal outcome is
too expensive to compute by type checking. The claim that the
alpha-beta search evaluates the outcome function on only 9 335 of the
362 880 full plays, about 39 times fewer, is about the Haskell
programs, and is not formalized here. The bounds -1 and 1 used for
Tic-Tac-Toe are justified by Corollary 1(b), which is
Games.AlphaBeta.ViaProductsOfQuantifiers.corollary', and which needs
no bounds on the outcomes of the outcome function.

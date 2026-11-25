Martin Escardo and Paulo Oliva, November 2026.

The main theorems of the paper

  Martín Hötzel Escardó and Paulo Oliva.
  Alpha-Beta Pruning via Monadic Continuations.
  https://doi.org/10.48550/arXiv.2611.32320

This file states the main theorems, Theorem 1 and Corollaries 1 and 2
of the paper, and displays every definition that their statements use.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import OrderedTypes.DecidableStrictWeakOrder
open import MLTT.List-Properties

module Games.AlphaBeta.Summary
        {𝓤 𝓣 : Universe}
        {V : 𝓤 ̇ }
        (O : Decidable-Strict-Weak-Order V 𝓣)
        (R : 𝓤 ̇ )
        (val : R → V)
       where

open import Games.TypeTrees {𝓤}
open import MLTT.List
open import MonadOnTypes.NonEmptyList
 using (List⁺ ; underlying-list⁺ ; underlying-list⁺-is-non-empty)

open import Games.AlphaBeta.Player
open import Games.AlphaBeta.Maximizer O R val
open import Games.AlphaBeta.Minimizer O R val
 using (φmin ; φ*min ; swap ; module Min)
open import Games.AlphaBeta.ViaProductsOfQuantifiers O R val
 using (quantifier ; quantifier* ; quantifier-tree ; quantifier*-tree ;
        outcome ; outcome* ; theorem ; corollary ; corollary')

import Games.AlphaBeta.ViaProductsOfQuantifiers
import Games.AlphaBeta.OptimalPlays

open Decidable-Strict-Weak-Order O

\end{code}

1. Values.

Values form a type V with a relation _<_, and outcomes form a type R
with a valuation val : R → V. The paper takes V = R and val the identity
in Sections 2 to 4, and in Section 5 it takes R = V × Path, with val the
first projection. The relation _<_ is assumed to be decidable,
irreflexive, transitive and cotransitive, which is to say a decidable
strict weak order, as in Section 4 of the paper.

\begin{code}

_ : (a b : V) → is-decidable (a < b)
_ = <-decidable

_ : (a : V) → ¬ (a < a)
_ = <-irreflexive

_ : (a b c : V) → a < b → b < c → a < c
_ = <-transitive

_ : (a b c : V) → a < b → (a < c) + (c < b)
_ = <-cotransitive

\end{code}

We write a ≤ b for ¬ (b < a), and max is the binary maximum, keeping
the left argument in case of a tie.

\begin{code}

_ : (a b : V) → (a ≤ b) ＝ ¬ (b < a)
_ = λ a b → refl

_ : (a b : V) (l : a < b)     → maxδ a b (inl l) ＝ b
_ = λ a b l → refl

_ : (a b : V) (n : ¬ (a < b)) → maxδ a b (inr n) ＝ a
_ = λ a b n → refl

_ : (a b : V) → max a b ＝ maxδ a b (<-decidable a b)
_ = λ a b → refl

\end{code}

2. The quantifiers.

The maximum r ⊔ᴿ s of two outcomes compares their values and keeps
the left argument in case of a tie, as the Haskell function pickMax of
Appendix A of the paper does, and maxˡ r rs is the maximum of the
non-empty list r ∷ rs, which is therefore its first element of largest
value.

\begin{code}

_ : (r s : R) (l : val r < val s)     → maxᴿδ r s (inl l) ＝ s
_ = λ r s l → refl

_ : (r s : R) (n : ¬ (val r < val s)) → maxᴿδ r s (inr n) ＝ r
_ = λ r s n → refl

_ : (r s : R) → r ⊔ᴿ s ＝ maxᴿδ r s (<-decidable (val r) (val s))
_ = λ r s → refl

_ : (r : R) → maxˡ r [] ＝ r
_ = λ r → refl

_ : (r s : R) (ss : List R) → maxˡ r (s ∷ ss) ＝ r ⊔ᴿ maxˡ s ss
_ = λ r s ss → refl

\end{code}

A list of moves is a non-empty list, that is, an element of
List⁺ X = Σ xs ꞉ List X , is-non-empty xs, written [X]⁺ in the paper.
The exhaustive quantifier φmax of Section 2.1 of the paper computes the
maximum of p over the list of moves.

\begin{code}

_ : {X : 𝓤 ̇ } (x : X) (xs : List X) (p : X → R)
  → φmax ((x ∷ xs) , cons-is-non-empty) p ＝ maxˡ (p x) (map p xs)
_ = λ x xs p → refl

\end{code}

The reader monad T, the function ℓ and the function takeUntil of
Definition 1 of the paper, which is take-until here, and the
alpha-beta quantifier φ*max of Definition 1, where "≥ β" is the
predicate λ r → β ≤ val r.

\begin{code}

_ : {X : 𝓤 ̇ } → T X ＝ (V × V → X)
_ = refl

_ : {X : 𝓤 ̇ } (p : X → T R) (α β : V)
  → ℓ p [] (α , β) ＝ []
_ = λ p α β → refl

_ : {X : 𝓤 ̇ } (p : X → T R) (x : X) (xs : List X) (α β : V)
  → ℓ p (x ∷ xs) (α , β)
  ＝ p x (α , β) ∷ ℓ p xs (max α (val (p x (α , β))) , β)
_ = λ p x xs α β → refl

module _ {A : 𝓤 ̇ } (P : A → 𝓣 ̇ ) (d : (a : A) → is-decidable (P a)) where

 _ : take-until P d [] ＝ []
 _ = refl

 _ : (a : A) (as : List A)
   → take-until P d (a ∷ as)
   ＝ a ∷ Cases (d a) (λ _ → []) (λ _ → take-until P d as)
 _ = λ a as → refl

_ : {X : 𝓤 ̇ } (xs : List⁺ X) (p : X → T R) (α β : V)
  → φ*max xs p (α , β)
  ＝ max⁺ (take-until (λ r → β ≤ val r) (λ r → ≤-decidable β (val r))
            (ℓ p (underlying-list⁺ xs) (α , β)) ,
          take-until-is-non-empty
           (λ r → β ≤ val r)
           (λ r → ≤-decidable β (val r))
           (ℓ p (underlying-list⁺ xs) (α , β))
           (ℓ-is-non-empty p (underlying-list⁺ xs) (α , β)
             (underlying-list⁺-is-non-empty xs)))
_ = λ xs p α β → refl

_ : (r : R) (rs : List R) (ν : is-non-empty (r ∷ rs))
  → max⁺ ((r ∷ rs) , ν) ＝ maxˡ r rs
_ = λ r rs ν → refl

\end{code}

The minimizing quantifiers are the maximizing quantifiers for the
opposite order, with the bounds swapped in the alpha-beta version.
The module Min is the module of the maximizing quantifiers
instantiated with the opposite order, whose relation is λ a b → b < a.

\begin{code}

_ : {X : 𝓤 ̇ } → φmin {X} ＝ Min.φmax
_ = refl

_ : {X : 𝓤 ̇ } (xs : List⁺ X) (p : X → T R) (α β : V)
  → φ*min xs p (α , β) ＝ Min.φ*max xs (λ x → p x ∘ swap) (β , α)
_ = λ xs p α β → refl

_ : (a b : V) → swap (a , b) ＝ (b , a)
_ = λ a b → refl

_ : (a b : V) → Decidable-Strict-Weak-Order._<_ (opposite O) a b ＝ (b < a)
_ = λ a b → refl

\end{code}

3. Games.

A game tree is an element of the type 𝑻 of the module Games.TypeTrees:
either the empty tree [], or a type X of moves followed by a tree Xf x
for each move x. A play is a path Path Xt from the root to a
leaf. Each internal node is labelled by an element of Node X, a player
and a non-empty list of moves, which gives the quantifier at that
node. These are the games of Section 6.1 of the paper, in the
generality of the paper on games with dependent types cited there,
where the type of moves at a round and the number of rounds may also
depend on the moves played so far.

\begin{code}

_ : Path [] ＝ 𝟙
_ = refl

_ : (X : 𝓤 ̇ ) (Xf : X → 𝑻) → Path (X ∷ Xf) ＝ (Σ x ꞉ X , Path (Xf x))
_ = λ X Xf → refl

_ : (X : 𝓤 ̇ ) → Node X ＝ Player × List⁺ X
_ = λ X → refl

_ : {X : 𝓤 ̇ } (xs : List⁺ X) → quantifier (maximizer , xs) ＝ φmax xs
_ = λ xs → refl

_ : {X : 𝓤 ̇ } (xs : List⁺ X) → quantifier (minimizer , xs) ＝ φmin xs
_ = λ xs → refl

_ : {X : 𝓤 ̇ } (xs : List⁺ X) → quantifier* (maximizer , xs) ＝ φ*max xs
_ = λ xs → refl

_ : {X : 𝓤 ̇ } (xs : List⁺ X) → quantifier* (minimizer , xs) ＝ φ*min xs
_ = λ xs → refl

\end{code}

The optimal outcome out(G) of the game G, and the outcome
out*_{α,β}(G) of its alpha-beta version G*, whose outcome function is
η ∘ q, the composition of q with the unit of the reader monad. These
are the recursive equations stated in Section 4 of the paper.

\begin{code}

_ : (q : Path [] → R) → outcome [] ⟨⟩ q ＝ q ⟨⟩
_ = λ q → refl

_ : (X : 𝓤 ̇ ) (Xf : X → 𝑻) (n : Node X) (nf : (x : X) → structure Node (Xf x))
    (q : Path (X ∷ Xf) → R)
  → outcome (X ∷ Xf) (n :: nf) q
  ＝ quantifier n (λ x → outcome (Xf x) (nf x) (λ ys → q (x , ys)))
_ = λ X Xf n nf q → refl

_ : (q : Path [] → R) (α β : V) → outcome* [] ⟨⟩ q (α , β) ＝ q ⟨⟩
_ = λ q α β → refl

_ : (X : 𝓤 ̇ ) (Xf : X → 𝑻) (n : Node X) (nf : (x : X) → structure Node (Xf x))
    (q : Path (X ∷ Xf) → R) (α β : V)
  → outcome* (X ∷ Xf) (n :: nf) q (α , β)
  ＝ quantifier* n (λ x → outcome* (Xf x) (nf x) (λ ys → q (x , ys))) (α , β)
_ = λ X Xf n nf q α β → refl

\end{code}

4. Theorem 1 and Corollary 1.

Theorem 1 of the paper, for every game, and so in particular for every
subgame G_s. The inequalities compare values under val, and the equation
of (iii) is an equation of outcomes.

\begin{code}

Theorem-1 : (Xt : 𝑻)
            (nt : structure Node Xt)
            (q  : Path Xt → R)
            (α β : V)
          → (val (outcome Xt nt q) ≤ α → val (outcome* Xt nt q (α , β)) ≤ α)
          × (β ≤ val (outcome Xt nt q) → β ≤ val (outcome* Xt nt q (α , β)))
          × (α < val (outcome Xt nt q) → val (outcome Xt nt q) < β
                                 → outcome* Xt nt q (α , β) ＝ outcome Xt nt q)
Theorem-1 = theorem

Corollary-1-a : (Xt : 𝑻)
                (nt : structure Node Xt)
                (q  : Path Xt → R)
                (α β : V)
              → ((t : Path Xt) → α < val (q t))
              → ((t : Path Xt) → val (q t) < β)
              → outcome* Xt nt q (α , β) ＝ outcome Xt nt q
Corollary-1-a = corollary

Corollary-1-b : (Xt : 𝑻)
                (nt : structure Node Xt)
                (q  : Path Xt → R)
                (α β : V)
              → α < val (outcome* Xt nt q (α , β))
              → val (outcome* Xt nt q (α , β)) < β
              → outcome* Xt nt q (α , β) ＝ outcome Xt nt q
Corollary-1-b = corollary'

\end{code}

5. Corollary 2.

The notion of optimal play is that of the module Games.OptimalPlays,
which is Definition 2 of the paper: every move of the play attains the
optimal outcome of the subgame at the position where it is made. We
display its definition by its two defining equations, where the first
factor of the second equation says that the optimal outcome of the
game, computed by sequenceᴷ, is the optimal outcome of the subgame
after the move x. The last equation says that sequenceᴷ computes the
optimal outcome of part 3.

\begin{code}

module _ where

 open import Games.OptimalPlays {𝓤} {𝓤} V
  using (is-optimal-play)
 import Games.FiniteHistoryDependent {𝓤} {𝓤} V as G

 _ : (q : Path [] → V) → is-optimal-play {[]} ⟨⟩ q ⟨⟩ ＝ 𝟙
 _ = λ q → refl

 _ : (X : 𝓤 ̇ ) (Xf : X → 𝑻) (ϕ : (X → V) → V) (ϕf : (x : X) → G.𝓚 (Xf x))
     (q : Path (X ∷ Xf) → V) (x : X) (xs : Path (Xf x))
   → is-optimal-play {X ∷ Xf} (ϕ :: ϕf) q (x :: xs)
   ＝ (G.sequenceᴷ (ϕ :: ϕf) q ＝ G.sequenceᴷ (ϕf x) (λ ys → q (x , ys)))
   × is-optimal-play {Xf x} (ϕf x) (λ ys → q (x , ys)) xs
 _ = λ X Xf ϕ ϕf q x xs → refl

 _ : (Xt : 𝑻) (nt : structure Node Xt) (q : Path Xt → V)
   → Games.AlphaBeta.ViaProductsOfQuantifiers.outcome O V id Xt nt q
   ＝ G.sequenceᴷ
      (Games.AlphaBeta.ViaProductsOfQuantifiers.quantifier-tree O V id nt) q
 _ = λ Xt nt q → refl

\end{code}

In Corollary 2, outcomes are values, so that R = V and the valuation
is the identity, and the extended game G' has outcomes in V × Path Xt,
compared by their first components, and outcome function
q'(t) = (q(t) , t).

\begin{code}

module _ (Xt : 𝑻)
         (nt : structure Node Xt)
         (q  : Path Xt → V)
       where

 open import Games.OptimalPlays {𝓤} {𝓤} V
  using (is-optimal-play)
 open Games.AlphaBeta.OptimalPlays O
  using (value ; q' ; extended-game-gives-optimal-play ;
         αβ-search-agrees-with-exhaustive-search)

 private
  outcome₀ : V
  outcome₀ = Games.AlphaBeta.ViaProductsOfQuantifiers.outcome O V id Xt nt q

  outcome' : V × Path Xt
  outcome' = Games.AlphaBeta.ViaProductsOfQuantifiers.outcome
              O (V × Path Xt) value Xt nt (q' Xt nt q)

  outcome*' : V → V → V × Path Xt
  outcome*' α β = Games.AlphaBeta.ViaProductsOfQuantifiers.outcome*
                   O (V × Path Xt) value Xt nt (q' Xt nt q) (α , β)

  optimal : Path Xt → 𝓤 ̇
  optimal = is-optimal-play
             (Games.AlphaBeta.ViaProductsOfQuantifiers.quantifier-tree
               O V id nt) q

 _ : (t : Path Xt) → q' Xt nt q t ＝ (q t , t)
 _ = λ t → refl

 Corollary-2 : (α β : V)
             → α < outcome₀
             → outcome₀ < β
             → Σ t ꞉ Path Xt , (outcome' ＝ (outcome₀ , t))
                             × (outcome*' α β ＝ (outcome₀ , t))
                             × optimal t
 Corollary-2 α β a b =
  let (t , e , o) = extended-game-gives-optimal-play Xt nt q

      I : Path Xt
      I = t

      II : outcome' ＝ (outcome₀ , I)
      II = e

      III : outcome*' α β ＝ (outcome₀ , I)
      III = outcome*' α β  ＝⟨ III₀ ⟩
            outcome'       ＝⟨ e ⟩
            (outcome₀ , I) ∎

      IV : optimal I
      IV = o
  in I , II , III , IV
  where
   III₀ = αβ-search-agrees-with-exhaustive-search Xt nt q α β a b

\end{code}

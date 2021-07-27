Martin Escardo, Paulo Oliva, 2nd July 2021

We study finite, history dependent games of perfect information using
selection functions and dependent-type trees.

This is based on our previous work.

  [1] M.H. Escardó and Paulo Oliva. Sequential Games and Optimal
      Strategies. Proceedings of the Royal Society A, 467:1519-1545,
      2011. https://doi.org/10.1098/rspa.2010.0471

We generalize [1] by considering the case that the type Xₖ of moves xₖ
at round k depends on the moves played at the previous rounds. So in a
sequence of moves x₀,x₁,x₂,…, we have that

  * the type X₀ of initial moves doesn't depend on anything,
  * the type X₁ depends on the first move x₀ : X₀,
  * the type X₂ depends on depends on the first move x₀ : X₀ and the
    second move x₁ : X₁.

In order to achieve this generalization, we work with game trees
whose nodes are labelled by types that collect the allowed moves at a
given round. Then a play x₀,x₁,x₂,…, is a path in such a tree.

This formulation of the notion of game naturally accounts for finite
games of *unbounded* length, which in [1] was achieved by continuous,
infinite games instead.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT hiding (J)
open import UF-Base
open import UF-FunExt

module FiniteHistoryDependentGames (fe : Fun-Ext) where

\end{code}

We represent the moves of a history-dependent sequential game by a
dependent-type tree (DTT).  This is either an empty tree [] or else
has a type X of initial moves at the root, and, inductively, a family
Xf of subtrees indexed by elements of X, which is written X ∷ Xf. We
refer to the family Xf as a forest. We let Xt range over such trees.

 * Xt ranges over dependent-type trees.
 * Xf ranges over dependent-type forests.

\begin{code}

data DTT : Type₁ where
  []  : DTT
  _∷_ : (X : Type) (Xf : X → DTT) → DTT

\end{code}

The type of full paths in a tree Xt, from the root to a leaf, is
inductively defined as follows:

\begin{code}

Path : DTT → Type
Path []       = 𝟙
Path (X ∷ Xf) = Σ x ꞉ X , Path (Xf x)

\end{code}

As discussed above, a play in a game is defined to be such a path.

The variable xs ranges over paths, that is, elements of the type
Path Xt for a dependent-type-tree Xt.

\begin{code}

pattern _::_ x xs = (x , xs)

path-head : {X : Type} {Xf : X → DTT} → Path (X ∷ Xf) → X
path-head (x :: xs) = x

path-tail : {X : Type} {Xf : X → DTT} ((x :: xs) : Path (X ∷ Xf)) → Path (Xf x)
path-tail (x :: xs) = xs

\end{code}

The idea is that we choose a move x, and then, inductively, a path in
the subtree Xf x.

Quantifiers and selections, as in Sections 1 and 2 of reference [1]:

\begin{code}

K : Type → Type → Type
K R X = (X → R) → R

J : Type → Type → Type
J R X = (X → R) → X

\end{code}

In the same way as the type of moves at a given stage of the game
depends on the previousely played moves, so do the quantifies and
selection functions.

𝓚 assigns a quantifier to each node in a given tree, and similarly 𝓙
assigns selection functions to the nodes.

\begin{code}

𝓚 :  Type → DTT → Type
𝓚 R []       = 𝟙
𝓚 R (X ∷ Xf) = K R X × ((x : X) → 𝓚 R (Xf x))

𝓙 :  Type → DTT → Type
𝓙 R []       = 𝟙
𝓙 R (X ∷ Xf) = J R X × ((x : X) → 𝓙 R (Xf x))

\end{code}

 * ϕ ranges over the type K R X of quantifiers.
 * ε ranges over the type J R X of selection functions.

 * ϕt ranges over the type 𝓚 R Xt of quantifier trees.
 * εt ranges over the type 𝓙 R Xt of selection-function trees.

 * ϕf ranges over the type (x : X) → 𝓚 R (Xf x) of quantifier forests.
 * εf ranges over the type (x : X) → 𝓙 R (Xf x) of selection-function forests.

Sequencing quantifiers and selections, as constructed in Definitions 2
and 12 of reference [1], but using our tree representation of games
instead:

\begin{code}

K-sequence : {Xt : DTT} {R : Type} → 𝓚 R Xt → K R (Path Xt)
K-sequence {[]}     ⟨⟩        q = q ⟨⟩
K-sequence {X ∷ Xf} (ϕ :: ϕf) q = ϕ (λ x → K-sequence {Xf x} (ϕf x) (λ xs → q (x :: xs)))

J-sequence : {Xt : DTT} {R : Type} → 𝓙 R Xt → J R (Path Xt)
J-sequence {[]}     ⟨⟩        q = ⟨⟩
J-sequence {X ∷ Xf} (ε :: εf) q = h :: t h
 where
  t : (x : X) → Path (Xf x)
  t x = J-sequence {Xf x} (εf x) (λ xs → q (x :: xs))

  h : X
  h = ε (λ x → q (x :: t x))

\end{code}

The following is Definition 3 of the above reference [1].

A game is defined by a type R of outcomes, a game tree Xt, a
quantifier tree ϕt and an outcome function q:

\begin{code}

record Game : Type₁ where
 constructor
  game

 field
  Xt  : DTT
  R   : Type
  ϕt  : 𝓚 R Xt
  q   : Path Xt → R

open Game

\end{code}

We define the optimal outcome of a game to be the sequencing of its
quantifiers applied to the outcome function (Theorem 3.1 of [1]).

\begin{code}

optimal-outcome : (G : Game) → G .R
optimal-outcome (game R Xt ϕt q) = K-sequence ϕt q

\end{code}

A strategy defines how to pick a path of a tree. The type Strategy of
all possible strategies is constructed as follows (Definition 4 of [1]):

\begin{code}

Strategy : DTT -> Type
Strategy []       = 𝟙
Strategy (X ∷ Xf) = X × ((x : X) → Strategy (Xf x))

\end{code}

 * σ ranges over the type Strategy Xt of strategies for a
   dependent-type tree Xt.

 * σf ranges over the type (x : X) → Strategy (Xf x) of strategy
   forests for a dependent-type forest Xf.

We get a path in the tree by following any given strategy:

\begin{code}

strategic-path : {Xt : DTT} → Strategy Xt → Path Xt
strategic-path {[]}    ⟨⟩         = ⟨⟩
strategic-path {X ∷ Xf} (x :: σf) = x :: strategic-path {Xf x} (σf x)

\end{code}

In the notation of reference [1] above, Definition 5, a strategy σt
for a game (Xt,R,ϕt,q) is said to be optimal, or in subgame perfect
equillibrium (abbreviated sgpe), if for every partial play a₀,…,aₖ₋₁
of length k, we have

   q(a₀,…,aₖ₋₁,bₖ(a₀,…,aₖ₋₁),…,bₙ₋₁(a₀,…,aₖ₋₁))
 = ϕₖ(λxₖ.q(a₀,…,aₖ₋₁,xₖ,bₖ₊₁(a₀,…,aₖ₋₁,xₖ),…,bₙ₋₁(a₀,…,aₖ₋₁,xₖ)))

where the sequence b is inductively defined by

  bⱼ(a₀,…,aₖ₋₁) = σⱼ(a₀,…,aₖ₋₁,bₖ(a₀,…,aₖ₋₁),…,bⱼ₋₁(a₀,…,aₖ₋₁))

for k ≤ j < n.

Intuitively, the strategy σ is optimal if the outcome

  q(a₀,…,aₖ₋₁,bₖ(a₀,…,aₖ₋₁),…,bₙ₋₁(a₀,…,aₖ₋₁))

obtained by following σ is the best possible outcome as described by
the quantifier ϕₖ for each round k, considering all possible
deviations xₖ from the strategy at that round.

For the purposes of our generalization of [1] to dependent games, it
is convenient to define this notion by induction on the game tree Xt:

\begin{code}

is-sgpe : {Xt : DTT} {R : Type} → 𝓚 R Xt → (Path Xt → R) → Strategy Xt → Type
is-sgpe {[]}     ⟨⟩        q ⟨⟩         = 𝟙
is-sgpe {X ∷ Xf} (ϕ :: ϕf) q (x₀ :: σf) =

      (q (x₀ :: strategic-path (σf x₀)) ≡ ϕ (λ x → q (x :: strategic-path (σf x))))
    ×
      ((x : X) → is-sgpe {Xf x} (ϕf x) (λ (xs : Path (Xf x)) → q (x :: xs)) (σf x))

\end{code}

In the above definition:

 * If the game tree is empty, then the strategy is empty, and we say
   that it is true that it is in sgpe, where "true" is represented by
   the unit type 𝟙 in propositions-as-types.

 * If the game tree has a root X followed by a forest Xf, then the
   strategy must be of the form x₀ :: σf, where x₀ is the first move
   according to the strategy, and where σf is a forest of strategies
   that depends on a deviation x.

   So the first part

     q (a :: strategic-path (σf a)) ≡ ϕ (λ x → q (x :: strategic-path (σf x)))

   of the definition is as in the comment above, but with a partial
   play of length k=0, and the second (inductive) part, says that the
   substrategy σf x, for any deviation x, is in subgame perfect
   equillibrium in the subgame

     (Xf x , R , ϕf x , λ (xs : Path (Xf x)) → q (x :: xs)).

As discussed above, we say that a strategy for a game is optimal if it
is in subgame perfect equilibrium.

\begin{code}

is-optimal : {G : Game} (σ : Strategy (G .Xt)) → Type
is-optimal {game Xt R ϕt q} σ = is-sgpe {Xt} {R} ϕt q σ

\end{code}

The main lemma is that the optimal outcome is the same as the
application of the outcome function to the path induced by a strategy
in perfect subgame equilibrium.

The following is Theorem 3.1 of reference [1].

\begin{code}

sgpe-lemma : (R : Type) (Xt : DTT) (ϕt : 𝓚 R Xt) (q : Path Xt → R) (σ : Strategy Xt)
           → is-sgpe ϕt q σ
           → K-sequence ϕt q ≡ q (strategic-path σ)
sgpe-lemma R []       ⟨⟩        q ⟨⟩        ⟨⟩       = refl
sgpe-lemma R (X ∷ Xf) (ϕ :: ϕt) q (a :: σf) (h :: t) = γ
 where
  IH : (x : X) → is-sgpe (ϕt x) (λ xs → q (x :: xs)) (σf x)
               → K-sequence (ϕt x) (λ xs → q (x :: xs)) ≡ q (x :: strategic-path (σf x))
  IH x = sgpe-lemma R (Xf x) (ϕt x) (λ (xs : Path (Xf x)) → q (x :: xs)) (σf x)

  γ = ϕ (λ x → K-sequence (ϕt x) (λ xs → q (x :: xs))) ≡⟨ ap ϕ (dfunext fe (λ x → IH x (t x))) ⟩
      ϕ (λ x → q (x :: strategic-path (σf x)))         ≡⟨ h ⁻¹ ⟩
      q (a :: strategic-path (σf a))                   ∎

\end{code}

This can be reformulated as follows in terms of the type of games:

\begin{code}

equillibrium-theorem : (G : Game) (σ : Strategy (G .Xt))
                     → is-optimal σ
                     → optimal-outcome G ≡ G .q (strategic-path σ)
equillibrium-theorem (game R Xt ϕt q) = sgpe-lemma Xt R ϕt q

\end{code}

We now show how to use selection functions to compute a sgpe strategy.

We first convert a selection function into a quantifiers as in
Definition 10 of [1]:

\begin{code}

overline : {X R : Type} → J R X → K R X
overline ε = λ p → p (ε p)

\end{code}

The following is the application of overline to each selection
function of a tree:

\begin{code}

Overline : {Xt : DTT} {R : Type} → 𝓙 R Xt → 𝓚 R Xt
Overline {[]}    ⟨⟩         = ⟨⟩
Overline {X ∷ Xf} (ε :: εs) = overline ε :: (λ x → Overline {Xf x} (εs x))

\end{code}

The following, which defines a strategy from given selection
functions, is defined in Theorem 5.4 of [1], with the difference that
here, for the moment, we consider only single-valued quantifiers.

\begin{code}

selection-strategy : {Xt : DTT} {R : Type} → 𝓙 R Xt → (Path Xt → R) → Strategy Xt
selection-strategy {[]}     ⟨⟩           q = ⟨⟩
selection-strategy {X ∷ Xf} εt@(ε :: εf) q = x₀ :: σf
 where
  x₀ : X
  x₀ = path-head (J-sequence εt q)

  σf : (x : X) → Strategy (Xf x)
  σf x = selection-strategy {Xf x} (εf x) (λ xs → q (x :: xs))

\end{code}

The following definition is in Section 1 on [1].

\begin{code}

_is-a-selection-of_ : {X R : Type} → J R X → K R X → Type
ε is-a-selection-of ϕ = overline ε ∼ ϕ

\end{code}

We generalize it to selection-function and quantifier trees in the
obvious way, by induction:

\begin{code}

_are-selections-of_ : {Xt : DTT} {R : Type} → 𝓙 R Xt → 𝓚 R Xt → Type
_are-selections-of_ {[]}     ⟨⟩        ⟨⟩        = 𝟙
_are-selections-of_ {X ∷ Xf} (ε :: εf) (ϕ :: ϕf) = (ε is-a-selection-of ϕ)
                                                 × ((x : X) → (εf x) are-selections-of (ϕf x))

observation : {Xt : DTT} {R : Type} (εt : 𝓙 R Xt) (ϕt : 𝓚 R Xt)
            → εt are-selections-of ϕt
            → Overline εt ≡ ϕt
observation {[]}     ⟨⟩        ⟨⟩        ⟨⟩        = refl
observation {X ∷ Xf} (ε :: εf) (ϕ :: ϕf) (a :: af) = γ
 where
  IH : (x : X) → Overline (εf x) ≡ ϕf x
  IH x = observation {Xf x} (εf x) (ϕf x) (af x)

  I : overline ε ≡ ϕ
  I = dfunext fe a

  II : (λ x → Overline (εf x)) ≡ ϕf
  II = dfunext fe IH

  γ : overline ε :: (λ x → Overline (εf x)) ≡ ϕ :: ϕf
  γ = ap₂ _::_ I II

\end{code}

Notice that the converse is also true, that is, if Overline εt ≡ ϕt
then εt are selection of ϕt, but we don't need this fact here.

\begin{code}

crucial-lemma : {Xt : DTT} {R : Type} (εt : 𝓙 R Xt) (q : Path Xt → R)
              → J-sequence εt q
              ≡ strategic-path (selection-strategy εt q)
crucial-lemma {[]}     ⟨⟩           q = refl
crucial-lemma {X ∷ Xf} εt@(ε :: εf) q = γ
 where
  t : (x : X) → Path (Xf x)
  t x = J-sequence {Xf x} (εf x) (λ xs → q (x :: xs))

  h : X
  h = ε (λ x → q (x :: t x))

  x₀ : X
  x₀ = path-head (J-sequence εt q)

  σf : (x : X) → Strategy (Xf x)
  σf x = selection-strategy {Xf x} (εf x) (λ xs → q (x :: xs))

  IH : t h ≡ strategic-path (σf x₀)
  IH = crucial-lemma (εf x₀) (λ xs → q (x₀ :: xs))

  remark : h ≡ x₀
  remark = refl

  γ : h :: t h ≡ x₀ :: strategic-path (σf x₀)
  γ = ap (h ::_) IH

selection-strategy-lemma : {Xt : DTT} {R : Type} (εt : 𝓙 R Xt) (q : Path Xt → R)
                         → is-sgpe (Overline εt) q (selection-strategy εt q)
selection-strategy-lemma {[]}     {R} ⟨⟩        q = ⟨⟩
selection-strategy-lemma {X ∷ Xf} {R} (ε :: εf) q = h :: t
 where
  f g : X → R
  f x = q (x :: J-sequence (εf x) (λ xs → q (x :: xs)))
  g x = q (x :: strategic-path (selection-strategy (εf x) (λ xs → q (x :: xs))))

  I : (x : X) → J-sequence (εf x) (λ xs → q (x :: xs))
              ≡ strategic-path (selection-strategy (εf x) (λ xs → q (x :: xs)))
  I x = crucial-lemma (εf x) (λ xs → q (x :: xs))

  II : f ≡ g
  II = dfunext fe (λ x → ap (λ - → q (x :: -)) (I x))

  h : g (ε f) ≡ g (ε g)
  h = ap (g ∘ ε) II

  t : (x : X) → is-sgpe (Overline (εf x)) (λ xs → q (x :: xs)) (selection-strategy (εf x) (λ xs → q (x :: xs)))
  t x = selection-strategy-lemma (εf x) (λ xs → q (x :: xs))


\end{code}

The following, which shows how to use selection functions to compute
optimal strategies, corresponds to Theorem 6.2 of [1].

\begin{code}

selection-strategy-theorem : {Xt : DTT} {R : Type} (εt : 𝓙 R Xt) (ϕt : 𝓚 R Xt) (q : Path Xt → R)
                           → εt are-selections-of ϕt
                           → is-sgpe ϕt q (selection-strategy εt q)
selection-strategy-theorem εt ϕt q a = III
 where
  I : Overline εt ≡ ϕt
  I = observation εt ϕt a

  II : is-sgpe (Overline εt) q (selection-strategy εt q)
  II = selection-strategy-lemma εt q

  III : is-sgpe ϕt q (selection-strategy εt q)
  III = transport (λ - → is-sgpe - q (selection-strategy εt q)) I II

\end{code}

Incomplete examples:

\begin{code}

no-repetitions : (n : ℕ) (X : Type) → DTT
no-repetitions zero X     = []
no-repetitions (succ n) X = X ∷ λ (x : X) → no-repetitions n (Σ y ꞉ X , y ≢ x )

open import Fin hiding ([] ; _∷_ ; _::_ ; hd ; tl ; _++_)

Permutations : ℕ → Type
Permutations n = Path (no-repetitions n (Fin n))

example-permutation2 : Permutations 2
example-permutation2 = 𝟎 , (𝟏 , λ ()) , ⟨⟩

\end{code}

TODO. Define tic-tac-toe using no-repetitions and Fin 9.

TODO. Generalize the above to multi-valued quantifiers, using monads.

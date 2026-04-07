Martin Escardo, Paulo Oliva, 2-27 July 2021.

The following paper is based on this file:

  [0] Martin Escardo and Paulo Oliva. Higher-order games with
      dependent types.  Theoretical Computer Science, Volume 974, 29
      September 2023, 114111.
      https://doi.org/10.48550/arXiv.2212.07735
      https://doi.org/10.1016/j.tcs.2023.114111

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
  * the type X₂ depends on the first move x₀ : X₀ and the
    second move x₁ : X₁.
  …

In order to achieve this generalization, we work with game trees
whose nodes are labelled by types that collect the allowed moves at a
given round. Then a play x₀,x₁,x₂,…, is a path in such a tree.

This formulation of the notion of game naturally accounts for finite
games of *unbounded* length, which in [1] was achieved by continuous,
infinite games instead.

We assume a given type R of outcomes for games as a module parameter.

\begin{code}

{-# OPTIONS --safe --without-K  #-}

open import MLTT.Spartan hiding (J)

module Games.FiniteHistoryDependent
        {𝓤 𝓦₀ : Universe}
        (R : 𝓦₀ ̇ )
       where

open import MonadOnTypes.Definition
open import MonadOnTypes.J
open import MonadOnTypes.K
open import MonadOnTypes.JK R
open import UF.Base
open import UF.FunExt

open K-definitions R
open J-definitions R

\end{code}

The following module defines the main data structure we use in order
to represent the above kind of game:

\begin{code}

open import Games.TypeTrees {𝓤}

\end{code}

We use quantifiers as in Section 1 of reference [1], defined in
another module.

In the same way as the type of moves at a given stage of the game
depends on the previously played moves, so do the quantifiers and
selection functions.

𝓚 decorates each internal node X of a type tree with the type K X of
quantifiers over X.

\begin{code}

𝓚 : 𝑻 → 𝓤 ⊔ 𝓦₀ ̇
𝓚 = structure K

remark-𝓚 : {X : 𝓤 ̇ } {Xf : X → 𝑻}
         → (𝓚 []       ＝ 𝟙)
         × (𝓚 (X ∷ Xf) ＝ K X × ((x : X) → 𝓚 (Xf x)))
remark-𝓚 = refl , refl

\end{code}

 * ϕ  ranges over the type K X of quantifiers.
 * ϕt ranges over the type 𝓚 Xt of quantifier trees.
 * ϕf ranges over the type (x : X) → 𝓚 (Xf x) of quantifier forests.


Sequencing quantifiers, as constructed in Definition 2 of reference [1],
but using our tree representation of games instead:

\begin{code}

sequenceᴷ : {Xt : 𝑻} → 𝓚 Xt → K (Path Xt)
sequenceᴷ = path-sequence (𝕂 R)

\end{code}

The following is Definition 3 of the above reference [1].

A game is defined by a game tree Xt, a type R of outcomes, a
quantifier tree ϕt and an outcome function q:

\begin{code}

record Game : 𝓤 ⁺ ⊔ 𝓦₀ ̇ where
 constructor game
 field
  game-tree       : 𝑻
  payoff-function : Path game-tree → R
  quantifier-tree : 𝓚 game-tree

open Game public

\end{code}

We can think of Xt as the rules of the game, and R, ϕt and q as the
objective of the game.

We define the optimal outcome of a game to be the sequencing of its
quantifiers applied to the outcome function (Theorem 3.1 of [1]).

\begin{code}

optimal-outcome : Game → R
optimal-outcome (game Xt q ϕt) = sequenceᴷ ϕt q

\end{code}

A strategy assigns a move to each node of a tree. This corresponds to
Definition 4 of [1]:

\begin{code}

Strategy : 𝑻 → 𝓤 ̇
Strategy = structure id

remark-Strategy : {X : 𝓤 ̇ } {Xf : X → 𝑻}
                → (Strategy []       ＝ 𝟙)
                × (Strategy (X ∷ Xf) ＝ X × ((x : X) → Strategy (Xf x)))
remark-Strategy = refl , refl

\end{code}

 * σ ranges over the type Strategy Xt of strategies for a
   dependent-type tree Xt.

 * σf ranges over the type (x : X) → Strategy (Xf x) of strategy
   forests for a dependent-type forest Xf.

We get a path in the tree by following any given strategy:

\begin{code}

strategic-path : {Xt : 𝑻} → Strategy Xt → Path Xt
strategic-path = path-sequence 𝕀𝕕

remark-strategic-path : {X : 𝓤 ̇ } {Xf : X → 𝑻} {x : X}
                        {σf : (x : X) → Strategy (Xf x)}
                      → (strategic-path {[]}     ⟨⟩        ＝ ⟨⟩)
                      × (strategic-path {X ∷ Xf} (x :: σf)
                         ＝ x :: strategic-path (σf x))
remark-strategic-path = refl , refl

\end{code}

In the notation of reference [1] above, Definition 5, a strategy σ
for a game (Xt,R,ϕt,q) is said to be optimal, or in subgame perfect
equilibrium (abbreviated sgpe), if for every partial play a₀,…,aₖ₋₁
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

is-in-equilibrium : {X : 𝓤 ̇ } {Xf : X → 𝑻}
                    (q : (Σ x ꞉ X , Path (Xf x)) → R)
                    (ϕ : K X)
                  → Strategy (X ∷ Xf)
                  → 𝓦₀ ̇
is-in-equilibrium {X} {Xf} q ϕ σt@(x₀ :: σf)  =
 subpred q x₀ (strategic-path (σf x₀)) ＝ ϕ (λ x → subpred q x (strategic-path (σf x)))

is-in-sgpe : {Xt : 𝑻} → 𝓚 Xt → (Path Xt → R) → Strategy Xt → 𝓤 ⊔ 𝓦₀ ̇
is-in-sgpe {[]}     ⟨⟩        q ⟨⟩            = 𝟙
is-in-sgpe {X ∷ Xf} (ϕ :: ϕf) q σt@(x₀ :: σf) =
   is-in-equilibrium q ϕ σt
 × ((x : X) → is-in-sgpe {Xf x} (ϕf x) (subpred q x) (σf x))

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

     subpred q x₀ (strategic-path (σf x₀)) ＝ ϕ (λ x → subpred q x (strategic-path (σf x)))

   of the definition is as in the comment above, but with a partial
   play of length k=0, and the second (inductive) part, says that the
   substrategy σf x, for any deviation x, is in subgame perfect
   equilibrium in the subgame

     (Xf x , R , ϕf x , subpred q x).

As discussed above, we say that a strategy for a game is optimal if it
is in subgame perfect equilibrium.

\begin{code}

is-optimal : (G : Game) (σ : Strategy (game-tree G)) → 𝓤 ⊔ 𝓦₀ ̇
is-optimal (game Xt ϕt q) σ = is-in-sgpe {Xt} q ϕt σ

\end{code}

The main lemma is that the optimal outcome is the same thing as the
application of the outcome function to the path induced by a strategy
in perfect subgame equilibrium.

Remark. In the published paper [0] above, we use the terminology
`is-optimal` as above, but perhaps we should stick to subgame perfect
equilibrium for the terminology.

The following is Theorem 3.1 of reference [1].

\begin{code}

sgpe-lemma : Fun-Ext
           → (Xt : 𝑻) (ϕt : 𝓚 Xt) (q : Path Xt → R) (σ : Strategy Xt)
           → is-in-sgpe ϕt q σ
           → q (strategic-path σ) ＝ sequenceᴷ ϕt q
sgpe-lemma fe []       ⟨⟩        q ⟨⟩        ⟨⟩       = refl
sgpe-lemma fe (X ∷ Xf) (ϕ :: ϕt) q (a :: σf) (h :: t) = γ
 where
  observation-t : type-of t ＝ ((x : X) → is-in-sgpe (ϕt x) (subpred q x) (σf x))
  observation-t = refl

  IH : (x : X) → subpred q x (strategic-path (σf x)) ＝ sequenceᴷ (ϕt x) (subpred q x)
  IH x = sgpe-lemma fe (Xf x) (ϕt x) (subpred q x) (σf x) (t x)

  γ = subpred q a (strategic-path (σf a))           ＝⟨ h ⟩
      ϕ (λ x → subpred q x (strategic-path (σf x))) ＝⟨ ap ϕ (dfunext fe IH) ⟩
      ϕ (λ x → sequenceᴷ (ϕt x) (subpred q x))      ∎

\end{code}

This can be reformulated as follows in terms of the type of games:

\begin{code}

optimality-theorem : Fun-Ext
                   → (G@(game Xt q ϕt) : Game) (σ : Strategy Xt)
                   → is-optimal G σ
                   → q (strategic-path σ) ＝ optimal-outcome G
optimality-theorem fe (game Xt ϕt q) = sgpe-lemma fe Xt q ϕt

\end{code}

We now show how to use selection functions to compute a sgpe strategy.

We use selection functions, as in Section 2 of reference [1], defined
in another module.

𝓙 assigns types of selection functions to the nodes.

\begin{code}

𝓙 : 𝑻 → 𝓦₀ ⊔ 𝓤 ̇
𝓙 = structure J

remark-𝓙 : {X : 𝓤 ̇ } {Xf : X → 𝑻}
         → (𝓙 [] ＝ 𝟙)
         × (𝓙 (X ∷ Xf) ＝ J X × ((x : X) → 𝓙 (Xf x)))
remark-𝓙 = refl , refl

\end{code}

 * ε ranges over the type J X of selection functions.
 * εt ranges over the type 𝓙 Xt of selection-function trees.
 * εf ranges over the type (x : X) → 𝓙 (Xf x) of selection-function forests.

Sequencing selection functions, as constructed in Definition 12 of
reference [1], but using our tree representation of games instead:

\begin{code}

sequenceᴶ : {Xt : 𝑻} → 𝓙 Xt → J (Path Xt)
sequenceᴶ = path-sequence (𝕁 R)

\end{code}

The following, which defines a strategy from given selection
functions, is defined in Theorem 5.4 of [1], with the difference that
here, for the moment, we consider only single-valued quantifiers.

\begin{code}

selection-strategy : {Xt : 𝑻} → 𝓙 Xt → (Path Xt → R) → Strategy Xt
selection-strategy {[]}     ⟨⟩           q = ⟨⟩
selection-strategy {X ∷ Xf} εt@(ε :: εf) q = x₀ :: σf
 where
  xs : Path (X ∷ Xf)
  xs = sequenceᴶ εt q

  x₀ : X
  x₀ = path-head xs

  σf : (x : X) → Strategy (Xf x)
  σf x = selection-strategy {Xf x} (εf x) (subpred q x)

\end{code}

We convert a selection function into a quantifier as in Definition 10
of [1], using the function overline, defined in another module.

The work with the definition of a selection function being a selection
function for a quantifier as in Section 1 on [1], defined in another
module.

We generalize it to selection-function and quantifier trees in the
obvious way, by induction:

\begin{code}

_Attains_ : {Xt : 𝑻} → 𝓙 Xt → 𝓚 Xt → 𝓤 ⊔ 𝓦₀ ̇
_Attains_ {[]}     ⟨⟩        ⟨⟩        = 𝟙
_Attains_ {X ∷ Xf} (ε :: εf) (ϕ :: ϕf) = (ε attains ϕ)
                                           × ((x : X) → (εf x) Attains (ϕf x))

\end{code}

The following is the application of overline to each selection
function of a tree:

\begin{code}

Overline : {Xt : 𝑻} → 𝓙 Xt → 𝓚 Xt
Overline {[]}     ⟨⟩        = ⟨⟩
Overline {X ∷ Xf} (ε :: εf) = overline ε :: (λ x → Overline {Xf x} (εf x))

\end{code}

The following is proved by straightforward induction on trees:

\begin{code}

observation : Fun-Ext
            → {Xt : 𝑻} (εt : 𝓙 Xt) (ϕt : 𝓚 Xt)
            → εt Attains ϕt
            → Overline εt ＝ ϕt
observation fe {[]}     ⟨⟩        ⟨⟩        ⟨⟩        = refl
observation fe {X ∷ Xf} (ε :: εf) (ϕ :: ϕf) (a :: af) = γ
 where
  IH : (x : X) → Overline (εf x) ＝ ϕf x
  IH x = observation fe {Xf x} (εf x) (ϕf x) (af x)

  I : overline ε ＝ ϕ
  I = dfunext fe a

  II : (λ x → Overline (εf x)) ＝ ϕf
  II = dfunext fe IH

  γ : overline ε :: (λ x → Overline (εf x)) ＝ ϕ :: ϕf
  γ = ap₂ _::_ I II

observation-converse : {Xt : 𝑻} (εt : 𝓙 Xt) (ϕt : 𝓚 Xt)
                     → Overline εt ＝ ϕt
                     → εt Attains ϕt
observation-converse {[]}     εt ϕt p = ⟨⟩
observation-converse {X ∷ Xf} (ε :: εf)
                     (.(λ p → p (ε p)) :: .(λ x → Overline (εf x))) refl =
 (λ x → refl) :: (λ x → observation-converse (εf x) (Overline (εf x)) refl)

\end{code}

Notice that the converse is also true, that is, if Overline εt ＝ ϕt
then εt are selections of ϕt, but we don't need this fact here.

\begin{code}

main-lemma : {Xt : 𝑻} (εt : 𝓙 Xt) (q : Path Xt → R)
           → strategic-path (selection-strategy εt q)
           ＝ sequenceᴶ εt q
main-lemma {[]}     ⟨⟩           q = refl
main-lemma {X ∷ Xf} εt@(ε :: εf) q =
 strategic-path (selection-strategy (ε :: εf) q) ＝⟨refl⟩
 x₀ :: strategic-path (σf x₀)                    ＝⟨ ap (x₀ ::_) IH ⟩
 x₀ :: sequenceᴶ {Xf x₀} (εf x₀) (subpred q x₀)  ＝⟨refl⟩
 x₀ :: ν x₀                                      ＝⟨refl⟩
 (ε ⊗ᴶ (λ x → sequenceᴶ {Xf x} (εf x))) q        ＝⟨refl⟩
 sequenceᴶ (ε :: εf) q                           ∎
 where
  ν : (x : X) → Path (Xf x)
  ν x = sequenceᴶ {Xf x} (εf x) (subpred q x)

  x₀ : X
  x₀ = ε (λ x → subpred q x (ν x))

  σf : (x : X) → Strategy (Xf x)
  σf x = selection-strategy {Xf x} (εf x) (subpred q x)

  IH : strategic-path (σf x₀) ＝ sequenceᴶ {Xf x₀} (εf x₀) (subpred q x₀)
  IH = main-lemma (εf x₀) (subpred q x₀)

selection-strategy-lemma : Fun-Ext
                         → {Xt : 𝑻} (εt : 𝓙 Xt) (q : Path Xt → R)
                         → is-in-sgpe (Overline εt) q (selection-strategy εt q)
selection-strategy-lemma fe {[]}     ⟨⟩           q = ⟨⟩
selection-strategy-lemma fe {X ∷ Xf} εt@(ε :: εf) q = γ
 where
  σf : (x : X) → Strategy (Xf x)
  σf x = selection-strategy (εf x) (subpred q x)

  x₀ x₁ : X
  x₀ = ε (λ x → subpred q x (sequenceᴶ (εf x) (subpred q x)))
  x₁ = ε (λ x → subpred q x (strategic-path (σf x)))

  I : (x : X) → strategic-path (σf x) ＝ sequenceᴶ (εf x) (subpred q x)
  I x = main-lemma (εf x) (subpred q x)

  II : x₁ ＝ x₀
  II = ap (λ - → ε (λ x → subpred q x (- x))) (dfunext fe I)

  III = overline ε (λ x → subpred q x (strategic-path (σf x))) ＝⟨refl⟩
        subpred q x₁ (strategic-path (σf x₁))                  ＝⟨ IV ⟩
        subpred q x₀ (strategic-path (σf x₀))                  ∎

   where
    IV = ap (λ - → subpred q - (strategic-path (σf -))) II

  IH : (x : X) → is-in-sgpe
                   (Overline (εf x))
                   (subpred q x)
                   (selection-strategy (εf x) (subpred q x))
  IH x = selection-strategy-lemma fe (εf x) (subpred q x)

  γ : is-in-sgpe (Overline εt) q (x₀ :: σf)
  γ = (III ⁻¹) :: IH

\end{code}

The following, which shows how to use selection functions to compute
optimal strategies, corresponds to Theorem 6.2 of [1].

\begin{code}

selection-strategy-theorem : Fun-Ext
                           → {Xt : 𝑻} (εt : 𝓙 Xt)
                             (ϕt : 𝓚 Xt) (q : Path Xt → R)
                           → εt Attains ϕt
                           → is-in-sgpe ϕt q (selection-strategy εt q)
selection-strategy-theorem fe εt ϕt q a = III
 where
  I : Overline εt ＝ ϕt
  I = observation fe εt ϕt a

  II : is-in-sgpe (Overline εt) q (selection-strategy εt q)
  II = selection-strategy-lemma fe εt q

  III : is-in-sgpe ϕt q (selection-strategy εt q)
  III = transport (λ - → is-in-sgpe - q (selection-strategy εt q)) I II


Selection-Strategy-Theorem
 : Fun-Ext
 → (G@(game Xt q ϕt) : Game) (εt : 𝓙 Xt)
 → εt Attains ϕt
 → is-optimal G (selection-strategy εt q)
Selection-Strategy-Theorem fe (game Xt ϕt q) εt
 = selection-strategy-theorem fe εt q ϕt

\end{code}

Added 27th August 2023 after the above was submitted for publication.

\begin{code}

selection-strategy-corollary
 : Fun-Ext
 → (G@(game Xt q ϕt) : Game) (εt : 𝓙 Xt)
 → εt Attains ϕt
 → q (sequenceᴶ εt q) ＝ optimal-outcome G
selection-strategy-corollary fe G@(game Xt q ϕt) εt a =
 q (sequenceᴶ εt q)                           ＝⟨ I ⟩
 q (strategic-path (selection-strategy εt q)) ＝⟨ II ⟩
 optimal-outcome G                            ∎
  where
   I  = ap q ((main-lemma εt q)⁻¹)
   II = sgpe-lemma fe Xt ϕt q
         (selection-strategy εt q)
         (Selection-Strategy-Theorem fe G εt a)

\end{code}

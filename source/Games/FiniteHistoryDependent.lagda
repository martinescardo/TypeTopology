Martin Escardo, Paulo Oliva, 2-27 July 2021

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
\begin{code}

{-# OPTIONS --without-K --safe --auto-inline #-} -- --exact-split

open import MLTT.Spartan hiding (J)
open import UF.Base
open import UF.FunExt

open import TypeTopology.SigmaDiscreteAndTotallySeparated

module Games.FiniteHistoryDependent (fe : Fun-Ext) where

\end{code}

We represent the moves of a history-dependent sequential game by a
dependent-type tree, collected in a type 𝕋.  This is either an empty
tree [] or else has a type X of initial moves at the root, and,
inductively, a family Xf of subtrees indexed by elements of X, which
is written X ∷ Xf. We refer to the family Xf as a forest. We let Xt
range over such trees.

 * Xt ranges over dependent-type trees.
 * Xf ranges over dependent-type forests.

\begin{code}

data 𝕋 : Type₁ where
  []  : 𝕋
  _∷_ : (X : Type) (Xf : X → 𝕋) → 𝕋

\end{code}

The type of full paths in a tree Xt, from the root to a leaf, is
inductively defined as follows:

\begin{code}

Path : 𝕋 → Type
Path []       = 𝟙
Path (X ∷ Xf) = Σ x ꞉ X , Path (Xf x)

\end{code}

As discussed above, a play in a game is defined to be such a path.

The idea is that we choose a move x, and then, inductively, a path in
the subtree Xf x.

The variable xs ranges over paths, that is, elements of the type
Path Xt for a dependent-type-tree Xt.

\begin{code}

pattern ⟨⟩        = ⋆
pattern _::_ x xs = (x , xs)

path-head : {X : Type} {Xf : X → 𝕋} → Path (X ∷ Xf) → X
path-head (x :: xs) = x

path-tail : {X : Type} {Xf : X → 𝕋} ((x :: xs) : Path (X ∷ Xf)) → Path (Xf x)
path-tail (x :: xs) = xs

plength : {Xt : 𝕋} → Path Xt → ℕ
plength {[]}     ⟨⟩        = 0
plength {X ∷ Xf} (x :: xs) = succ (plength {Xf x} xs)

\end{code}

NB. An alternative inductive definition of Path is the following,
where, unfortunately, we get a higher type level, and so we won't use
it:

\begin{code}

data Path₁ : 𝕋 → Type₁ where
 []  : Path₁ []
 _∷_ : {X : Type} {Xf : X → 𝕋} (x : X) (xs : Path₁ (Xf x)) → Path₁ (X ∷ Xf)

\end{code}

Quantifiers as in Section 1 of reference [1]:

\begin{code}

K : Type → Type → Type
K R X = (X → R) → R

\end{code}

In the same way as the type of moves at a given stage of the game
depends on the previously played moves, so do the quantifiers and
selection functions.

𝓚 assigns a quantifier to each node in a given tree:

\begin{code}

𝓚 :  Type → 𝕋 → Type
𝓚 R []       = 𝟙
𝓚 R (X ∷ Xf) = K R X × ((x : X) → 𝓚 R (Xf x))

\end{code}

 ⋆ ϕ  ranges over the type K R X of quantifiers.
 ⋆ ϕt ranges over the type 𝓚 R Xt of quantifier trees.
 ⋆ ϕf ranges over the type (x : X) → 𝓚 R (Xf x) of quantifier forests.


Sequencing quantifiers, as constructed in Definition 2 of reference [1],
but using our tree representation of games instead:

\begin{code}

K-sequence : {Xt : 𝕋} {R : Type} → 𝓚 R Xt → K R (Path Xt)
K-sequence {[]}     ⟨⟩        q = q ⟨⟩
K-sequence {X ∷ Xf} {R} (ϕ :: ϕf) q = ϕ (λ x → γ x (λ xs → q (x :: xs)))
 where
  γ : (x : X) → K R (Path (Xf x))
  γ x = K-sequence {Xf x} (ϕf x)

module remark-about-K-sequence (R : Type) where

 ηᴷ : {X : Type} → X → K R X
 ηᴷ x p = p x

 K-ext : {X Y : Type} → (X → K R Y) → K R X → K R Y
 K-ext f ϕ p = ϕ (λ x → f x p)

 K-map : {X Y : Type} → (X → Y) → K R X → K R Y
 K-map f = K-ext (ηᴷ ∘ f)

 _⊗ᴷ_ : {X : Type} {Y : X → Type}
      → K R X
      → ((x : X) → K R (Y x))
      → K R (Σ x ꞉ X , Y x)
 ϕ ⊗ᴷ γ = K-ext (λ x → K-map (λ y → x , y) (γ x)) ϕ

 remarkᴷ : {X : Type} {Xf : X → 𝕋}
           (ϕ : K R X)
           (ϕf : (x : X) → 𝓚 R (Xf x))
         → K-sequence {X ∷ Xf} (ϕ :: ϕf) ∼ ϕ ⊗ᴷ (λ x → K-sequence {Xf x} (ϕf x))
 remarkᴷ ϕ f q = refl

\end{code}

The following is Definition 3 of the above reference [1].

A game is defined by a game tree Xt, a type R of outcomes, a
quantifier tree ϕt and an outcome function q:

\begin{code}

record Game : Type₁ where
 constructor game
 field
  Xt  : 𝕋
  R   : Type
  q   : Path Xt → R
  ϕt  : 𝓚 R Xt

open Game

\end{code}

We can think of Xt as the rules of the game, and R, ϕt and q as the
objective of the game.

We define the optimal outcome of a game to be the sequencing of its
quantifiers applied to the outcome function (Theorem 3.1 of [1]).

\begin{code}

optimal-outcome : (G : Game) → R G
optimal-outcome (game R Xt q ϕt) = K-sequence ϕt q

\end{code}

A strategy defines how to pick a path of a tree. The type Strategy of
all possible strategies is constructed as follows (Definition 4 of [1]):

\begin{code}

Strategy : 𝕋 -> Type
Strategy []       = 𝟙
Strategy (X ∷ Xf) = X × ((x : X) → Strategy (Xf x))

\end{code}

 ⋆ σ ranges over the type Strategy Xt of strategies for a
   dependent-type tree Xt.

 ⋆ σf ranges over the type (x : X) → Strategy (Xf x) of strategy
   forests for a dependent-type forest Xf.

We get a path in the tree by following any given strategy:

\begin{code}

strategic-path : {Xt : 𝕋} → Strategy Xt → Path Xt
strategic-path {[]}     ⟨⟩        = ⟨⟩
strategic-path {X ∷ Xf} (x :: σf) = x :: strategic-path {Xf x} (σf x)

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

is-sgpe : {Xt : 𝕋} {R : Type} → 𝓚 R Xt → (Path Xt → R) → Strategy Xt → Type
is-sgpe {[]}     ⟨⟩        q ⟨⟩         = 𝟙
is-sgpe {X ∷ Xf} (ϕ :: ϕf) q (x₀ :: σf) =

      (q (x₀ :: strategic-path (σf x₀)) ＝ ϕ (λ x → q (x :: strategic-path (σf x))))
    ×
      ((x : X) → is-sgpe {Xf x} (ϕf x) (λ (xs : Path (Xf x)) → q (x :: xs)) (σf x))

\end{code}

In the above definition:

 ⋆ If the game tree is empty, then the strategy is empty, and we say
   that it is true that it is in sgpe, where "true" is represented by
   the unit type 𝟙 in propositions-as-types.

 ⋆ If the game tree has a root X followed by a forest Xf, then the
   strategy must be of the form x₀ :: σf, where x₀ is the first move
   according to the strategy, and where σf is a forest of strategies
   that depends on a deviation x.

   So the first part

     q (x₀ :: strategic-path (σf x₀)) ＝ ϕ (λ x → q (x :: strategic-path (σf x)))

   of the definition is as in the comment above, but with a partial
   play of length k=0, and the second (inductive) part, says that the
   substrategy σf x, for any deviation x, is in subgame perfect
   equilibrium in the subgame

     (Xf x , R , ϕf x , λ (xs : Path (Xf x)) → q (x :: xs)).

As discussed above, we say that a strategy for a game is optimal if it
is in subgame perfect equilibrium.

\begin{code}

is-optimal : (G : Game) (σ : Strategy (Xt G)) → Type
is-optimal (game Xt R ϕt q) σ = is-sgpe {Xt} {R} q ϕt σ

\end{code}

The main lemma is that the optimal outcome is the same thing as the
application of the outcome function to the path induced by a strategy
in perfect subgame equilibrium.

The following is Theorem 3.1 of reference [1].

\begin{code}

sgpe-lemma : (Xt : 𝕋) {R : Type} (ϕt : 𝓚 R Xt) (q : Path Xt → R) (σ : Strategy Xt)
           → is-sgpe ϕt q σ
           → K-sequence ϕt q ＝ q (strategic-path σ)
sgpe-lemma []       ⟨⟩        q ⟨⟩        ⟨⟩       = refl
sgpe-lemma (X ∷ Xf) (ϕ :: ϕt) q (a :: σf) (h :: t) = γ
 where
  observation-t : type-of t ＝ ((x : X) → is-sgpe (ϕt x) (λ xs → q (x :: xs)) (σf x))
  observation-t = refl

  IH : (x : X) → K-sequence (ϕt x) (λ xs → q (x :: xs)) ＝ q (x :: strategic-path (σf x))
  IH x = sgpe-lemma (Xf x) (ϕt x) (λ (xs : Path (Xf x)) → q (x :: xs)) (σf x) (t x)

  γ = ϕ (λ x → K-sequence (ϕt x) (λ xs → q (x :: xs))) ＝⟨ ap ϕ (dfunext fe IH) ⟩
      ϕ (λ x → q (x :: strategic-path (σf x)))         ＝⟨ h ⁻¹ ⟩
      q (a :: strategic-path (σf a))                   ∎

\end{code}

This can be reformulated as follows in terms of the type of games:

\begin{code}

equilibrium-theorem : (G : Game) (σ : Strategy (Xt G))
                    → is-optimal G σ
                    → optimal-outcome G ＝ q G (strategic-path σ)
equilibrium-theorem (game Xt R ϕt q) = sgpe-lemma Xt q ϕt

\end{code}

We now show how to use selection functions to compute a sgpe strategy.

Selection functions, as in Section 2 of reference [1]:

\begin{code}

J : Type → Type → Type
J R X = (X → R) → X

\end{code}

𝓙 assigns selection functions to the nodes.

\begin{code}

𝓙 :  Type → 𝕋 → Type
𝓙 R []       = 𝟙
𝓙 R (X ∷ Xf) = J R X × ((x : X) → 𝓙 R (Xf x))

\end{code}

 ⋆ ε ranges over the type J R X of selection functions.
 ⋆ εt ranges over the type 𝓙 R Xt of selection-function trees.
 ⋆ εf ranges over the type (x : X) → 𝓙 R (Xf x) of selection-function forests.

Sequencing selection functions, as constructed in Definition 12 of
reference [1], but using our tree representation of games instead:

\begin{code}

J-sequence₀ : {Xt : 𝕋} {R : Type} → 𝓙 R Xt → J R (Path Xt)
J-sequence₀ {[]}     ⟨⟩        q = ⟨⟩
J-sequence₀ {X ∷ Xf} (ε :: εf) q = h :: t h
 where
  t : (x : X) → Path (Xf x)
  t x = J-sequence₀ {Xf x} (εf x) (λ xs → q (x :: xs))

  h : X
  h = ε (λ x → q (x :: t x))

module remark-about-J-sequence (R : Type) where

 ηᴶ : {X : Type} → X → J R X
 ηᴶ x p = x

 J-ext : {X Y : Type} → (X → J R Y) → J R X → J R Y
 J-ext f ε p = f (ε (λ x → p (f x p))) p

 J-map : {X Y : Type} → (X → Y) → J R X → J R Y
 J-map f = J-ext (ηᴶ ∘ f)

 _⊗ᴶ_ : {X : Type} {Y : X → Type}
      → J R X
      → ((x : X) → J R (Y x))
      → J R (Σ x ꞉ X , Y x)
 ϕ ⊗ᴶ δ = J-ext (λ x → J-map (λ y → x , y) (δ x)) ϕ

 remarkᴶ : {X : Type} {Xf : X → 𝕋}
           (ϕ : J R X)
           (ϕf : (x : X) → 𝓙 R (Xf x))
         → J-sequence₀ {X ∷ Xf} (ϕ :: ϕf) ∼ ϕ ⊗ᴶ (λ x → J-sequence₀ {Xf x} (ϕf x))
 remarkᴶ ϕ f q = refl

\end{code}

Try to make faster, exploiting Agda's evaluation strategy, but this
doesn't seem to make any difference:

\begin{code}

J-sequence₁ : {Xt : 𝕋} {R : Type} → 𝓙 R Xt → J R (Path Xt)
J-sequence₁ {[]}     ⟨⟩        q = ⟨⟩
J-sequence₁ {X ∷ Xf} (ε :: εf) q = γ
 where
  t : (x : X) → Path (Xf x)
  t x = J-sequence₁ {Xf x} (εf x) (λ xs → q (x :: xs))

  ν : X → Path (X ∷ Xf)
  ν x = x :: t x

  x₀ : X
  x₀ = ε (λ x → q (ν x))

  γ : Path (X ∷ Xf)
  γ = ν x₀

\end{code}

Or this:

\begin{code}

J-sequence₂ : {Xt : 𝕋} {R : Type} → 𝓙 R Xt → J R (Path Xt)
J-sequence₂ {[]}     _         q = ⟨⟩
J-sequence₂ {X ∷ Xf} (ε :: εf) q = ν (ε (λ x → q (ν x)))
 where
  ν : X → Path (X ∷ Xf)
  ν x = x :: J-sequence₂ {Xf x} (εf x) (λ xs → q (x :: xs))

J-sequence = J-sequence₂

\end{code}

We now convert a selection function into a quantifier as in
Definition 10 of [1]:

\begin{code}

overline : {X R : Type} → J R X → K R X
overline ε = λ p → p (ε p)

\end{code}

The following is the application of overline to each selection
function of a tree:

\begin{code}

Overline : {Xt : 𝕋} {R : Type} → 𝓙 R Xt → 𝓚 R Xt
Overline {[]}     ⟨⟩        = ⟨⟩
Overline {X ∷ Xf} (ε :: εs) = overline ε :: (λ x → Overline {Xf x} (εs x))

\end{code}

The following, which defines a strategy from given selection
functions, is defined in Theorem 5.4 of [1], with the difference that
here, for the moment, we consider only single-valued quantifiers.

\begin{code}

selection-strategy : {Xt : 𝕋} {R : Type} → 𝓙 R Xt → (Path Xt → R) → Strategy Xt
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

_are-selections-of_ : {Xt : 𝕋} {R : Type} → 𝓙 R Xt → 𝓚 R Xt → Type
_are-selections-of_ {[]}     ⟨⟩        ⟨⟩        = 𝟙
_are-selections-of_ {X ∷ Xf} (ε :: εf) (ϕ :: ϕf) = (ε is-a-selection-of ϕ)
                                                 × ((x : X) → (εf x) are-selections-of (ϕf x))

observation : {Xt : 𝕋} {R : Type} (εt : 𝓙 R Xt) (ϕt : 𝓚 R Xt)
            → εt are-selections-of ϕt
            → Overline εt ＝ ϕt
observation {[]}     ⟨⟩        ⟨⟩        ⟨⟩        = refl
observation {X ∷ Xf} (ε :: εf) (ϕ :: ϕf) (a :: af) = γ
 where
  IH : (x : X) → Overline (εf x) ＝ ϕf x
  IH x = observation {Xf x} (εf x) (ϕf x) (af x)

  I : overline ε ＝ ϕ
  I = dfunext fe a

  II : (λ x → Overline (εf x)) ＝ ϕf
  II = dfunext fe IH

  γ : overline ε :: (λ x → Overline (εf x)) ＝ ϕ :: ϕf
  γ = ap₂ _::_ I II

\end{code}

Notice that the converse is also true, that is, if Overline εt ＝ ϕt
then εt are selections of ϕt, but we don't need this fact here.

\begin{code}

crucial-lemma : {Xt : 𝕋} {R : Type} (εt : 𝓙 R Xt) (q : Path Xt → R)
              → J-sequence εt q
              ＝ strategic-path (selection-strategy εt q)
crucial-lemma {[]}     ⟨⟩           q = refl
crucial-lemma {X ∷ Xf} εt@(ε :: εf) q = γ
 where
  t : (x : X) → Path (Xf x)
  t x = J-sequence {Xf x} (εf x) (λ xs → q (x :: xs))

  x₀ : X
  x₀ = path-head (J-sequence εt q)

  remark-used-implicitly : x₀ ＝ ε (λ x → q (x :: t x))
  remark-used-implicitly = refl

  σf : (x : X) → Strategy (Xf x)
  σf x = selection-strategy {Xf x} (εf x) (λ xs → q (x :: xs))

  IH : t x₀ ＝ strategic-path (σf x₀)
  IH = crucial-lemma (εf x₀) (λ xs → q (x₀ :: xs))

  γ : x₀ :: t x₀ ＝ x₀ :: strategic-path (σf x₀)
  γ = ap (x₀ ::_) IH

selection-strategy-lemma : {Xt : 𝕋} {R : Type} (εt : 𝓙 R Xt) (q : Path Xt → R)
                         → is-sgpe (Overline εt) q (selection-strategy εt q)
selection-strategy-lemma {[]}     {R} ⟨⟩        q = ⟨⟩
selection-strategy-lemma {X ∷ Xf} {R} (ε :: εf) q = h :: t
 where
  f g : X → R
  f x = q (x :: J-sequence (εf x) (λ xs → q (x :: xs)))
  g x = q (x :: strategic-path (selection-strategy (εf x) (λ xs → q (x :: xs))))

  I : (x : X) → J-sequence (εf x) (λ xs → q (x :: xs))
              ＝ strategic-path (selection-strategy (εf x) (λ xs → q (x :: xs)))
  I x = crucial-lemma (εf x) (λ xs → q (x :: xs))

  II : f ＝ g
  II = dfunext fe (λ x → ap (λ - → q (x :: -)) (I x))

  h : g (ε f) ＝ g (ε g)
  h = ap (g ∘ ε) II

  t : (x : X) → is-sgpe
                  (Overline (εf x))
                  (λ xs → q (x :: xs))
                  (selection-strategy (εf x) (λ xs → q (x :: xs)))
  t x = selection-strategy-lemma (εf x) (λ xs → q (x :: xs))

\end{code}

The following, which shows how to use selection functions to compute
optimal strategies, corresponds to Theorem 6.2 of [1].

\begin{code}

selection-strategy-theorem : {Xt : 𝕋} {R : Type} (εt : 𝓙 R Xt) (ϕt : 𝓚 R Xt) (q : Path Xt → R)
                           → εt are-selections-of ϕt
                           → is-sgpe ϕt q (selection-strategy εt q)
selection-strategy-theorem εt ϕt q a = III
 where
  I : Overline εt ＝ ϕt
  I = observation εt ϕt a

  II : is-sgpe (Overline εt) q (selection-strategy εt q)
  II = selection-strategy-lemma εt q

  III : is-sgpe ϕt q (selection-strategy εt q)
  III = transport (λ - → is-sgpe - q (selection-strategy εt q)) I II


Selection-Strategy-Theorem : (G : Game) (εt : 𝓙 (R G) (Xt G))
                           → εt are-selections-of (ϕt G)
                           → is-optimal G (selection-strategy εt (q G))
Selection-Strategy-Theorem (game Xt R ϕt q) εt = selection-strategy-theorem εt q ϕt

\end{code}

Incomplete example:

\begin{code}

module permutations-example where

 open import MLTT.NonSpartanMLTTTypes

 no-repetitions : (n : ℕ) (X : Type) → 𝕋
 no-repetitions 0        X = []
 no-repetitions (succ n) X = X ∷ λ (x : X) → no-repetitions n (Σ y ꞉ X , y ≠ x)

 Permutations : ℕ → Type
 Permutations n = Path (no-repetitions n (Fin n))

 example-permutation2 : Permutations 2
 example-permutation2 = 𝟎 :: ((𝟏 , (λ ())) :: ⟨⟩)

 example-permutation3 : Permutations 3
 example-permutation3 = 𝟐 :: ((𝟏 :: (λ ())) :: (((𝟎 , (λ ())) , (λ ())) :: ⟨⟩))

\end{code}

We use the type GameJ to present games equipped with selection
functions, as in some examples, such as tic-tac-toe this is easier
than to give a game directly.

\begin{code}

data GameJ (R : Type) : Type₁ where
  leaf   : R → GameJ R
  branch : (X : Type) (Xf : X → GameJ R) (ε : J R X) → GameJ R


dtt : {R : Type} → GameJ R → 𝕋
dtt (leaf x)        = []
dtt (branch X Xf ε) = X ∷ λ x → dtt (Xf x)

predicate : {R : Type} (Γ : GameJ R) → Path (dtt Γ) → R
predicate (leaf r)        ⟨⟩        = r
predicate (branch X Xf ε) (x :: xs) = predicate (Xf x) xs

selections : {R : Type} (Γ : GameJ R) → 𝓙 R (dtt Γ)
selections (leaf r)        = ⟨⟩
selections (branch X Xf ε) = ε :: (λ x → selections (Xf x))

quantifiers : {R : Type} (Γ : GameJ R) → 𝓚 R (dtt Γ)
quantifiers (leaf r)        = ⟨⟩
quantifiers (branch X Xf ε) = overline ε :: (λ x → quantifiers (Xf x))

Game-from-GameJ : {R : Type} → GameJ R → Game
Game-from-GameJ {R} Γ = game (dtt Γ) R (predicate Γ) (quantifiers Γ)

strategyJ : {R : Type} (Γ : GameJ R) → Strategy (dtt Γ)
strategyJ Γ = selection-strategy (selections Γ) (predicate Γ)

Selection-Strategy-TheoremJ : {R : Type} (Γ : GameJ R)
                            → is-optimal (Game-from-GameJ Γ) (strategyJ Γ)
Selection-Strategy-TheoremJ {R} Γ = γ
 where
  δ : (Γ : GameJ R) → (selections Γ) are-selections-of (quantifiers Γ)
  δ (leaf r)        = ⟨⟩
  δ (branch X Xf ε) = (λ p → refl) , (λ x → δ (Xf x))

  γ : is-optimal (Game-from-GameJ Γ) (strategyJ Γ)
  γ = Selection-Strategy-Theorem (Game-from-GameJ Γ) (selections Γ) (δ Γ)

\end{code}

The following is used in conjunction with GameJ to build certain games
in a convenient way.

\begin{code}

build-GameJ : {R          : Type}
              (draw       : R)
              (Board      : Type)
              (transition : Board → R + (Σ M ꞉ Type , (M → Board) × J R M))
              (n          : ℕ)
              (b          : Board)
            → GameJ R
build-GameJ {R} draw Board transition n b = h n b
 where
  h : ℕ → Board → GameJ R
  h 0        b = leaf draw
  h (succ n) b = g (transition b) refl
   where
    g : (f : R + (Σ M ꞉ Type , (M → Board) × J R M)) → transition b ＝ f → GameJ R
    g (inl r)              p = leaf r
    g (inr (M , play , ε)) p = branch M Xf ε
     where
      Xf : M → GameJ R
      Xf m = h n (play m)

build-Game : {R          : Type}
             (draw       : R)
             (Board      : Type)
             (transition : Board → R + (Σ M ꞉ Type , (M → Board) × J R M))
             (n          : ℕ)
             (b          : Board)
           → Game
build-Game draw Board transition n b = Game-from-GameJ (build-GameJ draw Board transition n b)

\end{code}

Example: Tic-tac-toe. We have two versions.

\begin{code}

tic-tac-toe₁ : Game
tic-tac-toe₁ = build-Game draw Board transition 9 board₀
 where
  open import TypeTopology.CompactTypes
  open import UF.Subsingletons
  open import TypeTopology.DiscreteAndSeparated
  open import UF.Miscelanea

  open import MLTT.NonSpartanMLTTTypes hiding (Fin ; 𝟎 ; 𝟏 ; 𝟐 ; 𝟑 ; 𝟒 ; 𝟓 ; 𝟔 ; 𝟕 ; 𝟖 ; 𝟗)
  open import MLTT.Fin
  open import MLTT.Fin-Properties

  data Player : Type where
   X O : Player

  opponent : Player → Player
  opponent X = O
  opponent O = X

  𝟛 = Fin 3

  pattern X-wins = 𝟎
  pattern draw   = 𝟏
  pattern O-wins = 𝟐

  Grid   = 𝟛 × 𝟛
  Matrix = Grid → Maybe Player
  Board  = Player × Matrix

\end{code}

Convention: in a board (p , A), p is the opponent of the the current player.

\begin{code}

  Grid-is-discrete : is-discrete Grid
  Grid-is-discrete = ×-is-discrete Fin-is-discrete Fin-is-discrete

  Grid-compact : Compact Grid {𝓤₀}
  Grid-compact = ×-Compact Fin-Compact Fin-Compact

  board₀ : Board
  board₀ = X , (λ _ → Nothing)

  Move : Board → Type
  Move (_ , A) = Σ g ꞉ Grid , A g ＝ Nothing

  Move-decidable : (b : Board) → decidable (Move b)
  Move-decidable (_ , A) = Grid-compact
                            (λ g → A g ＝ Nothing)
                            (λ g → Nothing-is-isolated' (A g))

  Move-compact : (b : Board) → Compact (Move b)
  Move-compact (x , A) = complemented-subset-of-compact-type
                          Grid-compact
                          (λ g → Nothing-is-isolated' (A g))
                          (λ g → Nothing-is-h-isolated' (A g))

  selection : (b : Board) → Move b → J 𝟛 (Move b)
  selection b@(X , A) m p = pr₁ (compact-argmax p (Move-compact b) m)
  selection b@(O , A) m p = pr₁ (compact-argmin p (Move-compact b) m)

  _is_ : Maybe Player → Player → Bool
  Nothing is _ = false
  Just X  is X = true
  Just O  is X = false
  Just X  is O = false
  Just O  is O = true

  infix 30 _is_

  wins : Player → Matrix → Bool
  wins p A = line || col || diag
   where
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

  update : (p : Player) (A : Matrix)
         → Move (p , A) → Matrix
  update p A (m , _) m' = f (Grid-is-discrete m m')
   where
    f : decidable (m ＝ m') → Maybe Player
    f (inl _) = Just p
    f (inr _) = A m'

  play : (b : Board) (m : Move b) → Board
  play (p , A) m = opponent p , update p A m

  transition : Board → 𝟛 + (Σ M ꞉ Type , (M → Board) × J 𝟛 M)
  transition (p , A) = f p A (wins p A) refl
   where
    f : (p : Player) (A : Matrix) (b : Bool) → wins p A ＝ b
      → 𝟛 + (Σ M ꞉ Type , (M → Board) × J 𝟛 M)
    f X A true e  = inl X-wins
    f O A true e  = inl O-wins
    f p A false e = Cases (Move-decidable (p , A))
                     (λ (g , e) → inr (Move (p , A) ,
                                       (λ m → opponent p , update p A m) ,
                                       selection (p , A) (g , e)))
                     (λ ν → inl draw)

t₁ : R tic-tac-toe₁
t₁ = optimal-outcome tic-tac-toe₁

\end{code}

The above computation takes too long, due to the use of brute-force search.

The following is another, more efficient, version of tic-tac-toe, with
a more refined exhaustive search that allows us to compute answers.

\begin{code}

data 𝟛 : Type where
 O-wins draw X-wins : 𝟛

tic-tac-toe₂J : GameJ 𝟛
tic-tac-toe₂J = build-GameJ draw Board transition 9 board₀
 where
  flip : 𝟛 → 𝟛
  flip O-wins = X-wins
  flip draw   = draw
  flip X-wins = O-wins

  data Player : Type where
   O X : Player

  open import MLTT.NonSpartanMLTTTypes
  open list-util

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

  argmin : (m : Cell) (ms : List Cell) → 𝟛 → (Move (m ∷ ms) → 𝟛) → Move (m ∷ ms)
  argmin m ms r q = argmax m ms (flip r) (λ xs → flip (q xs))

  arg : Player → (ms : List Cell) → empty ms ＝ false →  J 𝟛 (Move ms)
  arg _ []       e q = 𝟘-elim (true-is-not-false e)
  arg X (m ∷ ms) e q = argmax m ms (q (m , ||-left-intro (m is-in ms) (==-refl m))) q
  arg O (m ∷ ms) e q = argmin m ms (q (m , ||-left-intro (m is-in ms) (==-refl m))) q

  play : (b : Board) → Move (available-moves b) → Board
  play (board X as xs os) (c , e) = board O (remove-first c as) (insert c xs) os
  play (board O as xs os) (c , e) = board X (remove-first c as) xs            (insert c os)

  transition : Board → 𝟛 + (Σ M ꞉ Type , (M → Board) × J 𝟛 M)
  transition b@(board next as xs os) =
   if wins b
   then inl (opponent-wins next)
   else Bool-equality-cases (empty as)
         (λ (_ : empty as ＝ true)  → inl draw)
         (λ (e : empty as ＝ false) → inr (Move as , play b , arg next as e))

tic-tac-toe₂ : Game
tic-tac-toe₂ = Game-from-GameJ tic-tac-toe₂J

t₂ : R tic-tac-toe₂
t₂ = optimal-outcome tic-tac-toe₂

s₂ : Path (Xt tic-tac-toe₂)
s₂ = strategic-path (selection-strategy (selections tic-tac-toe₂J) (q tic-tac-toe₂))

u₂ : Path (Xt tic-tac-toe₂)
u₂ = J-sequence (selections tic-tac-toe₂J) (q tic-tac-toe₂)

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

open import NonSpartanMLTTTypes

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

More tests.

\begin{code}

module test where

 open import MLTT.NonSpartanMLTTTypes

 ε₂ : J Bool Bool
 ε₂ p = p true

 h : ℕ → 𝕋
 h 0        = []
 h (succ n) = Bool ∷ λ _ → h n

 εs : (n : ℕ) → 𝓙 Bool (h n)
 εs 0        = ⟨⟩
 εs (succ n) = ε₂ :: λ _ → εs n

 ε : (n : ℕ) → J Bool (Path (h n))
 ε n = J-sequence (εs n)

 qq : (n : ℕ) → Path (h n) → Bool
 qq 0        ⟨⟩        = true
 qq (succ n) (x :: xs) = not x && qq n xs

 test : (n : ℕ) → Path (h n)
 test n = ε n (qq n)

\end{code}

TODO. Generalize the above to multi-valued quantifiers, as in [1], using monads.

\begin{code}

data GameK (R : Type) : Type₁ where
  leaf   : R → GameK R
  branch : (X : Type) (Xf : X → GameK R) (ϕ : K R X) → GameK R

\end{code}

TODO. GameK ≃ Game and we have a map GameJ → GameK.

TODO. Define game isomorphism (and possibly homomorphism more generally).

\begin{code}

data 𝕋' (X : Type) : Type₁ where
  []  : 𝕋' X
  _∷_ : (A : X → Type) (Xf : (x : X) → A x → 𝕋' X) → 𝕋' X

record Game⁻ : Type₁ where
 constructor game⁻
 field
  Xt  : 𝕋
  R   : Type
  q   : Path Xt → R

\end{code}

TODO. Game⁻ ≃ (Σ R : Type, D𝕋 R) for a suitable definition of
D𝕋. Idea: In Game⁻, we know how to play the game, but we don't know
what the objective of the game is.

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

We assume a given type R of outcomes for games as a module parameter.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline #-} -- --exact-split

open import MLTT.Spartan hiding (J)
open import UF.Base
open import UF.FunExt

module Games.FiniteHistoryDependent
        (R : Type)
        (fe : Fun-Ext)
       where

\end{code}

The following module defines the main data structure we use in order
to represent the above kind of game:

\begin{code}

open import Games.TypeTrees

\end{code}

Quantifiers as in Section 1 of reference [1]:

\begin{code}

K : Type → Type
K X = (X → R) → R

\end{code}

In the same way as the type of moves at a given stage of the game
depends on the previously played moves, so do the quantifiers and
selection functions.

𝓚 assigns a quantifier to each node in a given tree:

\begin{code}

𝓚 : 𝕋 → Type
𝓚 []       = 𝟙
𝓚 (X ∷ Xf) = K X × ((x : X) → 𝓚 (Xf x))

\end{code}

 ⋆ ϕ  ranges over the type K X of quantifiers.
 ⋆ ϕt ranges over the type 𝓚 Xt of quantifier trees.
 ⋆ ϕf ranges over the type (x : X) → 𝓚 (Xf x) of quantifier forests.


Sequencing quantifiers, as constructed in Definition 2 of reference [1],
but using our tree representation of games instead:

\begin{code}

sub : {X : Type} {Y : X → Type} → (Σ Y → R) → (x : X) → Y x → R
sub q x xs = q (x , xs)

_⊗ᴷ_ : {X : Type} {Y : X → Type}
     → K X
     → ((x : X) → K (Y x))
     → K (Σ x ꞉ X , Y x)
(ϕ ⊗ᴷ γ) q = ϕ (λ x → γ x (sub q x))

K-sequence : {Xt : 𝕋} → 𝓚 Xt → K (Path Xt)
K-sequence {[]}     ⟨⟩        = λ q → q ⟨⟩
K-sequence {X ∷ Xf} (ϕ :: ϕf) = ϕ ⊗ᴷ (λ x → K-sequence {Xf x} (ϕf x))

\end{code}

We remark that ⊗ᴷ can be defined from the strong monad structure on K:

\begin{code}

module remark-about-⊗ᴷ (R : Type) where

 ηᴷ : {X : Type} → X → K X
 ηᴷ x p = p x

 K-ext : {X Y : Type} → (X → K Y) → K X → K Y
 K-ext f ϕ p = ϕ (λ x → f x p)

 K-map : {X Y : Type} → (X → Y) → K X → K Y
 K-map f = K-ext (ηᴷ ∘ f)

 remarkᴷ : {X : Type} {Y : X → Type}
           (ϕ : K X)
           (γ : (x : X) → K (Y x))
         → ϕ ⊗ᴷ γ ∼ K-ext (λ x → K-map (λ y → x , y) (γ x)) ϕ
 remarkᴷ ϕ γ q = refl

\end{code}

The following is Definition 3 of the above reference [1].

A game is defined by a game tree Xt, a type R of outcomes, a
quantifier tree ϕt and an outcome function q:

\begin{code}

record Game : Type₁ where
 constructor game
 field
  Xt  : 𝕋
  q   : Path Xt → R
  ϕt  : 𝓚 Xt

open Game public

\end{code}

We can think of Xt as the rules of the game, and R, ϕt and q as the
objective of the game.

We define the optimal outcome of a game to be the sequencing of its
quantifiers applied to the outcome function (Theorem 3.1 of [1]).

\begin{code}

optimal-outcome : (G : Game) → R
optimal-outcome (game Xt q ϕt) = K-sequence ϕt q

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

is-sgpe : {Xt : 𝕋} → 𝓚 Xt → (Path Xt → R) → Strategy Xt → Type
is-sgpe {[]}     ⟨⟩        q ⟨⟩         = 𝟙
is-sgpe {X ∷ Xf} (ϕ :: ϕf) q (x₀ :: σf) =

      (q (x₀ :: strategic-path (σf x₀)) ＝ ϕ (λ x → q (x :: strategic-path (σf x))))
    ×
      ((x : X) → is-sgpe {Xf x} (ϕf x) (sub q x) (σf x))

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

     (Xf x , R , ϕf x , sub q x).

As discussed above, we say that a strategy for a game is optimal if it
is in subgame perfect equilibrium.

\begin{code}

is-optimal : (G : Game) (σ : Strategy (Xt G)) → Type
is-optimal (game Xt ϕt q) σ = is-sgpe {Xt} q ϕt σ

\end{code}

The main lemma is that the optimal outcome is the same thing as the
application of the outcome function to the path induced by a strategy
in perfect subgame equilibrium.

The following is Theorem 3.1 of reference [1].

\begin{code}

sgpe-lemma : (Xt : 𝕋) (ϕt : 𝓚 Xt) (q : Path Xt → R) (σ : Strategy Xt)
           → is-sgpe ϕt q σ
           → K-sequence ϕt q ＝ q (strategic-path σ)
sgpe-lemma []       ⟨⟩        q ⟨⟩        ⟨⟩       = refl
sgpe-lemma (X ∷ Xf) (ϕ :: ϕt) q (a :: σf) (h :: t) = γ
 where
  observation-t : type-of t ＝ ((x : X) → is-sgpe (ϕt x) (sub q x) (σf x))
  observation-t = refl

  IH : (x : X) → K-sequence (ϕt x) (sub q x) ＝ q (x :: strategic-path (σf x))
  IH x = sgpe-lemma (Xf x) (ϕt x) (sub q x) (σf x) (t x)

  γ = ϕ (λ x → K-sequence (ϕt x) (sub q x))    ＝⟨ ap ϕ (dfunext fe IH) ⟩
      ϕ (λ x → q (x :: strategic-path (σf x))) ＝⟨ h ⁻¹ ⟩
      q (a :: strategic-path (σf a))           ∎

\end{code}

This can be reformulated as follows in terms of the type of games:

\begin{code}

equilibrium-theorem : (G : Game) (σ : Strategy (Xt G))
                    → is-optimal G σ
                    → optimal-outcome G ＝ q G (strategic-path σ)
equilibrium-theorem (game Xt ϕt q) = sgpe-lemma Xt q ϕt

\end{code}

We now show how to use selection functions to compute a sgpe strategy.

Selection functions, as in Section 2 of reference [1]:

\begin{code}

J : Type → Type
J X = (X → R) → X

\end{code}

𝓙 assigns selection functions to the nodes.

\begin{code}

𝓙 : 𝕋 → Type
𝓙 []       = 𝟙
𝓙 (X ∷ Xf) = J X × ((x : X) → 𝓙 (Xf x))

\end{code}

 ⋆ ε ranges over the type J X of selection functions.
 ⋆ εt ranges over the type 𝓙 Xt of selection-function trees.
 ⋆ εf ranges over the type (x : X) → 𝓙 (Xf x) of selection-function forests.

Sequencing selection functions, as constructed in Definition 12 of
reference [1], but using our tree representation of games instead:

\begin{code}

_⊗ᴶ_ : {X : Type} {Y : X → Type}
     → J X
     → ((x : X) → J (Y x))
     → J (Σ x ꞉ X , Y x)
(ε ⊗ᴶ δ) q = a :: b a
 where
  b = λ x → δ x (sub q x)
  a = ε (λ x → q (x :: b x))

J-sequence : {Xt : 𝕋} → 𝓙 Xt → J (Path Xt)
J-sequence {[]}     ⟨⟩        = λ q → ⟨⟩
J-sequence {X ∷ Xf} (ε :: εf) = ε ⊗ᴶ (λ x → J-sequence {Xf x} (εf x))

\end{code}

We remark that ⊗ᴶ can be defined from the strong monad structure on J,
as is the case for K:

\begin{code}

module remark-about-⊗ᴶ (R : Type) where

 ηᴶ : {X : Type} → X → J X
 ηᴶ x p = x

 J-ext : {X Y : Type} → (X → J Y) → J X → J Y
 J-ext f ε p = f (ε (λ x → p (f x p))) p

 J-map : {X Y : Type} → (X → Y) → J X → J Y
 J-map f = J-ext (ηᴶ ∘ f)

 remarkᴶ : {X : Type} {Y : X → Type}
           (ε : J X)
           (δ : (x : X) → J (Y x))
         → ε ⊗ᴶ δ ∼ J-ext (λ x → J-map (λ y → x , y) (δ x)) ε
 remarkᴶ ε δ q = refl

\end{code}

The following, which defines a strategy from given selection
functions, is defined in Theorem 5.4 of [1], with the difference that
here, for the moment, we consider only single-valued quantifiers.

\begin{code}

selection-strategy : {Xt : 𝕋} → 𝓙 Xt → (Path Xt → R) → Strategy Xt
selection-strategy {[]}     ⟨⟩           q = ⟨⟩
selection-strategy {X ∷ Xf} εt@(ε :: εf) q = x₀ :: σf
 where
  x₀ : X
  x₀ = path-head (J-sequence εt q)

  σf : (x : X) → Strategy (Xf x)
  σf x = selection-strategy {Xf x} (εf x) (sub q x)

\end{code}

We now convert a selection function into a quantifier as in
Definition 10 of [1]:

\begin{code}

overline : {X : Type} → J X → K X
overline ε = λ p → p (ε p)

\end{code}

The following definition is in Section 1 on [1].

\begin{code}

_is-a-selection-of_ : {X : Type} → J X → K X → Type
ε is-a-selection-of ϕ = overline ε ∼ ϕ

\end{code}

We generalize it to selection-function and quantifier trees in the
obvious way, by induction:

\begin{code}

_are-selections-of_ : {Xt : 𝕋} → 𝓙 Xt → 𝓚 Xt → Type
_are-selections-of_ {[]}     ⟨⟩        ⟨⟩        = 𝟙
_are-selections-of_ {X ∷ Xf} (ε :: εf) (ϕ :: ϕf) = (ε is-a-selection-of ϕ)
                                                 × ((x : X) → (εf x) are-selections-of (ϕf x))

\end{code}

The following is the application of overline to each selection
function of a tree:

\begin{code}

Overline : {Xt : 𝕋} → 𝓙 Xt → 𝓚 Xt
Overline {[]}     ⟨⟩        = ⟨⟩
Overline {X ∷ Xf} (ε :: εs) = overline ε :: (λ x → Overline {Xf x} (εs x))

\end{code}

The following is proved by straightforward induction on trees:

\begin{code}

observation : {Xt : 𝕋} (εt : 𝓙 Xt) (ϕt : 𝓚 Xt)
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

crucial-lemma : {Xt : 𝕋} (εt : 𝓙 Xt) (q : Path Xt → R)
              → J-sequence εt q
              ＝ strategic-path (selection-strategy εt q)
crucial-lemma {[]}     ⟨⟩           q = refl
crucial-lemma {X ∷ Xf} εt@(ε :: εf) q =
 J-sequence (ε :: εf) q                          ＝⟨ refl ⟩
 (ε ⊗ᴶ (λ x → J-sequence {Xf x} (εf x))) q       ＝⟨ refl ⟩
 a :: b a                                        ＝⟨ refl ⟩
 a :: J-sequence {Xf a} (εf a) (sub q a)         ＝⟨ ap (a ::_) IH ⟩
 a :: strategic-path (σf a)                      ＝⟨ refl ⟩
 strategic-path (selection-strategy (ε :: εf) q) ∎
 where
  b : (x : X) → Path (Xf x)
  b x = J-sequence {Xf x} (εf x) (sub q x)

  a : X
  a = ε (λ x → q (x :: b x))

  σf : (x : X) → Strategy (Xf x)
  σf x = selection-strategy {Xf x} (εf x) (sub q x)

  IH : J-sequence {Xf a} (εf a) (sub q a) ＝ strategic-path (σf a)
  IH = crucial-lemma (εf a) (sub q a)

selection-strategy-lemma : {Xt : 𝕋} (εt : 𝓙 Xt) (q : Path Xt → R)
                         → is-sgpe (Overline εt) q (selection-strategy εt q)
selection-strategy-lemma {[]}     ⟨⟩        q = ⟨⟩
selection-strategy-lemma {X ∷ Xf} (ε :: εf) q = h :: t
 where
  f g : X → R
  f x = q (x :: J-sequence (εf x) (sub q x))
  g x = q (x :: strategic-path (selection-strategy (εf x) (sub q x)))

  I : (x : X) → J-sequence (εf x) (λ xs → q (x :: xs))
              ＝ strategic-path (selection-strategy (εf x) (sub q x))
  I x = crucial-lemma (εf x) (sub q x)

  II : f ＝ g
  II = dfunext fe (λ x → ap (sub q x ) (I x))

  h : g (ε f) ＝ g (ε g)
  h = ap (g ∘ ε) II

  t : (x : X) → is-sgpe
                  (Overline (εf x))
                  (sub q x)
                  (selection-strategy (εf x) (sub q x))
  t x = selection-strategy-lemma (εf x) (sub q x)

\end{code}

The following, which shows how to use selection functions to compute
optimal strategies, corresponds to Theorem 6.2 of [1].

\begin{code}

selection-strategy-theorem : {Xt : 𝕋} (εt : 𝓙 Xt)
                             (ϕt : 𝓚 Xt) (q : Path Xt → R)
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


Selection-Strategy-Theorem : (G : Game) (εt : 𝓙 (Xt G))
                           → εt are-selections-of (ϕt G)
                           → is-optimal G (selection-strategy εt (q G))
Selection-Strategy-Theorem (game Xt ϕt q) εt = selection-strategy-theorem εt q ϕt

\end{code}

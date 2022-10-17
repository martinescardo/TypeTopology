Martin Escardo, Paulo Oliva, 2-27 July 2021

We represent the moves of a history-dependent sequential game by a
dependent-type tree, collected in a type 𝕋.  This is either an empty
tree [] or else has a type X of initial moves at the root, and,
inductively, a family Xf of subtrees indexed by elements of X, which
is written X ∷ Xf. We refer to the family Xf as a forest. We let Xt
range over such trees.

 * Xt ranges over dependent-type trees.
 * Xf ranges over dependent-type forests.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

module Games.TypeTrees where

open import MLTT.Spartan

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

Martin Escardo, 5th April 2024

Demonstration of `remove` and `remove-swap` without Agda's `with`,
regarding a mastodon discussion.
https://mathstodon.xyz/deck/@MartinEscardo/112214064298894127

We use Hedberg to show that any two proofs of equality are themselves
equal, in a discrete type. This is because we want to disable K.

We use function extensionality to show that any two proofs of negation
of equality are themselves equal.

*Challenge* Re-define `remove-swap` below

 * without Hedberg,

 * Without function extensionality,

 * without Agda's `with`,

and still with `--safe` and `--without-K` and all other flags in
typetopology.agda-lib.

(This file is extracted from a larger file about this subject, to be
published in the TypeTopology in the near future.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.DiscreteAndSeparated

module gist.remove-swap
        (fe : Fun-Ext)
        {𝓤 : Universe}
        (X : 𝓤 ̇ )
        (d : is-discrete X)
       where

open import MLTT.List

\end{code}

We first define a conditional `cons` operation, and then we use it to
define `remove`.

\begin{code}

abstract
 ccons : ({x} y : X) → is-decidable (x ＝ y) → List X → List X
 ccons y (inl e) ys = ys
 ccons y (inr u) ys = y ∷ ys

remove : X → List X → List X
remove x []       = []
remove x (y ∷ ys) = ccons y (d x y) (remove x ys)

\end{code}

The following two facts are the specification of `remove`. (See below
for discussion and more verbose proofs that are much clearer.)

\begin{code}

module _ (x y : X) (zs : List X) where

 abstract
  remove-＝ : x ＝ y → remove x (y ∷ zs) ＝ remove x zs
  remove-＝ e = ap (λ - → ccons y - (remove x zs)) (discrete-inl d x y e)

  remove-≠ : x ≠ y → remove x (y ∷ zs) ＝ y ∷ remove x zs
  remove-≠ u = ap (λ - → ccons y - (remove x zs)) (discrete-inr fe d x y u)

\end{code}

A particular case of `remove-＝` occurs more often in practice.

\begin{code}

remove-same : (x : X) (ys : List X) → remove x (x ∷ ys) ＝ remove x ys
remove-same x ys = remove-＝ x x ys refl

\end{code}

And this is our definition of `remove-swap` without `with`. Notice
that the helper function h plays the role of `with`.

\begin{code}

remove-swap : (x y : X) (zs : List X)
            → remove x (remove y zs) ＝ remove y (remove x zs)
remove-swap x y []       = refl
remove-swap x y (z ∷ zs) = h (d x z) (d y z)
 where
  IH : remove x (remove y zs) ＝ remove y (remove x zs)
  IH = remove-swap x y zs

  h : is-decidable (x ＝ z)
    → is-decidable (y ＝ z)
    → remove x (remove y (z ∷ zs)) ＝ remove y (remove x (z ∷ zs))
  h (inl refl) (inl refl) = refl
  h (inl refl) (inr v) =
   remove x (remove y (x ∷ zs)) ＝⟨ ap (remove x) (remove-≠ y x zs v) ⟩
   remove x (x ∷ remove y zs)   ＝⟨ remove-same x (remove y zs) ⟩
   remove x (remove y zs)       ＝⟨ IH ⟩
   remove y (remove x zs)       ＝⟨ ap (remove y) ((remove-same x zs)⁻¹) ⟩
   remove y (remove x (x ∷ zs)) ∎
  h (inr u) (inl refl) =
   remove x (remove y (y ∷ zs)) ＝⟨ ap (remove x) (remove-same y zs) ⟩
   remove x (remove y zs)       ＝⟨ IH ⟩
   remove y (remove x zs)       ＝⟨ (remove-same y (remove x zs))⁻¹ ⟩
   remove y (y ∷ remove x zs)   ＝⟨ ap (remove y) (remove-≠ x y zs u)⁻¹ ⟩
   remove y (remove x (y ∷ zs)) ∎
  h (inr u) (inr v) =
   remove x (remove y (z ∷ zs)) ＝⟨ ap (remove x) (remove-≠ y z zs v) ⟩
   remove x (z ∷ remove y zs)   ＝⟨ remove-≠ x z (remove y zs) u ⟩
   z ∷ remove x (remove y zs)   ＝⟨ ap (z ∷_) IH ⟩
   z ∷ remove y (remove x zs)   ＝⟨ (remove-≠ y z (remove x zs) v)⁻¹ ⟩
   remove y (z ∷ remove x zs)   ＝⟨ (ap (remove y) (remove-≠ x z zs u))⁻¹ ⟩
   remove y (remove x (z ∷ zs)) ∎

\end{code}

I think it's better to be verbose, and this is what we tend to do in
TypeTopology, because we want people to understand what's going on by
reading the code, as much as possible.

The first of the following two proofs use Hedberg (to show that d x y
＝ inl e), and the second one uses Hedberg and, and additionally
function extensionality (to show that d x y = inr u). This is the only
place function extensionality is used in this file. Also notice that
we only use function extensionality for empty-type-valued functions!

\begin{code}

module _ (x y : X) (zs : List X) where

 abstract
  verbose-remove-＝ : x ＝ y → remove x (y ∷ zs) ＝ remove x zs
  verbose-remove-＝ e =
   remove x (y ∷ zs)             ＝⟨refl⟩
   ccons y (d x y) (remove x zs) ＝⟨ ap (λ - → ccons y - (remove x zs)) I ⟩
   ccons y (inl e) (remove x zs) ＝⟨refl⟩
   remove x zs                   ∎
    where
     I : d x y ＝ inl e
     I = discrete-inl d x y e

  verbose-remove-≠ : x ≠ y → remove x (y ∷ zs) ＝ y ∷ remove x zs
  verbose-remove-≠ u =
   remove x (y ∷ zs)             ＝⟨refl⟩
   ccons y (d x y) (remove x zs) ＝⟨ ap (λ - → ccons y - (remove x zs)) I ⟩
   ccons y (inr u) (remove x zs) ＝⟨refl⟩
   y ∷ remove x zs               ∎
    where
     I : d x y ＝ inr u
     I = discrete-inr fe d x y u

\end{code}

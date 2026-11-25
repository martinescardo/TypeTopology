Martin Escardo and Paulo Oliva, originally March - April 2023, with the
proofs November 2026.

Part of the formalization, in Games.AlphaBeta.index, of the paper

  Martín Hötzel Escardó and Paulo Oliva.
  Alpha-Beta Pruning via Monadic Continuations.
  https://doi.org/10.48550/arXiv.2611.32320

The minimizing quantifiers φmin and φ*min are the maximizing
quantifiers of the module Games.AlphaBeta.Maximizer for the opposite
order, with the bounds α and β swapped in the alpha-beta version.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import OrderedTypes.DecidableStrictWeakOrder

module Games.AlphaBeta.Minimizer
        {𝓤 𝓣 : Universe}
        {V : 𝓤 ̇ }
        (O : Decidable-Strict-Weak-Order V 𝓣)
        (R : 𝓤 ̇ )
        (val : R → V)
       where

open import MonadOnTypes.K
open import MonadOnTypes.NonEmptyList using (List⁺)

import Games.AlphaBeta.Maximizer

open Decidable-Strict-Weak-Order O
open K-definitions {𝓤} {R} using (K)

module Max = Games.AlphaBeta.Maximizer O R val
module Min = Games.AlphaBeta.Maximizer (opposite O) R val

open Max
 using (T ; φmax ; φ*max ; _is-αβ-approximated-by_ ;
        αβ-approximation-at-most-α ; αβ-approximation-at-least-β ;
        αβ-approximation-exact ; φmax-is-αβ-approximated-by-φ*max)
 public

swap : V × V → V × V
swap (a , b) = (b , a)

φmin : {X : 𝓤 ̇ } → List⁺ X → K X
φmin = Min.φmax

φ*min : {X : 𝓤 ̇ } → List⁺ X → (X → T R) → T R
φ*min xs p αβ = Min.φ*max xs (λ x → p x ∘ swap) (swap αβ)

\end{code}

An outcome is approximated by a monadic outcome for the order _<_ if
and only if it is approximated by the monadic outcome with swapped
bounds for the opposite order.

\begin{code}

approximation-to-opposite : (r : R) (t : T R)
                          → r is-αβ-approximated-by t
                          → r Min.is-αβ-approximated-by (t ∘ swap)
approximation-to-opposite r t h α β =
   αβ-approximation-at-least-β h β α ,
   αβ-approximation-at-most-α h β α ,
   (λ a b → αβ-approximation-exact h β α b a)

approximation-from-opposite : (r : R) (t : T R)
                            → r Min.is-αβ-approximated-by (t ∘ swap)
                            → r is-αβ-approximated-by t
approximation-from-opposite r t h α β =
   Min.αβ-approximation-at-least-β h β α ,
   Min.αβ-approximation-at-most-α h β α ,
   (λ a b → Min.αβ-approximation-exact h β α b a)

\end{code}

The induction step of the proof of Theorem 1 for the minimizing player
follows from that for the maximizing player.

\begin{code}

φmin-is-αβ-approximated-by-φ*min
 : {X : 𝓤 ̇ }
   (p  : X → R)
   (p* : X → T R)
 → ((x : X) → (p x) is-αβ-approximated-by (p* x))
 → (xs : List⁺ X) → (φmin xs p) is-αβ-approximated-by (φ*min xs p*)
φmin-is-αβ-approximated-by-φ*min p p* h xs =
 approximation-from-opposite (φmin xs p) (φ*min xs p*)
  (Min.φmax-is-αβ-approximated-by-φ*max p (λ x → p* x ∘ swap)
    (λ x → approximation-to-opposite (p x) (p* x) (h x))
    xs)

\end{code}

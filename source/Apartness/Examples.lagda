Martin Escardo, 26 January 2018.

Moved from the file TotallySeparated 22 August 2024.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module Apartness.Examples
        (pt : propositional-truncations-exist)
       where

open import Apartness.Definition
open import MLTT.Spartan
open import UF.SubtypeClassifier

open PropositionalTruncation pt
open Apartness pt

\end{code}

I don't think there is a tight apartness relation on Ω without
constructive taboos. The natural apartness relation seems to be the
following, but it isn't cotransitive unless excluded middle holds.

\begin{code}

_♯Ω_ : Ω 𝓤 → Ω 𝓤 → 𝓤 ̇
(P , i) ♯Ω (Q , j) = (P × ¬ Q) + (¬ P × Q)

♯Ω-irrefl : is-irreflexive (_♯Ω_ {𝓤})
♯Ω-irrefl (P , i) (inl (p , nq)) = nq p
♯Ω-irrefl (P , i) (inr (np , q)) = np q

♯Ω-sym : is-symmetric (_♯Ω_ {𝓤})
♯Ω-sym (P , i) (Q , j) (inl (p , nq)) = inr (nq , p)
♯Ω-sym (P , i) (Q , j) (inr (np , q)) = inl (q , np)

♯Ω-cotran-taboo : is-cotransitive (_♯Ω_ {𝓤})
                → (p : Ω 𝓤)
                → p holds ∨ ¬ (p holds)
♯Ω-cotran-taboo c p = ∥∥-functor II I
 where
  I : (⊥ ♯Ω p) ∨ (⊤ ♯Ω p)
  I = c ⊥ ⊤ p (inr (𝟘-elim , ⋆))

  II : (⊥ ♯Ω p) + (⊤ ♯Ω p) → (p holds) + ¬ (p holds)
  II (inl (inr (a , b))) = inl b
  II (inr (inl (a , b))) = inr b
  II (inr (inr (a , b))) = inl b

\end{code}

TODO. Show that *any* apartness relation on Ω gives weak excluded
middle.

Martin Escardo 2012.

The Weak Limited Principle of Omniscience (only somebody called Bishop
could have called it that), or WLPO for short, says that every
infinity binary sequence is either constantly 1 or it isn't.

This is equivalent to saying that every decreasing infinity binary
sequence os either constantly one or not.

The type ℕ∞ of decreasing binary sequences is defined in the module
GenericConvergentSequence. The constantly 1 sequence is called ∞.

WLPO is independent of type theory: it holds in the model of classical
sets, and it fails in recursive models, because it amounts to a
solution of the Halting Problem. But we want to keep it undecided, for
the sake of being compatible with classical mathematics, following the
wishes of Bishop, and perhaps upsetting those of Brouwer who was happy
to accept continuity principles that falsify WLPO. In the words of
Aczel, WLPO is a taboo.  More generally, anything that implies a taboo
is a taboo, and any taboo is undecided. Taboos are boundary
propositions: they are classically true, recursively false, and
constructively, well, taboos!

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module WLPO where

open import SpartanMLTT
open import GenericConvergentSequence

WLPO : U₀ ̇
WLPO = (u : ℕ∞) → (u ≡ ∞) + (u ≢ ∞)

open import DiscreteAndSeparated

\end{code}

If ℕ∞ is discrete, i.e. has decidable equality, then WLPO follows:

\begin{code}

ℕ∞-discrete-gives-WLPO : discrete ℕ∞ → WLPO
ℕ∞-discrete-gives-WLPO d u = d u ∞

\end{code}

Conversely, assuming function extensionality, WLPO implies that ℕ∞ is
discrete. The proof uses a codistance (or closeness) function
c : ℕ∞ → ℕ∞ → ℕ∞ such that c u v ≡ ∞ ⇔ u ≡ v.

\begin{code}

open import UF-FunExt

WLPO-gives-ℕ∞-discrete : (∀ U V → funext U V) → WLPO → discrete ℕ∞
WLPO-gives-ℕ∞-discrete fe wlpo u v =
 Cases (wlpo (ℕ∞-codistance u v))
  (λ (p : ℕ∞-codistance u v ≡ ∞)
        → inl (ℕ∞-iae u v p))
  (λ (n : ℕ∞-codistance u v ≢ ∞)
        → inr (contrapositive (λ (q : u ≡ v) → ℕ∞-si' u v q) n))
 where
  open import Codistance fe

\end{code}

More discussion is included in the modules TheTopologyOfTheUniverse
and FailureOfTotalSeparatedness.

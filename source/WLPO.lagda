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

open import GenericConvergentSequence
open import SpartanMLTT

WLPO : U₀ ̇
WLPO = (u : ℕ∞) → (u ≡ ∞) + (u ≢ ∞)

open import DiscreteAndSeparated

ℕ∞-discrete-WLPO : discrete ℕ∞ → WLPO
ℕ∞-discrete-WLPO d u = d u ∞

\end{code}

TODO.

WLPO-[ℕ∞-discrete] : WLPO → discrete ℕ∞
WLPO-[ℕ∞-discrete] w = {!!}

More discussion is included in the modules TheTopologyOfTheUniverse
and FailureOfTotalSeparatedness.

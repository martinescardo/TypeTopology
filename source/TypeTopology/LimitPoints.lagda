Martin Escardo 2023 and 2024.

Notions of limit point moved from FailureofTotalSeparatedness and
Ordinals.NotationInterpretation2 to this module 14th October 2024.

In classical topology, a limit point is a point that is not
isolated. In TypeTopology we investigate the "intrinsic topology" of
types, with emphasis on sets. But also we are agnostic regarding
classical principles, which we leave deliberately undecided, unless
they are explicitly assumed. The idea is that we want our results to
hold in any ∞-topos, and in more general settings too.

If excluded middle holds, every point of every set is isolated, and so
it is not possible to exhibit any isolated point. This changes if we
assume anticlassical principles, such as "all functions (of some kind)
are continuous". One of the weakest continuity principle is the
negation of WLPO, as discussed in the module
DecidabilityOfNonContinuity. So, in order to remain agnostic, we
define the notion of limit point as follows.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module TypeTopology.LimitPoints where

open import MLTT.Spartan
open import Taboos.WLPO
open import UF.DiscreteAndSeparated

is-limit-point : {X : 𝓤 ̇ } → X → 𝓤 ̇
is-limit-point x = is-isolated x → WLPO

\end{code}

But it turns out that there is a strengthening of this notion that
arises in practice in two places in this development, in the modules
FailureOfTotalSeparatedness and Ordinals.NotationInterpretation2.

\begin{code}

is-limit-point⁺ : {X : 𝓤 ̇ } → X → 𝓤 ̇
is-limit-point⁺ x = is-weakly-isolated x → WLPO

limit-points⁺-are-limit-points : {X : 𝓤 ̇ } (x : X)
                               → is-limit-point⁺ x
                               → is-limit-point x
limit-points⁺-are-limit-points x ℓ i = ℓ (isolated-gives-weakly-isolated x i)

\end{code}

Martin Escardo, 1st April 2024.

Three versions of the Drinker Paradox, one of which is equivalent to
the principle of excluded middle.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc

module Taboos.DrinkerParadox
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.ClassicalLogic
open import UF.Subsingletons
open import UF.SubtypeClassifier

\end{code}

The so-called Drinker Paradox says that in every non-empty pub X there
is a person x₀ such that if x₀ drinks then everybody drinks, for any
notion of drinking.

\begin{code}

DP : (𝓤 : Universe) → 𝓤 ⁺ ̇
DP 𝓤 = (X : 𝓤 ̇ )
     → ¬ is-empty X
     → (drinks : X → Ω 𝓤)
     → ∃ x₀ ꞉ X , (drinks x₀ holds → (x : X) → drinks x holds)

\end{code}

This implies double negation elimination and hence excluded middle.

\begin{code}

DP-gives-DNE : DP 𝓤 → DNE 𝓤
DP-gives-DNE {𝓤} dp P P-is-prop ν = III
 where
  X : 𝓤 ̇
  X = P

  X-is-non-empty : ¬ is-empty X
  X-is-non-empty = ν

  anything-you-like : Ω 𝓤
  anything-you-like = ⊥

  drinks : X → Ω 𝓤
  drinks x = anything-you-like

  I : ∃ x₀ ꞉ X , (drinks x₀ holds → (x : X) → drinks x holds)
  I = dp X X-is-non-empty drinks

  II : (Σ x₀ ꞉ X , (drinks x₀ holds → (x : X) → drinks x holds)) → P
  II = pr₁

  III : P
  III = ∥∥-rec P-is-prop II I

DP-gives-EM : DP 𝓤 → EM 𝓤
DP-gives-EM dp = DNE-gives-EM fe (DP-gives-DNE dp)

\end{code}

As indicated in the above proof, it doesn't matter what "drinks" is
taken to be. Any drinking predicate will do.

Conversely, excluded middle gives DP.

\begin{code}

EM-gives-DP : EM 𝓤 → DP 𝓤
EM-gives-DP em X X-is-non-empty drinks = V
 where
  X-is-inhabited : ∥ X ∥
  X-is-inhabited = non-empty-is-inhabited pt em X-is-non-empty

  I : (∃ x ꞉ X , ¬ (drinks x holds)) + ((x : X) → (drinks x holds))
  I = ∃-not+Π pt em
       (λ (x : X) → drinks x holds)
       (λ (x : X) → holds-is-prop (drinks x))

  II : (Σ x₀ ꞉ X , ¬ (drinks x₀ holds))
     → Σ x₀ ꞉ X , (drinks x₀ holds → (x : X) → drinks x holds)
  II (x₀ , x₀-is-sober) = x₀ ,
                          (λ (x₀-is-not-sober : drinks x₀ holds)
                             → 𝟘-elim (x₀-is-sober x₀-is-not-sober))

  III : ((x : X) → (drinks x holds))
      → X
      → Σ x₀ ꞉ X , (drinks x₀ holds → (x : X) → drinks x holds)
  III a x₀ = x₀ , λ (_ : drinks x₀ holds) → a

  IV : type-of I → ∃ x₀ ꞉ X , (drinks x₀ holds → (x : X) → drinks x holds)
  IV (inl e) = ∥∥-functor II e
  IV (inr a) = ∥∥-functor (III a) X-is-inhabited

  V : ∃ x₀ ꞉ X , (drinks x₀ holds → (x : X) → drinks x holds)
  V = IV I

\end{code}

Now consider the following two variations, where we instead
require that the pub is assumed to be respectively pointed and
inhabited.

\begin{code}

pointed-DP : (𝓤 : Universe) → 𝓤 ⁺ ̇
pointed-DP 𝓤 = (X : 𝓤 ̇ )
              → X
              → (drinks : X → Ω 𝓤)
              → ∃ x₀ ꞉ X , (drinks x₀ holds → (x : X) → drinks x holds)

inhabited-DP : (𝓤 : Universe) → 𝓤 ⁺ ̇
inhabited-DP 𝓤 = (X : 𝓤 ̇ )
                → ∥ X ∥
                → (drinks : X → Ω 𝓤)
                → ∃ x₀ ꞉ X , (drinks x₀ holds → (x : X) → drinks x holds)

\end{code}

These two variations are weaker than the original version.

\begin{code}

pointed-DP-gives-inhabited-DP : inhabited-DP 𝓤 → pointed-DP 𝓤
pointed-DP-gives-inhabited-DP idp X x₀ = idp X ∣ x₀ ∣

DP-gives-pointed-DP : DP 𝓤 → pointed-DP 𝓤
DP-gives-pointed-DP dp X x = dp X (λ (e : X → 𝟘) → e x)

\end{code}

I don't know whether excluded middle can be proved from any of these
two weaker variations, or, equivalently, whether each of these two
variations imply the original.

There are more variations. For example, we can consider the particular
case where the drinking predicate is decidable, or we can replace ∃ by Σ.
These two modifications together are indeed one of our definitions of
compactness in TypeTopology.CompactTypes.

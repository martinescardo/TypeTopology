Martin Escardo 29 April 2014.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt
open import UF-Embedding

module ExtendedSumCompact (fe : ∀ U V → funext U V) where

open import CompactTypes
open import UF-InjectiveTypes (fe)
open import PropTychonoff (fe)

extended-sum-compact∙ : {X : U ̇} {K : V ̇} {Y : X → W ̇} (j : X → K) → is-embedding j
                        → ((x : X) → compact∙(Y x)) → compact∙ K → compact∙(Σ(Y / j))
extended-sum-compact∙ j e ε δ = Σ-compact∙ δ (λ k → prop-tychonoff (e k) (ε ∘ pr₁))

\end{code}

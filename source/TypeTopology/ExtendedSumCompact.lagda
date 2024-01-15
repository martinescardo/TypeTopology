Martin Escardo 29 April 2014.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.Embeddings

module TypeTopology.ExtendedSumCompact (fe : FunExt) where

open import TypeTopology.CompactTypes
open import TypeTopology.PropTychonoff fe

open import InjectiveTypes.Blackboard fe

extended-sum-compact∙ : {X : 𝓤 ̇ }
                        {K : 𝓥 ̇ }
                        {Y : X → 𝓦 ̇ }
                        (j : X → K)
                      → is-embedding j
                      → ((x : X) → is-compact∙ (Y x))
                      → is-compact∙ K
                      → is-compact∙ (Σ (Y / j))
extended-sum-compact∙ j e ε δ = Σ-is-compact∙ δ (λ k → prop-tychonoff (e k) (ε ∘ pr₁))

\end{code}

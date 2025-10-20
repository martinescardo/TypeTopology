Tom de Jong, 20 October 2025

We define the infinite dimensional real projective space RP∞ as the connected
component of the booleans. This is motivated by [1], where Buchholtz and Rijke
define RP∞ as a sequential colimit of finite dimensional real projective spaces
and then prove that RP∞ is equivalent to the connected component of the booleans
(called the type of 0-sphere bundles in [1]).

The advantage of the definition adopted here is that it is very simple to state,
the downside is that it produces a large type. However, in the presence of
sequential colimits, it is equivalent to a small type by the results of [1].

[1] Ulrik Buchholtz and Egbert Rijke
    The real projective spaces in homotopy type theory
    LICS'17: Proceedings of the 32nd Annual ACM/IEEE Symposium on Logic in
    Computer Science, Article No.: 86, pp. 1—8, 2017
    https://doi.org/10.5555/3329995.3330081
    https://arxiv.org/abs/1704.05770

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.PropTrunc

module SyntheticHomotopyTheory.RP-infinity
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import MLTT.Spartan
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Univalence

RP∞ : 𝓤₁ ̇
RP∞ = Σ X ꞉ 𝓤₀ ̇  , ∥ X ≃ 𝟚 ∥

RP∞' : 𝓤₁ ̇
RP∞' = Σ X ꞉ 𝓤₀ ̇  , ∥ X ＝ 𝟚 ∥

RP∞-equivalent-formulations : is-univalent 𝓤₀ → RP∞ ≃ RP∞'
RP∞-equivalent-formulations ua =
 Σ-cong (λ X → ∥∥-cong pt (≃-sym (univalence-≃ ua X 𝟚)))

\end{code}

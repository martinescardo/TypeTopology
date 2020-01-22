Martin Escardo, 22nd January 2020

This is a univalent-foundations version of Pierre Pradic and Chad
E. Brown's argument that Cantor-Schroeder-Bernstein implies excluded
middle in constructive set theory (https://arxiv.org/abs/1904.09193).

Their proof, reproduced below, uses the compactness (also know as the
searchability or omniscience) of ℕ∞.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module CantorSchroederBernsteinGivesEM where

open import UF-ExcludedMiddle
open import UF-Subsingletons
open import UF-Equiv
open import UF-Embeddings
open import UF-Retracts
open import GenericConvergentSequence
open import DecidableAndDetachable
open import Plus-Properties
open import CompactTypes
open import ConvergentSequenceCompact

CantorSchroederBernstein : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
CantorSchroederBernstein X Y = (X ↪ Y) → (Y ↪ X) → X ≃ Y

\end{code}

The following is Lemma 7 of the above reference, using retractions
rather than surjections, for simplicity:

\begin{code}

csb-lemma : {X : 𝓤 ̇ } {A : 𝓥 ̇ } → Compact X → retract (A + X) of X → decidable A
csb-lemma {𝓤} {𝓥} {X} {A} c (r , s , η) = γ e
 where
  P : X → 𝓤 ⊔ 𝓥 ̇
  P x = Σ \(a : A) → r x ≡ inl a
  d : detachable P
  d x = equality-cases (r x)
         (λ (a : A) (p : r x ≡ inl a) → inl (a , p))
         (λ (y : X) (q : r x ≡ inr y) → inr (λ {(a , p) → +disjoint (inl a ≡⟨ p ⁻¹ ⟩
                                                                     r x   ≡⟨ q    ⟩
                                                                     inr y ∎)}))
  e : decidable (Σ (\(x : X) → P x))
  e = c P d
  f : A → Σ \(x : X) → P x
  f a = s (inl a) , a , η (inl a)
  γ : decidable (Σ (\(x : X) → P x)) → decidable A
  γ (inl (x , a , p)) = inl a
  γ (inr φ)           = inr (contrapositive f φ)

\end{code}

Function extensionality is used twice in the following, once to know
that ℕ∞ is a set, and once to know that it is compact.

\begin{code}

CantorSchroederBernstein-gives-EM : funext 𝓤₀ 𝓤₀
                                  → (P : 𝓤 ̇ ) → is-prop P → CantorSchroederBernstein ℕ∞ (P + ℕ∞) → P + ¬ P
CantorSchroederBernstein-gives-EM fe P i csb = γ
 where
  f : ℕ∞ → P + ℕ∞
  f = inr

  j : is-embedding f
  j = inr-is-embedding P ℕ∞

  z : P → ℕ∞
  z _ = Zero

  g : P + ℕ∞ → ℕ∞
  g = cases z Succ

  a : is-embedding z
  a = maps-of-props-into-sets-are-embeddings (λ p → Zero) i (ℕ∞-is-set fe)

  b : is-embedding Succ
  b = lc-maps-into-sets-are-embeddings Succ Succ-lc (ℕ∞-is-set fe)

  c : disjoint-images z Succ
  c = λ (p : P) (x : ℕ∞) (q : Zero ≡ Succ x) → Zero-not-Succ q

  k : is-embedding g
  k = disjoint-cases-embedding z Succ a b c

  e : ℕ∞ ≃ P + ℕ∞
  e = csb (f , j) (g , k)

  ρ : retract (P + ℕ∞) of ℕ∞
  ρ = equiv-retract-r e

  γ : P + ¬ P
  γ = csb-lemma (ℕ∞-Compact fe) ρ

\end{code}

The classical Cantor-Schroeder-Bernstein theorem, which assumes
excluded middle for its proof, works for sets, because the proofs use
decidability of equality, and, under excluded middle, the types that
have decidable equality are precisely the sets, by Hedberg's
Theorem. Hence the following is the appropriate formulation of
Cantor-Schroeder-Bernstein for univalent foundations:

\begin{code}

CSB : 𝓤ω
CSB = (𝓤 𝓥 : Universe) (X : 𝓤 ̇ ) (Y : 𝓥 ̇ ) → is-set X → is-set Y → CantorSchroederBernstein X Y

CSB-gives-excluded-middle : funext 𝓤₀ 𝓤₀ → CSB → (𝓤 : Universe) → EM 𝓤
CSB-gives-excluded-middle fe csb 𝓤 P i = γ
 where
  a : CantorSchroederBernstein ℕ∞ (P + ℕ∞)
  a = csb 𝓤₀ 𝓤 ℕ∞ (P + ℕ∞) (ℕ∞-is-set fe) (+-is-set P ℕ∞ (props-are-sets i) (ℕ∞-is-set fe))
  γ : P + ¬ P
  γ = CantorSchroederBernstein-gives-EM fe P i a

\end{code}

Remark. If instead of requiring that we have a designated equivalence,
we required that there is an an unspecified equivalence in the
formulation of Cantor-Schroeder-Bernstein, we still get excluded
middle, because P + ¬P is a proposition.

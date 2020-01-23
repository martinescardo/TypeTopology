Martin Escardo, 22nd January 2020

This is a univalent-foundations version of Pierre Pradic and Chad
E. Brown's argument that Cantor-Schröder-Bernstein implies excluded
middle in constructive set theory (https://arxiv.org/abs/1904.09193).

Their proof, reproduced below, uses the compactness (also known as the
searchability or omniscience) of ℕ∞.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module CantorSchroederBernsteinGivesEM where

open import UF-ExcludedMiddle
open import UF-Subsingletons
open import UF-Equiv
open import UF-Embeddings
open import UF-Retracts
open import UF-FunExt
open import SpartanMLTT
open import GenericConvergentSequence
open import DecidableAndDetachable
open import Plus-Properties
open import CompactTypes
open import ConvergentSequenceCompact

\end{code}

The following is Lemma 7 of the above reference, using retractions
rather than surjections, for simplicity:

\begin{code}

Pradic-Brown-lemma : {X : 𝓤 ̇ } {A : 𝓥 ̇ }
                   → retract (A + X) of X
                   → Compact X
                   → decidable A
Pradic-Brown-lemma {𝓤} {𝓥} {X} {A} (r , s , η) c = γ e
 where
  P : X → 𝓤 ⊔ 𝓥 ̇
  P x = Σ \(a : A) → r x ≡ inl a

  d : (x : X) → decidable (P x)
  d x = equality-cases (r x)
         (λ (a : A) (u : r x ≡ inl a) → inl (a , u))
         (λ (y : X) (v : r x ≡ inr y) → inr (λ {(a , u) → +disjoint (inl a ≡⟨ u ⁻¹ ⟩
                                                                     r x   ≡⟨ v    ⟩
                                                                     inr y ∎)}))

  e : decidable (Σ (\(x : X) → P x))
  e = c P d

  f : A → Σ \(x : X) → P x
  f a = s (inl a) , a , η (inl a)

  γ : decidable (Σ \(x : X) → P x) → decidable A
  γ (inl (x , a , u)) = inl a
  γ (inr φ)           = inr (contrapositive f φ)

\end{code}

We first consider Cantor-Schröder-Bernstein for a pair of types:

\begin{code}

CSB : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
CSB X Y = (X ↪ Y) → (Y ↪ X) → X ≃ Y

\end{code}

Function extensionality is used twice in the following, once to know
that ℕ∞ is a set, and once to know that it is compact.

\begin{code}

CSB-gives-EM : funext 𝓤₀ 𝓤₀
             → (P : 𝓤 ̇ )
             → is-prop P
             → CSB ℕ∞ (P + ℕ∞)
             → P + ¬ P
CSB-gives-EM fe P i csb = γ
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
  γ = Pradic-Brown-lemma ρ (ℕ∞-Compact fe)

\end{code}

The classical Cantor-Schröder-Bernstein theorem, which assumes
excluded middle for its proof, works for sets, because the proofs use
decidability of equality, and, under excluded middle, the types that
have decidable equality are precisely the sets, by Hedberg's
Theorem. Hence the following is the appropriate formulation of
Cantor-Schröder-Bernstein for univalent foundations:

\begin{code}

CantorSchröderBernstein : {𝓤 𝓥 : Universe} → (𝓤 ⊔ 𝓥)⁺ ̇
CantorSchröderBernstein {𝓤} {𝓥} = {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                                → is-set X → is-set Y → CSB X Y

\end{code}

If we assume Cantor-Schröder-Bernstein for the first universe 𝓤₀ and
an arbitrary universe 𝓥, as formulated above, then we get excluded
middle for propositions in the universe 𝓤:

\begin{code}

CantorSchröderBernstein-gives-EM : funext 𝓤₀ 𝓤₀
                                 → CantorSchröderBernstein
                                 → EM 𝓥
CantorSchröderBernstein-gives-EM fe csb P i = γ
 where
  a : CSB ℕ∞ (P + ℕ∞)
  a = csb (ℕ∞-is-set fe) (+-is-set P ℕ∞ (props-are-sets i) (ℕ∞-is-set fe))

  γ : P + ¬ P
  γ = CSB-gives-EM fe P i a

\end{code}

Remark. If instead of requiring that we have a designated equivalence,
we required that there is an unspecified equivalence in the
formulation of Cantor-Schröder-Bernstein, we would still get excluded
middle, because P + ¬P is a proposition.

Also recall that for types that are sets, embeddings are the same
thing as left-cancellable maps, and equivalences are the same thing as
invertible maps.

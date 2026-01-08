Tom de Jong and Martin Escardo
January 2026

This file follows the definitions, equations, lemmas, propositions, theorems and
remarks of our paper

   Tom de Jong and Martín Hötzel Escardó
   Examples and counterexamples of injective types
   January 2026
   https://arxiv.org/abs/TODO

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-} -- --lossy-unification (TODO)

\end{code}

Our global assumptions are univalence and the existence of propositional
truncations.

Function extensionality can be derived from univalence.

\begin{code}

open import UF.Univalence
open import UF.PropTrunc

module InjectiveTypes.ExamplesCounterExamplesArticle
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       where

open import MLTT.Spartan
open import Notation.General

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥
open import UF.Base
open import UF.Equiv
open import UF.NotNotStablePropositions
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Size
open import UF.Subsingletons

open import InjectiveTypes.Blackboard fe

\end{code}

Section 2. Preliminaries

\begin{code}

Definition-2-1 : (𝓤 : Universe) → 𝓤 ⁺ ̇
Definition-2-1 𝓤 = is-small (Ω¬¬ 𝓤)

Lemma-2-2 : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : (x : X) → A x → 𝓦 ̇ )
            (x y : X) (a : A x) (b : B x a) (p : x ＝ y)
          → transport (λ - → Sigma (A -) (B -)) p (a , b)
            ＝ transport A p a , transportd A B a p b
Lemma-2-2 A B x y a b p = transport-Σ A B y p a {b}

module Lemma-2-3
        {X : 𝓤 ̇ } (a : X) {Y : X → 𝓥 ̇ } (i : is-prop X)
       where

 Lemma-2-3-i : Π Y ≃ Y a
 Lemma-2-3-i = prop-indexed-product a fe' i

 Lemma-2-3-i₁ : ⌜ Lemma-2-3-i ⌝ ＝ (λ f → f a)
 Lemma-2-3-i₁ = refl

 Lemma-2-3-i₂ : ⌜ Lemma-2-3-i ⌝⁻¹ ＝ (λ y x → transport Y (i a x) y)
 Lemma-2-3-i₂ = refl

 Lemma-2-3-ii : Y a ≃ Σ Y
 Lemma-2-3-ii = ≃-sym (prop-indexed-sum a i)

 Lemma-2-3-ii₁ : ⌜ Lemma-2-3-ii ⌝ ＝ (λ y → (a , y))
 Lemma-2-3-ii₁ = refl

 Lemma-2-3-ii₂ : ⌜ Lemma-2-3-ii ⌝⁻¹ ＝ (λ (x , y) → transport Y (i x a) y)
 Lemma-2-3-ii₂ = refl

\end{code}

Section 3. Flabbiness and injectivity

\begin{code}

Definition-3-1 : (D : 𝓦 ̇ ) (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ⊔ 𝓦 ̇
Definition-3-1 = ainjective-type

Definition-3-2 : (D : 𝓦 ̇ ) (𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓦 ̇
Definition-3-2 = aflabby

Lemma-3-3-i : (D : 𝓦 ̇ ) → ainjective-type D 𝓤 𝓥 → aflabby D 𝓤
Lemma-3-3-i = ainjective-types-are-aflabby

Lemma-3-3-ii : (D : 𝓦 ̇ ) → aflabby D (𝓤 ⊔ 𝓥) → ainjective-type D 𝓤 𝓥
Lemma-3-3-ii = aflabby-types-are-ainjective

Lemma-3-4 : (D : 𝓦 ̇ ) → ainjective-type D 𝓤 𝓥
          → (D' : 𝓦 ̇ ) → retract D' of D → ainjective-type D' 𝓤 𝓥
Lemma-3-4 D ainj D' = retract-of-ainjective D' D ainj

\end{code}
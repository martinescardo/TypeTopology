Martin Escardo

UF things that depend on non-UF things.

Find a better home for all of this.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module UF.Miscelanea where

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import Naturals.Properties
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Lower-FunExt
open import UF.Retracts
open import UF.Sets
open import UF.Size
open import UF.SmallnessProperties
open import UF.SubTypeClassifier
open import UF.SubTypeClassifier-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

𝟚-ℕ-embedding : 𝟚 → ℕ
𝟚-ℕ-embedding ₀ = 0
𝟚-ℕ-embedding ₁ = 1

𝟚-ℕ-embedding-is-lc : left-cancellable 𝟚-ℕ-embedding
𝟚-ℕ-embedding-is-lc {₀} {₀} refl = refl
𝟚-ℕ-embedding-is-lc {₀} {₁} r    = 𝟘-elim (positive-not-zero 0 (r ⁻¹))
𝟚-ℕ-embedding-is-lc {₁} {₀} r    = 𝟘-elim (positive-not-zero 0 r)
𝟚-ℕ-embedding-is-lc {₁} {₁} refl = refl

C-B-embedding : (ℕ → 𝟚) → (ℕ → ℕ)
C-B-embedding α = 𝟚-ℕ-embedding ∘ α

C-B-embedding-is-lc : funext 𝓤₀ 𝓤₀ → left-cancellable C-B-embedding
C-B-embedding-is-lc fe {α} {β} p = dfunext fe h
 where
  h : (n : ℕ) → α n ＝ β n
  h n = 𝟚-ℕ-embedding-is-lc (ap (λ - → - n) p)

𝟚-retract-of-ℕ : retract 𝟚 of ℕ
𝟚-retract-of-ℕ = r , s , rs
 where
  r : ℕ → 𝟚
  r 0        = ₀
  r (succ n) = ₁

  s : 𝟚 → ℕ
  s ₀ = 0
  s ₁ = 1

  rs : r ∘ s ∼ id
  rs ₀ = refl
  rs ₁ = refl

\end{code}

Added 19th Feb 2020:

\begin{code}

open import UF.Embeddings

maps-of-props-into-h-isolated-points-are-embeddings :

   {P : 𝓤 ̇ } {X : 𝓥 ̇ } (f : P → X)
 → is-prop P
 → ((p : P) → is-h-isolated (f p))
 → is-embedding f

maps-of-props-into-h-isolated-points-are-embeddings f i j q (p , s) (p' , s') =
 to-Σ-＝ (i p p' , j p' _ s')

maps-of-props-into-isolated-points-are-embeddings : {P : 𝓤 ̇ } {X : 𝓥 ̇ }
                                                    (f : P → X)
                                                  → is-prop P
                                                  → ((p : P) → is-isolated (f p))
                                                  → is-embedding f
maps-of-props-into-isolated-points-are-embeddings f i j =
 maps-of-props-into-h-isolated-points-are-embeddings f i
  (λ p → isolated-is-h-isolated (f p) (j p))

global-point-is-embedding : {X : 𝓤 ̇  } (f : 𝟙 {𝓥} → X)
                          → is-h-isolated (f ⋆)
                          → is-embedding f
global-point-is-embedding f h =
 maps-of-props-into-h-isolated-points-are-embeddings
  f 𝟙-is-prop h'
   where
    h' : (p : 𝟙) → is-h-isolated (f p)
    h' ⋆ = h

\end{code}

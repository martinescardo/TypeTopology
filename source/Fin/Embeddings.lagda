Martin Escardo, sometime between 2014 and 2021.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Fin.Embeddings where


open import Fin.Properties
open import Fin.Type
open import Fin.Variation
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import Naturals.Order
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Embeddings

⟦_⟧ : {n : ℕ} → Fin n → ℕ
⟦_⟧ {n} = pr₁ ∘ Fin-prime n

module _ {n : ℕ} where

 instance
  canonical-map-Fin-ℕ : Canonical-Map (Fin n) ℕ
  ι {{canonical-map-Fin-ℕ}} = ⟦_⟧ {n}

⟦⟧-property : {n : ℕ} (k : Fin n) → ⟦ k ⟧ < n
⟦⟧-property {n} k = pr₂ (Fin-prime n k)

⟦_⟧-is-embedding : (n : ℕ) → is-embedding (⟦_⟧ {n})
⟦_⟧-is-embedding n = ∘-is-embedding
                      (equivs-are-embeddings (Fin-prime n) (Fin-prime-is-equiv n))
                      (pr₁-is-embedding (λ i → <-is-prop-valued i n))

⟦⟪⟫⟧-property : {n : ℕ} → ⟦ ⟪ n ⟫ ⟧ ＝ n
⟦⟪⟫⟧-property {0}      = refl
⟦⟪⟫⟧-property {succ n} = ap succ (⟦⟪⟫⟧-property {n})

⟦_⟧-lc : (n : ℕ) → left-cancellable (⟦_⟧ {n})
⟦_⟧-lc n = embeddings-are-lc ⟦_⟧ (⟦_⟧-is-embedding n)

coerce : {n : ℕ} {i : Fin n} → Fin ⟦ i ⟧ → Fin n
coerce {0}      {i}     x       = 𝟘-elim i
coerce {succ n} {𝟎}     x       = 𝟘-elim x
coerce {succ n} {suc i} 𝟎       = 𝟎
coerce {succ n} {suc i} (suc j) = suc (coerce j)

coerce-lc : {n : ℕ} {i : Fin n} (j k : Fin ⟦ i ⟧)
          → coerce {n} {i} j ＝ coerce {n} {i} k → j ＝ k
coerce-lc {0}      {i}     j       k       p = 𝟘-elim i
coerce-lc {succ n} {𝟎}     j       k       p = 𝟘-elim j
coerce-lc {succ n} {suc i} 𝟎       𝟎       p = refl
coerce-lc {succ n} {suc i} 𝟎       (suc j) p = 𝟘-elim (+disjoint' p)
coerce-lc {succ n} {suc i} (suc j) 𝟎       p = 𝟘-elim (+disjoint p)
coerce-lc {succ n} {suc i} (suc j) (suc k) p = ap suc (coerce-lc {n} j k (suc-lc p))

incl : {n : ℕ} {k : ℕ} → k ≤ n → Fin k → Fin n
incl {n} {0}      l i = 𝟘-elim i
incl {0} {succ k} l i = 𝟘-elim l
incl {succ n} {succ k} l 𝟎 = 𝟎
incl {succ n} {succ k} l (suc i) = suc (incl l i)

incl-lc : {n : ℕ} {k : ℕ} (l : k ≤ n)
        → (i j : Fin k) → incl l i ＝ incl l j → i ＝ j
incl-lc {n} {0}      l i j p = 𝟘-elim i
incl-lc {0} {succ k} l i j p = 𝟘-elim l
incl-lc {succ n} {succ k} l 𝟎       𝟎       p = refl
incl-lc {succ n} {succ k} l 𝟎       (suc j) p = 𝟘-elim (positive-not-𝟎 (p ⁻¹))
incl-lc {succ n} {succ k} l (suc i) 𝟎       p = 𝟘-elim (positive-not-𝟎 p)
incl-lc {succ n} {succ k} l (suc i) (suc j) p = ap suc (incl-lc l i j (suc-lc p))

_/_ : {n : ℕ} (k : Fin (succ n)) → Fin ⟦ k ⟧ → Fin n
k / i = incl (⟦⟧-property k) i

_╱_ :  (n : ℕ) → Fin n → Fin (succ n)
n ╱ k = incl (≤-succ n) k

mirror : {n : ℕ} → Fin n → Fin n
mirror {0}            i = 𝟘-elim i
mirror {succ n}       𝟎 = ⟪ n ⟫
mirror {succ n} (suc k) = n ╱ mirror {n} k

\end{code}

TODO. Show that the above coersions are left cancellable (easy).

TODO. Rewrite above code to use the notation ι for all coersions,
defined in the module Notation.CanonicalMap.

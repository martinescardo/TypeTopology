Martin Escardo 7th December 2018.

We show that the natural map into the lifting is an embedding using
the structure identity principle. A more direct, but longer, proof
is in the module Lifting.EmbeddingDirectly.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Lifting.EmbeddingViaSIP
        (𝓣 𝓤 : Universe)
        (X : 𝓤 ̇ )
       where

open import UF.Subsingletons
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Univalence
open import UF.UA-FunExt

open import Lifting.Construction 𝓣
open import Lifting.IdentityViaSIP 𝓣

\end{code}

The crucial point the use the characterization of identity via the
structure identity principle:

\begin{code}

η-is-embedding' : is-univalent 𝓣 → funext 𝓣 𝓤 → is-embedding (η {𝓤} {X})
η-is-embedding' ua fe = embedding-criterion' η c
 where
  a = (𝟙 ≃ 𝟙) ≃⟨ ≃-sym (univalence-≃ ua 𝟙 𝟙) ⟩
      (𝟙 ＝ 𝟙) ≃⟨ 𝟙-＝-≃ 𝟙 (univalence-gives-funext ua)
                         (univalence-gives-propext ua) 𝟙-is-prop ⟩
      𝟙       ■

  b = λ (x y : X) →
       ((λ _ → x) ＝ (λ _ → y)) ≃⟨ ≃-funext fe (λ _ → x) (λ _ → y) ⟩
       (𝟙 → x ＝ y)             ≃⟨ ≃-sym (𝟙→ fe) ⟩
       (x ＝ y)                 ■

  c = λ x y → (η x ＝ η y)                       ≃⟨ 𝓛-Id ua (η x) (η y) ⟩
              (𝟙 ≃ 𝟙) × ((λ _ → x) ＝ (λ _ → y)) ≃⟨ ×-cong a (b x y) ⟩
              𝟙 × (x ＝ y)                       ≃⟨ 𝟙-lneutral ⟩
              (x ＝ y)                           ■

\end{code}

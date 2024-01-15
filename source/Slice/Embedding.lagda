Martin Escardo 6th December 2018.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Univalence
open import UF.FunExt

module Slice.Embedding
        (𝓤 𝓣 : Universe)
        (ua : is-univalent 𝓣)
        (fe : funext 𝓣 𝓤)
       where

open import UF.Subsingletons
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.UA-FunExt

open import Slice.Slice 𝓣
open import Slice.IdentityViaSIP 𝓣

η-is-embedding : {X : 𝓤 ̇ } → is-embedding (η {𝓤} {X})
η-is-embedding {X} = embedding-criterion' η c
  where
   a : (𝟙 ≃ 𝟙) ≃ 𝟙
   a = (𝟙 ≃ 𝟙) ≃⟨ ≃-sym (univalence-≃ ua 𝟙 𝟙) ⟩
       (𝟙 ＝ 𝟙) ≃⟨ 𝟙-＝-≃ 𝟙 (univalence-gives-funext ua) (univalence-gives-propext ua) 𝟙-is-prop ⟩
       𝟙       ■
   b : (x y : X) → ((λ (_ : 𝟙) → x) ＝ (λ (_ : 𝟙) → y)) ≃ (x ＝ y)
   b x y = ((λ _ → x) ＝ (λ _ → y)) ≃⟨ ≃-funext fe (λ _ → x) (λ _ → y) ⟩
           (𝟙 → x ＝ y)             ≃⟨ ≃-sym (𝟙→ fe) ⟩
           (x ＝ y)                 ■
   c : (x y : X) → (η x ＝ η y) ≃ (x ＝ y)
   c x y = (η x ＝ η y)                       ≃⟨ 𝓕-Id ua (η x) (η y) ⟩
           (𝟙 ≃ 𝟙) × ((λ _ → x) ＝ (λ _ → y)) ≃⟨ ×-cong a (b x y) ⟩
           𝟙 × (x ＝ y)                       ≃⟨ 𝟙-lneutral ⟩
           (x ＝ y)                           ■

\end{code}

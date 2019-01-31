Martin Escardo, 29th January 2019

If univalence holds, then any universe is embedded into any larger universe.

We do this without cumulativity, because it is not available in the
Martin-Löf type theory that we are working with in Agda.

Moreover, any map f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ with f X ≃ X for all X : 𝓤 ̇ is an
embedding, e.g. the map X ↦ X + 𝟘 {𝓥}.

(Here the notion of a map being an embedding is stronger than that of
being left-cancellable, and it means that the fibers of the map are
propositions, or subsingletons, as in HoTT/UF.)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Univalence

module UF-UniverseEmbedding where

open import SpartanMLTT
open import UF-Embedding
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Equiv-FunExt
open import UF-UA-FunExt

universe-embedding-criterion : Univalence
                             → (𝓤 𝓥 : Universe) (f : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇)
                             → ((X : 𝓤 ̇) → f X ≃ X)
                             → is-embedding f
universe-embedding-criterion ua 𝓤 𝓥 f i = embedding-criterion' f γ
 where
  γ : (X X' : 𝓤 ̇) → (f X ≡ f X') ≃ (X ≡ X')
  γ X X' =  (f X ≡ f X')  ≃⟨ is-univalent-≃ (ua (𝓤 ⊔ 𝓥)) (f X) (f X') ⟩
            (f X ≃ f X')  ≃⟨ Eq-Eq-cong (FunExt-from-univalence ua) (i X) (i X') ⟩
            (X ≃ X')      ≃⟨ ≃-sym (is-univalent-≃ (ua 𝓤) X X') ⟩
            (X ≡ X')      ■

\end{code}

For instance, the following function satisfies this condition and
hence is an embedding:

\begin{code}

lift : (𝓥 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
lift 𝓥 X = X + 𝟘 {𝓥}

lift-≃ : (𝓥 : Universe) (X : 𝓤 ̇)
              → lift 𝓥 X ≃ X
lift-≃ 𝓥 X = 𝟘-rneutral'

lift-is-embedding : Univalence → is-embedding (lift {𝓤} 𝓥)
lift-is-embedding {𝓤} {𝓥} ua = universe-embedding-criterion ua 𝓤 𝓥 (lift 𝓥) (lift-≃ 𝓥)

\end{code}

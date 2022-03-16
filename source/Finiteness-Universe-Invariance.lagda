Martin Escardo, 23rd June 2021

The type of finite types is universe invariant.

After a discussion with Ulrik Buchholtz and Peter Lumsdaine.

There is also a proof in Egbert Rijke's book (to appear).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import SpartanMLTT
open import Fin
open import Fin-Properties
open import PairFun

open import UF-Subsingletons renaming (⊤Ω to ⊤)
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-PropTrunc
open import UF-ImageAndSurjection
open import UF-Embeddings
open import UF-UniverseEmbedding
open import UF-FunExt
open import UF-Univalence
open import UF-UA-FunExt

module Finiteness-Universe-Invariance
        (pt : propositional-truncations-exist)
        (ua : Univalence)
       where

fe : Fun-Ext
fe = Univalence-gives-Fun-Ext ua

open ImageAndSurjection pt
open finiteness pt

module constructions (X₀ : 𝓤₀ ̇ ) where

  A : (𝓤 : Universe) → 𝓤 ⁺ ̇
  A 𝓤 = Σ X ꞉ 𝓤 ̇ , ∥ X ≃ X₀ ∥

\end{code}

Recall that Lift : (𝓥 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇ is the unique map with
Lift 𝓥 X ≃ X, and that Lift 𝓥 is an embedding of the universe 𝓤 into
the universe 𝓤 ⊔ 𝓥, meaning that it has subsingleton fibers. This
relies on univalence, which we are assuming in this file.

\begin{code}

  δ : (𝓤 : Universe) → (X : 𝓤₀ ̇ ) → ∥ X ≃ X₀ ∥ → ∥ Lift 𝓤 X ≃ X₀ ∥
  δ 𝓤 X = ∥∥-functor (λ (e : X ≃ X₀) → Lift-≃ 𝓤 X ● e)

  δ-is-embedding : (X : 𝓤₀ ̇ ) → is-embedding (δ 𝓤 X)
  δ-is-embedding {𝓤} X = maps-of-props-are-embeddings (δ 𝓤 X) ∥∥-is-prop ∥∥-is-prop

  ϕ : (𝓤 : Universe) → A 𝓤₀ → A 𝓤
  ϕ 𝓤 (X , s) = Lift 𝓤 X , δ 𝓤 X s

  ϕ-is-embedding : is-embedding (ϕ 𝓤)
  ϕ-is-embedding {𝓤} = pair-fun-is-embedding
                        (Lift 𝓤) (δ 𝓤)
                        (Lift-is-embedding ua) δ-is-embedding

  ϕ-is-surjection : is-surjection (ϕ 𝓤)
  ϕ-is-surjection {𝓤} (Y , t) = g
   where
    f : Y ≃ X₀ → Σ (X , s) ꞉ A 𝓤₀ , (Lift 𝓤 X , δ 𝓤 X s) ≡ (Y , t)
    f e = (X₀ , ∣ ≃-refl X₀ ∣) , q

     where
      d = Lift 𝓤 X₀ ≃⟨ Lift-≃ 𝓤 X₀ ⟩
          X₀        ≃⟨ ≃-sym e ⟩
          Y         ■

      p : Lift 𝓤 X₀ ≡ Y
      p = eqtoid (ua 𝓤) _ _ d

      q : (Lift 𝓤 X₀ , δ 𝓤 X₀ ∣ ≃-refl X₀ ∣) ≡ (Y , t)
      q = to-subtype-≡ (λ X → ∥∥-is-prop) p


    g : ∃ (X , s) ꞉ A 𝓤₀ , (Lift 𝓤 X , δ 𝓤 X s) ≡ (Y , t)
    g = ∥∥-functor f t

  ϕ-is-equiv : is-equiv (ϕ 𝓤)
  ϕ-is-equiv {𝓤} = surjective-embeddings-are-equivs (ϕ 𝓤) ϕ-is-embedding ϕ-is-surjection

  lemma₀ : (𝓤 : Universe) → A 𝓤₀ ≃ A 𝓤
  lemma₀ 𝓤 = ϕ 𝓤 , ϕ-is-equiv

  lemma : A 𝓤 ≃ A 𝓥
  lemma {𝓤} {𝓥} = ≃-sym (lemma₀ 𝓤) ● lemma₀ 𝓥


Finite : (𝓤 : Universe) → 𝓤 ⁺ ̇
Finite 𝓤 = Σ X ꞉ 𝓤 ̇ , is-finite X

Finite-is-universe-independent : Finite 𝓤 ≃ Finite 𝓥
Finite-is-universe-independent {𝓤} {𝓥} =
  (Σ X ꞉ 𝓤 ̇ , Σ n ꞉ ℕ , ∥ X ≃ Fin n ∥) ≃⟨ Σ-flip ⟩
  (Σ n ꞉ ℕ , Σ X ꞉ 𝓤 ̇ , ∥ X ≃ Fin n ∥) ≃⟨ Σ-cong (λ n → constructions.lemma (Fin n)) ⟩
  (Σ n ꞉ ℕ , Σ Y ꞉ 𝓥 ̇ , ∥ Y ≃ Fin n ∥) ≃⟨ Σ-flip ⟩
  (Σ Y ꞉ 𝓥 ̇ , Σ n ꞉ ℕ , ∥ Y ≃ Fin n ∥) ■

finite-types-are-lifts : (X : 𝓤 ̇ ) → is-finite X → Σ X₀ ꞉ 𝓤₀ ̇ , Lift 𝓤 X₀ ≡ X
finite-types-are-lifts {𝓤} X (n , s) = X₀ , p
 where
  open constructions (Fin n)

  X₀ : 𝓤₀ ̇
  X₀ = pr₁ (inverse (ϕ 𝓤) ϕ-is-equiv (X , s))

  p : Lift 𝓤 X₀ ≡ X
  p = ap pr₁ (inverses-are-sections (ϕ 𝓤) ϕ-is-equiv (X , s))

\end{code}

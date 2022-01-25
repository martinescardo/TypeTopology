Tom de Jong, 25 January 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --experimental-lossy-unification #-}

open import SpartanMLTT

open import UF-FunExt
open import UF-PropTrunc
open import UF-Subsingletons

module DcpoLiftingAlgebraic
        (pt : propositional-truncations-exist)
        (fe : ∀ {𝓤 𝓥} → funext 𝓤 𝓥)
        (𝓤 : Universe)
        (pe : propext 𝓤)
       where

open PropositionalTruncation pt

open import UF-Equiv

open import UF-Miscelanea
open import UF-Subsingletons-FunExt

open import UF-ImageAndSurjection
open ImageAndSurjection pt

open import Lifting 𝓤 hiding (⊥)
open import LiftingMiscelanea 𝓤
open import LiftingMiscelanea-PropExt-FunExt 𝓤 pe fe
open import LiftingMonad 𝓤

open import Dcpo pt fe 𝓤
open import DcpoLifting pt fe 𝓤 pe
open import DcpoMiscelanea pt fe 𝓤
open import DcpoWayBelow pt fe 𝓤

open import Poset fe

module _
        {X : 𝓤 ̇ }
        (X-is-set : is-set X)
       where

 κ : 𝟙{𝓤} + X → 𝓛 X
 κ (inl ⋆) = ⊥ (𝓛-DCPO⊥ X-is-set)
 κ (inr x) = η x

 κ⁺ : (l : 𝓛 X) → (Σ i ꞉ (𝟙 + X) , κ i ⊑' l) → 𝓛 X
 κ⁺ l = κ ∘ pr₁

 -- TODO: κ⁺ is directed, κ⁺-sup

 ηs-are-compact : (x : X) → is-compact (𝓛-DCPO X-is-set) (η x)
 ηs-are-compact x I α δ ηx-below-∐α =
  ∥∥-functor h (≡-to-is-defined (ηx-below-∐α ⋆) ⋆)
   where
    h : (Σ i ꞉ I , is-defined (α i))
      → (Σ i ꞉ I , η x ⊑' α i)
    h (i , pᵢ) = i , (λ _ → e)
     where
      e : η x ≡ α i
      e = η x                      ≡⟨ ηx-below-∐α ⋆ ⟩
          lifting-sup X-is-set α δ ≡⟨ e'            ⟩
          α i                      ∎
       where
        e' = (family-defined-somewhere-sup-≡ X-is-set δ i pᵢ) ⁻¹

 compact-if-in-image-of-κ : (l : 𝓛 X)
                          → l ∈image κ
                          → is-compact (𝓛-DCPO X-is-set) l
 compact-if-in-image-of-κ l l-in-image-of-κ =
  ∥∥-rec (being-compact-is-prop (𝓛-DCPO X-is-set) l) γ l-in-image-of-κ
   where
    γ : (Σ i ꞉ domain κ , κ i ≡ l)
      → is-compact (𝓛-DCPO X-is-set) l
    γ (inl ⋆ , refl) = ⊥-is-compact (𝓛-DCPO⊥ X-is-set)
    γ (inr x , refl) = ηs-are-compact x

 in-image-of-κ-if-compact : (l : 𝓛 X)
                          → is-compact (𝓛-DCPO X-is-set) l
                          → l ∈image κ
 in-image-of-κ-if-compact l@(P , φ , P-is-prop) l-cpt = ∥∥-functor goal claim
  where
   I : 𝓤 ̇
   I = 𝟙{𝓤} + P
   α : I → 𝓛 X
   α = add-⊥ (𝓛-DCPO⊥ X-is-set) (η ∘ φ)
   δ : is-Directed (𝓛-DCPO X-is-set) α
   -- TODO: This is where we use --experimental-lossy-unification
   δ = add-⊥-is-directed (𝓛-DCPO⊥ X-is-set) σ
    where
     σ : is-semidirected _⊑'_ (η ∘ φ)
     σ = subsingleton-indexed-is-semidirected (𝓛-DCPO X-is-set) (η ∘ φ) P-is-prop
   l-below-∐α : l ⊑' ∐ (𝓛-DCPO X-is-set) δ
   l-below-∐α p = l                      ≡⟨ ⦅1⦆ ⟩
                  η (φ p)                ≡⟨ ⦅2⦆ ⟩
                  ∐ (𝓛-DCPO X-is-set) δ ∎
    where
     ⦅1⦆ = is-defined-η-≡ p
     ⦅2⦆ = ∐-is-upperbound (𝓛-DCPO X-is-set) δ (inr p) ⋆
   claim : ∃ i ꞉ I , l ⊑' α i
   claim = l-cpt I α δ l-below-∐α
   goal : (Σ i ꞉ I , l ⊑' α i)
        → (Σ k ꞉ domain κ , κ k ≡ l)
   goal (inl ⋆ , lᵢ) =
    (inl ⋆ , ⊑'-is-antisymmetric (⊥-is-least (𝓛-DCPO⊥ X-is-set) l) lᵢ)
   goal (inr p , lᵢ) =
    (inr (φ p) , ((lᵢ p) ⁻¹))

 -- TODO: κ-is-small-compact-basis : is-small-compact-basis (𝓛-DCPO X-is-set) κ

\end{code}

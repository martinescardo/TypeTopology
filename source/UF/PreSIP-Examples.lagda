Martin Escardo, 24 Feb 2023

Modified from SIP-Examples. Only the examples we need are included for the moment.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF.PreSIP-Examples where

open import MLTT.Spartan
open import Notation.Order

open import UF.Base
open import UF.PreSIP
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.PreUnivalence
open import UF.EquivalenceExamples
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Embeddings
open import UF.FunExt

module generalized-metric-space
        {𝓤 𝓥 𝓦  : Universe}
        (R : 𝓥 ̇ )
        (axioms  : (X : 𝓤 ̇ ) → (X → X → R) → 𝓦 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (d : X → X → R) → is-prop (axioms X d))
       where

 open presip
 open presip-with-axioms

 S : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ̇
 S X = X → X → R

 sns-data : SNS S (𝓤 ⊔ 𝓥)
 sns-data = (ι , ρ , θ)
  where
   ι : (A B : Σ S) → ⟨ A ⟩ ≃ ⟨ B ⟩ → 𝓤 ⊔ 𝓥 ̇
   ι (X , d) (Y , e) (f , _) = (d ＝ λ x x' → e (f x) (f x'))

   ρ : (A : Σ S) → ι A A (≃-refl ⟨ A ⟩)
   ρ (X , d) = 𝓻𝓮𝒻𝓵 d

   h : {X : 𝓤 ̇ } {d e : S X} → canonical-map ι ρ d e ∼ -id (d ＝ e)
   h (refl {d}) = 𝓻𝓮𝒻𝓵 (𝓻𝓮𝒻𝓵 d)

   θ : {X : 𝓤 ̇ } (d e : S X) → is-embedding (canonical-map ι ρ d e)
   θ d e = equivs-are-embeddings
            (canonical-map ι ρ d e)
            (equiv-closed-under-∼ id
              (canonical-map ι ρ d e)
              (id-is-equiv (d ＝ e))
              h)

 M : 𝓤 ⁺ ⊔ 𝓥 ⊔ 𝓦 ̇
 M = Σ X ꞉ 𝓤 ̇ , Σ d ꞉ (X → X → R) , axioms X d

 _≅₀_  : M → M → 𝓤 ⊔ 𝓥 ̇
 (X , d , _) ≅₀ (Y , e , _) = Σ f ꞉ (X → Y)
                                  , is-equiv f
                                  × (d ＝ λ x x' → e (f x) (f x'))

 M-embedding₀ : is-preunivalent 𝓤 → (A B : M) → (A ＝ B) ↪ (A ≅₀ B)
 M-embedding₀ pua = ＝-embedding-with-axioms pua sns-data axioms axiomss

 _≅₁_  : M → M → 𝓤 ⊔ 𝓥 ̇
 (X , d , _) ≅₁ (Y , e , _) = Σ f ꞉ (X → Y)
                                  , is-equiv f
                                  × ((x x' : X) → d x x' ＝ e (f x) (f x'))

 ≅₀-coincides-with-≅₁ : Fun-Ext → (A B : M) → (A ≅₀ B) ≃ (A ≅₁ B)
 ≅₀-coincides-with-≅₁ fe (X , d , _) (Y , e , _) =
  Σ-cong (λ f → ×-cong
                 (≃-refl (is-equiv f))
                 (≃-funext₂ fe fe d (λ x x' → e (f x) (f x'))))

 M-embedding₁ : is-preunivalent 𝓤
              → Fun-Ext
              → (A B : M) → (A ＝ B) ↪ (A ≅₁ B)
 M-embedding₁ pua fe A B = (A ＝ B) ↪⟨ M-embedding₀ pua A B ⟩
                           (A ≅₀ B) ↪⟨ ≃-gives-↪ (≅₀-coincides-with-≅₁ fe A B) ⟩
                           (A ≅₁ B) □

module relational-space
        {𝓤 𝓥 𝓦 : Universe}
        (axioms  : (X : 𝓤 ̇ ) → (X → X → 𝓥 ̇ ) → 𝓦 ̇ )
        (axiomss : (X : 𝓤 ̇ ) (R : X → X → 𝓥 ̇ ) → is-prop (axioms X R))
        (rel-is-prop-valued : ∀ {X R} → axioms X R → ∀ {x y} → is-prop (R x y))
       where

 open presip
 open presip-with-axioms
 open generalized-metric-space (𝓥 ̇ ) axioms axiomss

 _≅₂_ : M → M → 𝓤 ⊔ 𝓥 ̇
 (X , R , _) ≅₂ (Y , S , _) = Σ f ꞉ (X → Y)
                                  , is-equiv f
                                  × ((x x' : X) → R x x' ⇔ S (f x) (f x'))

 ≅₁-coincides-with-≅₂ : Fun-Ext
                      → Prop-Ext
                      → (A B : M) → (A ≅₁ B) ≃ (A ≅₂ B)
 ≅₁-coincides-with-≅₂ fe pe A@(X , R , a) B@(Y , S , b) =
  Σ-cong
   (λ f → ×-cong
           (≃-refl (is-equiv f))
           (Π-cong' fe (λ x →
            Π-cong' fe (λ x' →
             prop-＝-≃-⇔ pe fe
              (rel-is-prop-valued a)
              (rel-is-prop-valued b)))))

 M-embedding₂ : is-preunivalent 𝓤
              → Fun-Ext
              → Prop-Ext
              → (A B : M) → (A ＝ B) ↪ (A ≅₂ B)
 M-embedding₂ pua fe pe A B =
  (A ＝ B) ↪⟨ M-embedding₁ pua fe A B ⟩
  (A ≅₁ B) ↪⟨ ≃-gives-↪ (≅₁-coincides-with-≅₂ fe pe A B) ⟩
  (A ≅₂ B) □

\end{code}

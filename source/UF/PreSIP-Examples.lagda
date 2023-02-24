Martin Escardo, 24 Feb 2023

Modified from SIP-Examples. Only the examples we need are included for the moment.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module UF.PreSIP-Examples where

open import MLTT.Spartan
open import Notation.Order

open import UF.Base
open import UF.PreSIP
open import UF.Equiv hiding (_≅_)
open import UF.PreUnivalence
open import UF.EquivalenceExamples
open import UF.Subsingletons
open import UF.Embeddings
open import UF.Subsingletons-FunExt
open import UF.FunExt
open import UF.UA-FunExt
open import UF.Retracts
open import UF.Yoneda

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

 _≅_  : M → M → 𝓤 ⊔ 𝓥 ̇
 (X , d , _) ≅ (Y , e , _) = Σ f ꞉ (X → Y), is-equiv f
                                          × (d ＝ λ x x' → e (f x) (f x'))

 M-embedding : is-preunivalent 𝓤
             → (A B : M)

             → (A ＝ B) ↪ (A ≅ B)

 M-embedding ua = ＝-embedding-with-axioms ua
                                sns-data
                                axioms
                                axiomss

 _≅'_  : M → M → 𝓤 ⊔ 𝓥 ̇
 (X , d , _) ≅' (Y , e , _)
             = Σ f ꞉ (X → Y), is-equiv f
                            × ((x x' : X) → d x x' ＝ e (f x) (f x'))


 M-embedding' : Preunivalence
              → Fun-Ext
              → ((X , d , a) (Y , e , b) : M)
              → ((X , d , a) ＝ (Y , e , b))
                             ↪  (Σ f ꞉ (X → Y)
                                     , is-equiv f
                                     × ((x x' : X) → d x x' ＝ e (f x) (f x')))

 M-embedding' pua fe (X , d , a) (Y , e , b) =
    ((X , d , a) ＝ (Y , e , b)) ↪⟨ M-embedding (pua 𝓤) (X , d , a) (Y , e , b) ⟩
    ((X , d , a) ≅ (Y , e , b))  ↪⟨ ≃-gives-↪ i ⟩
    _                            □
  where
   i = Σ-cong (λ f → ×-cong (≃-refl (is-equiv f))
                      (≃-funext₂ fe fe
                        (λ x y → d x y)
                        (λ x x' → e (f x) (f x'))))
\end{code}

Martin Escardo, Paulo Oliva, June 2024

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module RelativeMonadOnStructuredTypes.OneSigmaStructure where

record 𝟙-Σ-structure : 𝓤ω where
 field
  S : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  𝟙-is-S : {𝓤 : Universe} → S (𝟙 {𝓤})

 𝕊 : (𝓤 : Universe) → 𝓤 ⁺ ̇
 𝕊 𝓤 = Σ X ꞉ 𝓤 ̇ , S X

 ⟨_⟩ : {𝓤 : Universe} → 𝕊 𝓤 → 𝓤 ̇
 ⟨_⟩ = pr₁

 underlying-structure : {𝓤 : Universe} (𝓧 : 𝕊 𝓤) → S ⟨ 𝓧 ⟩
 underlying-structure = pr₂

 𝟙ₛ : {𝓤 : Universe} → 𝕊 𝓤
 𝟙ₛ = 𝟙 , 𝟙-is-S

 field
  Σ-is-S
     : {𝓤 𝓥 : Universe}
       (𝓧 : 𝕊 𝓤)
       (𝓨 : ⟨ 𝓧 ⟩ → 𝕊 𝓥)
     → S (Σ x ꞉ ⟨ 𝓧 ⟩ , ⟨ 𝓨 x ⟩)

 Sigmaₛ : {𝓤 𝓥 : Universe} (𝓧 : 𝕊 𝓤) (𝓨 : ⟨ 𝓧 ⟩ → 𝕊 𝓥) → 𝕊 (𝓤 ⊔ 𝓥)
 Sigmaₛ {𝓤} {𝓥} 𝓧 𝓨 = (Σ x ꞉ ⟨ 𝓧 ⟩ , ⟨ 𝓨 x ⟩) , Σ-is-S 𝓧 𝓨

 syntax Sigmaₛ 𝓧 (λ x → 𝓨) = Σₛ x ꞉ 𝓧 , 𝓨

 infixr -1 Sigmaₛ

\end{code}

Some typical examples that we are going to need.

\begin{code}

open import UF.DiscreteAndSeparated
open import TypeTopology.SigmaDiscreteAndTotallySeparated

discrete-𝟙-Σ-structure : 𝟙-Σ-structure
discrete-𝟙-Σ-structure =
 record {
  S      = is-discrete ;
  𝟙-is-S = 𝟙-is-discrete ;
  Σ-is-S = λ (X , d) 𝓨 → Σ-is-discrete d (λ x → pr₂ (𝓨 x))
  }

\end{code}

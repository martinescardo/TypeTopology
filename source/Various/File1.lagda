Alice Laroche , 26th September 2023
\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Univalence

module Various.File1
        (ua : Univalence)
        (𝓤 : Universe)
       where

open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Subsingletons
open import Iterative.Multisets 𝓤
open import Iterative.Multisets-Addendum ua 𝓤
open import Iterative.Sets ua 𝓤
open import Iterative.Sets-Addendum ua 𝓤
open import Iterative.Ordinals ua 𝓤

𝟘ⱽ-is-transitive-iset : is-transitive-iset 𝟘ⱽ
𝟘ⱽ-is-transitive-iset v₁ v₂ ()

𝟘ⱽ-has-transitive-members : has-transitive-members 𝟘ⱽ
𝟘ⱽ-has-transitive-members v₁ () 

𝟘ⱽ-is-iordinal : is-iterative-ordinal 𝟘ⱽ
𝟘ⱽ-is-iordinal = 𝟘ⱽ-is-transitive-iset , 𝟘ⱽ-has-transitive-members

𝟘ᴼ : 𝕆
𝟘ᴼ = 𝟘ⱽ , 𝟘ⱽ-is-iordinal

𝟙ⱽ-is-transitive-iset : is-transitive-iset 𝟙ⱽ
𝟙ⱽ-is-transitive-iset v₁ v₂ (⋆ , p) (b , q) =
 ⋆ , 𝟘-elim (transport (𝕄-root) (p ⁻¹) b)

𝟙ⱽ-has-transitive-members : has-transitive-members 𝟙ⱽ
𝟙ⱽ-has-transitive-members v₁ (⋆ , p) = II
 where
  I : 𝟘ⱽ ＝ v₁
  I = to-subtype-＝ being-iset-is-prop p

  II : is-transitive-iset v₁
  II = transport is-transitive-iset I 𝟘ⱽ-is-transitive-iset 
  
𝟙ⱽ-is-iordinal : is-iterative-ordinal 𝟙ⱽ
𝟙ⱽ-is-iordinal = 𝟙ⱽ-is-transitive-iset , 𝟙ⱽ-has-transitive-members

𝟙ᴼ : 𝕆
𝟙ᴼ = 𝟙ⱽ , 𝟙ⱽ-is-iordinal

\end{code}

Martin Escardo 7th November 2018.

Remark. Another equivalent way to define the multiplication, which has
a different universe level:

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module Lifting.MonadVariation where

open import UF.Subsingletons
open import UF.Embeddings
open import UF.Equiv
open import UF.FunExt

open import Lifting.Lifting
open import Lifting.EmbeddingDirectly

𝓛* : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → is-embedding f → 𝓛 𝓣 Y → 𝓛 (𝓤 ⊔ 𝓥 ⊔ 𝓣) X
𝓛* f e (Q , ψ , j) = (Σ q ꞉ Q , fiber f (ψ q)) ,
                      (λ p → pr₁ (pr₂ p)) ,
                      Σ-is-prop j (e ∘ ψ)

μ* : (𝓣 𝓣' : Universe) {X : 𝓤 ̇ }
   → funext 𝓣 𝓣
   → funext 𝓣' 𝓣'
   → funext 𝓣' 𝓤
   → funext 𝓤 (𝓤 ⊔ (𝓣' ⁺))
   → propext 𝓣'
   → 𝓛 𝓣 (𝓛 𝓣' X) → 𝓛 (𝓤 ⊔ 𝓣 ⊔ (𝓣' ⁺)) X
μ* {𝓤} 𝓣 𝓣' {X} fe fe' fe'' fe''' pe = 𝓛* (η 𝓣') (η-is-embedding 𝓣' pe fe' fe'' fe''')

\end{code}

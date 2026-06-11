Martin Escardo, 31st May 2026.

The type of totally separated ordinals is (algebraically)
injective. Examples of totally separated ordinals are 𝟘, 𝟙 (and any
proposition), 𝟚, Fin n, ℕ + 𝟙 and ℕ∞ with their natural orders
(defined elsewhere in this repository). In particular, the type of
totally separated ordinals doesn't admit a non-trivial apartness in
general, and hence isn't totally separated itself.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module Ordinals.TotallySeparated where

open import MLTT.Spartan
open import Ordinals.Type
open import Ordinals.Underlying
open import UF.Embeddings
open import UF.Subsingletons
open import UF.Univalence
open import Ordinals.Injectivity
open import TypeTopology.TotallySeparated

TSOrdinal : ∀ 𝓤 → 𝓤 ⁺ ̇
TSOrdinal 𝓤 = Σ α ꞉ Ordinal 𝓤 , is-totally-separated ⟨ α ⟩

underlying-ordinal : TSOrdinal 𝓤 → Ordinal 𝓤
underlying-ordinal = pr₁

⟪_⟫ : TSOrdinal 𝓤 → 𝓤 ̇
⟪ τ ⟫ = ⟨ underlying-ordinal τ ⟩

total-separatedness-of-underlying-ordinal : (τ : TSOrdinal 𝓤)
                                          → is-totally-separated ⟪ τ ⟫
total-separatedness-of-underlying-ordinal = pr₂

module _ (fe : FunExt) where

 private
  fe' : Fun-Ext
  fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 open import InjectiveTypes.Blackboard fe
 open ordinals-injectivity fe

 ↗-is-totally-separated : {I : 𝓤 ̇ } {J : 𝓥 ̇ }
                          (α : I → Ordinal 𝓦)
                          (𝓮 : I ↪ J)
                        → ((i : I) → is-totally-separated ⟨ α i ⟩)
                        → ((j : J) → is-totally-separated ⟨ (α ↗ 𝓮) j ⟩)
 ↗-is-totally-separated α 𝓮 t j = Π-is-totally-separated fe'
                                   (λ φ → t (fiber-point φ))

 TSOrdinal-is-ainjective : is-univalent (𝓤 ⊔ 𝓥)
                         → ainjective-type (TSOrdinal (𝓤 ⊔ 𝓥)) 𝓤 𝓥
 TSOrdinal-is-ainjective {𝓤} {𝓥} ua {I} {J} e e-is-embedding α = γ
  where
   β : I → Ordinal (𝓤 ⊔ 𝓥)
   β x = underlying-ordinal (α x)

   𝓮 : I ↪ J
   𝓮 = (e , e-is-embedding)

   α↗𝓮 : J → TSOrdinal (𝓤 ⊔ 𝓥)
   α↗𝓮 y = (β ↗ 𝓮) y ,
           ↗-is-totally-separated
            β
            𝓮
            (λ i → total-separatedness-of-underlying-ordinal (α i)) y

   γ : Σ α↗𝓮 ꞉ (J → TSOrdinal (𝓤 ⊔ 𝓥)) , (α↗𝓮 ∘ e ∼ α)
   γ = α↗𝓮 ,
       (λ i → to-subtype-＝
                (λ α → being-totally-separated-is-prop fe' ⟨ α ⟩)
                (↗-property ua β 𝓮 i))

\end{code}

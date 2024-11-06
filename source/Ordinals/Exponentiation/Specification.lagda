Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu
6 November 2024

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

open import UF.PropTrunc
open import UF.Size
open import UF.Univalence

module Ordinals.Exponentiation.Specification
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import MLTT.Spartan
open import UF.FunExt
open import UF.ImageAndSurjection pt
open import UF.UA-FunExt
open import UF.UniverseEmbedding

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

open import Ordinals.Arithmetic fe
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Type

open PropositionalTruncation pt
open suprema pt sr

-- TODO: Explain in a comment what F is supposed to represent (exponentation with base α)

module _
        (α : Ordinal 𝓤)
        (F : {𝓥 : Universe} → Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥))
       where

 exp-specification-zero : (𝓤 ⊔ 𝓥) ⁺ ̇
 exp-specification-zero {𝓥} = F (𝟘ₒ {𝓥}) ＝ 𝟙ₒ

 exp-specification-succ : (𝓤 ⊔ 𝓥) ⁺ ̇
 exp-specification-succ {𝓥} = (β : Ordinal 𝓥) → F (β +ₒ 𝟙ₒ) ＝ (F β ×ₒ α)

 exp-specification-sup : 𝓤 ⁺ ̇
 exp-specification-sup =
   𝟙ₒ{𝓤} ⊴ α → {I : 𝓤 ̇  } → ∥ I ∥ → (β : I → Ordinal 𝓤) → F (sup β) ＝ sup (F ∘ β)

 exp-specification-sup-generalized : (𝓤 ⊔ 𝓥) ⁺ ̇
 exp-specification-sup-generalized {𝓥} =
   𝟙ₒ{𝓤} ⊴ α → {I : 𝓥 ̇  } (β : I → Ordinal 𝓥) → ∥ I ∥
             → F (sup β) ＝ sup (λ (i : Lift 𝓤 I) → F (β (lower i)))

\end{code}
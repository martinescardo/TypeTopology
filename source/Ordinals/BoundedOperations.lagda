Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu.
14 July 2025.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.BoundedOperations
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import MLTT.Spartan

open import UF.Base
-- open import UF.ImageAndSurjection pt
open import UF.Subsingletons
-- open import UF.UniverseEmbedding

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Exponentiation.Specification ua pt sr
open import Ordinals.Maps
open import Ordinals.MultiplicationProperties ua
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

open PropositionalTruncation pt
open suprema pt sr

_greatest-satisfying_ : Ordinal 𝓤 → (Ordinal 𝓤 → 𝓥 ̇ ) → 𝓤 ⁺ ⊔ 𝓥 ̇
_greatest-satisfying_ {𝓤} γ P = (α : Ordinal 𝓤) → P α → α ⊴ γ

module greatest-element-satisfying-predicate
        (P : Ordinal 𝓤 → 𝓤 ̇ )
        (P-closed-under-suprema : {I : 𝓤 ̇ } (F : I → Ordinal 𝓤)
                                → ((i : I) → P (F i))
                                → P (sup F))
        (P-antitone : (α β : Ordinal 𝓤) → α ⊴ β → P β → P α)
        (P-bounded : Σ β ꞉ Ordinal 𝓤 , ((α : Ordinal 𝓤) → P α → α ⊴ β))
       where

 private
  β : Ordinal 𝓤
  β = pr₁ P-bounded
  β-is-bound : (α : Ordinal 𝓤) → P α → α ⊴ β
  β-is-bound = pr₂ P-bounded

  S : (α : Ordinal 𝓤) → ⟨ α ⟩ → Ordinal 𝓤
  S α a = (α ↓ a) +ₒ 𝟙ₒ

 γ : Ordinal 𝓤
 γ = sup {𝓤} {Σ b ꞉ ⟨ β ⟩ , P (S β b)} (λ (b , _) → S β b)

 γ-satisfies-P : P γ
 γ-satisfies-P = P-closed-under-suprema (λ (b , _) → S β b) (λ (b , p) → p)

 γ-greatest-satisfying-P : γ greatest-satisfying P
 γ-greatest-satisfying-P α p = to-⊴ α γ I
  where
   II : (a : ⟨ α ⟩) → Σ bₐ ꞉ ⟨ β ⟩ , α ↓ a ＝ β ↓ bₐ
   II = from-≼ (⊴-gives-≼ α β (β-is-bound α p))
   I : (a : ⟨ α ⟩) → α ↓ a ⊲ γ
   I a = c , (α ↓ a ＝⟨ eq ⟩
              β ↓ bₐ ＝⟨ (successor-lemma-right (β ↓ bₐ)) ⁻¹ ⟩
              S β bₐ ↓ inr ⋆ ＝⟨ (initial-segment-of-sup-at-component _ (bₐ , p') (inr ⋆)) ⁻¹ ⟩
              γ ↓ c ∎)
    where
     bₐ = pr₁ (II a)
     eq = pr₂ (II a)
     p' : P (S β bₐ)
     p' = transport P (ap (_+ₒ 𝟙ₒ) eq) p''
      where
       p'' : P (S α a)
       p'' = P-antitone _ _ (upper-bound-of-successors-of-initial-segments α a) p
     c : ⟨ γ ⟩
     c = [ S β bₐ , γ ]⟨ sup-is-upper-bound _ (bₐ , p') ⟩ (inr ⋆)

approximate-subtraction
 : (α β : Ordinal 𝓤) → α ⊴ β
 → Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying (λ - → (α +ₒ - ⊴ β) × (- ⊴ β))
approximate-subtraction {𝓤} α β β-above-α = γ , γ-greatest-satisfying-P
 where
  P : Ordinal 𝓤 → 𝓤 ̇
  P δ = (α +ₒ δ ⊴ β) × (δ ⊴ β)
  P-closed-under-suprema : {I : 𝓤 ̇ } (F : I → Ordinal 𝓤)
                         → ((i : I) → P (F i))
                         → P (sup F)
  P-closed-under-suprema {I} F ρ =
      {!!} -- Should formalize [α +ₒ (sup F) ＝ α ∨ sup (λ i → α +ₒ F i)]
    , (sup-is-lower-bound-of-upper-bounds F β (λ i → pr₂ (ρ i)))
  P-antitone : (α₁ α₂ : Ordinal 𝓤) → α₁ ⊴ α₂ → P α₂ → P α₁
  P-antitone α₁ α₂ k (l , m) =
     ⊴-trans (α +ₒ α₁) (α +ₒ α₂) β (≼-gives-⊴ _ _ (+ₒ-right-monotone α α₁ α₂ (⊴-gives-≼ α₁ α₂ k))) l
     -- Should record monotonicity for ⊴
   , ⊴-trans α₁ α₂ β k m
  P-bounded : Σ β ꞉ Ordinal 𝓤 , ((α : Ordinal 𝓤) → P α → α ⊴ β)
  P-bounded = β , (λ α p → pr₂ p)
  open greatest-element-satisfying-predicate P P-closed-under-suprema P-antitone P-bounded



\end{code}

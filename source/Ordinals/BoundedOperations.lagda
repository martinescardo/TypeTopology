Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu.
14 July 2025.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

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
_greatest-satisfying_ {𝓤} γ P = P γ × ((α : Ordinal 𝓤) → P α → α ⊴ γ)

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

 γ-greatest : (α : Ordinal 𝓤) → P α → α ⊴ γ
 γ-greatest α p = to-⊴ α γ I
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

 γ-greatest-satisfying-P : γ greatest-satisfying P
 γ-greatest-satisfying-P = γ-satisfies-P , γ-greatest

-- Note that we can't quite assume continuity, but we can assume something like
-- t (sup F) ＝ c ∨ sup (t ∘ F) for some suitable c

module Enderton
        (t : Ordinal 𝓤 → Ordinal 𝓤)
        (δ₀ δ : Ordinal 𝓤)
        (δ₀-below-δ : δ₀ ⊴ δ)
        (t-preserves-suprema : {I : 𝓤 ̇ } (F : I → Ordinal 𝓤) -- TODO: rename
                         → t (sup F) ＝ sup (cases (λ (_ : 𝟙{𝓤}) → δ₀) (λ i → t (F i))))
       where

 private
  t-is-monotone : (α β : Ordinal 𝓤) → α ⊴ β → t α ⊴ t β
  t-is-monotone α β l = III
   where
    F : 𝟙{𝓤} + 𝟙{𝓤} → Ordinal 𝓤
    F (inl ⋆) = α
    F (inr ⋆) = β
    I : sup F ＝ β
    I = ⊴-antisym (sup F) β
         (sup-is-lower-bound-of-upper-bounds F β ub)
         (sup-is-upper-bound F (inr ⋆))
     where
      ub : (i : 𝟙 + 𝟙) → F i ⊴ β
      ub (inl ⋆) = l
      ub (inr ⋆) = ⊴-refl β
    II : t (sup F) ＝ sup (cases (λ _ → δ₀) (λ i → t (F i)))
    II = t-preserves-suprema F
    III : t α ⊴ t β
    III = transport⁻¹
           (t α ⊴_)
           (ap t I ⁻¹ ∙ II)
           (sup-is-upper-bound (cases (λ _ → δ₀) (t ∘ F)) (inr (inl ⋆)))

 enderton : Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying (λ - → (t - ⊴ δ) × (- ⊴ δ))
 enderton = γ , γ-greatest-satisfying-P
  where
   P : Ordinal 𝓤 → 𝓤 ̇
   P α = (t α ⊴ δ) × (α ⊴ δ)
   P-closed-under-suprema : {I : 𝓤 ̇ } (F : I → Ordinal 𝓤)
                          → ((i : I) → P (F i))
                          → P (sup F)
   P-closed-under-suprema {I} F ρ =
    transport⁻¹ (_⊴ δ) (t-preserves-suprema F) σ ,
    sup-is-lower-bound-of-upper-bounds F δ (λ i → pr₂ (ρ i))
     where
      σ : sup (cases (λ ⋆ → δ₀) (λ i → t (F i))) ⊴ δ
      σ = sup-is-lower-bound-of-upper-bounds _ δ h
       where
        h : (x : 𝟙 + I) → cases (λ ⋆ → δ₀) (λ i → t (F i)) x ⊴ δ
        h (inl ⋆) = δ₀-below-δ
        h (inr i) = pr₁ (ρ i)
   P-antitone : (α₁ α₂ : Ordinal 𝓤) → α₁ ⊴ α₂ → P α₂ → P α₁
   P-antitone α₁ α₂ k (l , m) =
     ⊴-trans (t α₁) (t α₂) δ (t-is-monotone α₁ α₂ k) l ,
     ⊴-trans α₁ α₂ δ k m
   P-bounded : Σ β ꞉ Ordinal 𝓤 , ((α : Ordinal 𝓤) → P α → α ⊴ β)
   P-bounded = δ , (λ α p → pr₂ p)
   open greatest-element-satisfying-predicate P P-closed-under-suprema P-antitone P-bounded

approximate-subtraction
 : (α β : Ordinal 𝓤) → α ⊴ β
 → Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying (λ - → (α +ₒ - ⊴ β) × (- ⊴ β))
approximate-subtraction {𝓤} α β β-above-α = enderton
 where
  open Enderton (α +ₒ_) α β β-above-α (+ₒ-preserves-suprema pt sr α)

approximate-division
 : (α β : Ordinal 𝓤) → 𝟘ₒ ⊲ β -- In our weakening this assumption becomes redundant
 → Σ γ ꞉ Ordinal 𝓤 ,
    γ greatest-satisfying (λ - → (β ×ₒ - ⊴ α) × (- ⊴ α))
approximate-division {𝓤} α β β-pos = enderton
 where -- TODO: Upstream this part into the Enderton module
  σ : {I : 𝓤 ̇} (F : I → Ordinal 𝓤)
    → β ×ₒ sup F ＝ sup (cases (λ _ → 𝟘ₒ) (λ i → β ×ₒ F i))
  σ {I} F = e₁ ∙ e₂
   where
    e₁ : β ×ₒ sup F ＝ sup (λ i → β ×ₒ F i)
    e₁ = ×ₒ-preserves-suprema pt sr β F
    e₂ : sup (λ i → β ×ₒ F i) ＝ sup (cases (λ _ → 𝟘ₒ) (λ i → β ×ₒ F i))
    e₂ = ⊴-antisym _ _ u v
     where
      u : sup (λ i → β ×ₒ F i) ⊴ sup (cases (λ _ → 𝟘ₒ) (λ i → β ×ₒ F i))
      u = sup-is-lower-bound-of-upper-bounds _ _ (λ i → sup-is-upper-bound _ (inr i))
      v : sup (cases (λ _ → 𝟘ₒ) (λ i → β ×ₒ F i)) ⊴ sup (λ i → β ×ₒ F i)
      v = sup-is-lower-bound-of-upper-bounds _ _ w
       where
        w : (x : 𝟙 + I)
          → cases (λ _ → 𝟘ₒ) (λ i → β ×ₒ F i) x ⊴ sup (λ i → β ×ₒ F i)
        w (inl ⋆) = 𝟘ₒ-least-⊴ (sup (λ i → β ×ₒ F i))
        w (inr i) = sup-is-upper-bound (λ j → β ×ₒ F j) i
  open Enderton (β ×ₒ_) 𝟘ₒ α (𝟘ₒ-least-⊴ α) σ

open import Ordinals.Exponentiation.Supremum ua pt sr
aproximate-logarithm
 : (α β : Ordinal 𝓤) → 𝟙ₒ ⊴ β
 → Σ γ ꞉ Ordinal 𝓤 ,
    γ greatest-satisfying (λ - → (α ^ₒ - ⊴ β) × (- ⊴ β))
aproximate-logarithm {𝓤} α β β-pos = enderton
 where
 open Enderton (α ^ₒ_) 𝟙ₒ β β-pos (^ₒ-satisfies-strong-sup-specification α _)

\end{code}

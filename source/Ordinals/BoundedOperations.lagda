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

-- TODO: Capture the common core à la Enderton
-- Note that we can't quite assume continuity, but we can assume something like
-- t (sup F) ＝ c ∨ sup (t ∘ F) for some suitable c

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
      transport⁻¹ (_⊴ β) (+ₒ-preserves-suprema pt sr α F) σ
    , (sup-is-lower-bound-of-upper-bounds F β (λ i → pr₂ (ρ i)))
   where
    σ : sup (cases (λ ⋆ → α) (λ i → α +ₒ F i)) ⊴ β
    σ = sup-is-lower-bound-of-upper-bounds _ β h
     where
      h : (x : 𝟙 + I) → cases (λ _ → α) (λ i → α +ₒ F i) x ⊴ β
      h (inl ⋆) = β-above-α
      h (inr i) = pr₁ (ρ i)
  P-antitone : (α₁ α₂ : Ordinal 𝓤) → α₁ ⊴ α₂ → P α₂ → P α₁
  P-antitone α₁ α₂ k (l , m) =
     ⊴-trans (α +ₒ α₁) (α +ₒ α₂) β (+ₒ-right-monotone-⊴ α α₁ α₂ k) l
   , ⊴-trans α₁ α₂ β k m
  P-bounded : Σ β ꞉ Ordinal 𝓤 , ((α : Ordinal 𝓤) → P α → α ⊴ β)
  P-bounded = β , (λ α p → pr₂ p)
  open greatest-element-satisfying-predicate P P-closed-under-suprema P-antitone P-bounded

approximate-division
 : (α β : Ordinal 𝓤) → 𝟘ₒ ⊲ β
 → Σ γ ꞉ Ordinal 𝓤 ,
    γ greatest-satisfying (λ - → (β ×ₒ - ⊴ α) × (- ⊴ α))
approximate-division {𝓤} α β β-pos = γ , γ-greatest-satisfying-P
 where
  b₀ : ⟨ β ⟩
  b₀ = pr₁ β-pos
  b₀-eq : β ↓ b₀ ＝ 𝟘ₒ
  b₀-eq = (pr₂ β-pos) ⁻¹
  fact : (δ : Ordinal 𝓤) → β ×ₒ δ +ₒ (β ↓ b₀) ＝ β ×ₒ δ
  fact δ = ap (β ×ₒ δ +ₒ_) b₀-eq ∙ 𝟘ₒ-right-neutral (β ×ₒ δ)

  P : Ordinal 𝓤 → 𝓤 ̇
  P δ = (β ×ₒ δ ⊴ α) × (δ ⊴ α)
  P-closed-under-suprema : {I : 𝓤 ̇ } (F : I → Ordinal 𝓤)
                         → ((i : I) → P (F i))
                         → P (sup F)
  P-closed-under-suprema {I} F ρ =
     transport⁻¹ (_⊴ α) (×ₒ-preserves-suprema pt sr β F) (sup-is-lower-bound-of-upper-bounds (λ i → β ×ₒ F i) α (λ i → pr₁ (ρ i)))
   , sup-is-lower-bound-of-upper-bounds F α (λ i → pr₂ (ρ i))
  P-antitone : (α₁ α₂ : Ordinal 𝓤) → α₁ ⊴ α₂ → P α₂ → P α₁
  P-antitone α₁ α₂ k (l , m) = ⊴-trans (β ×ₒ α₁) (β ×ₒ α₂) α (×ₒ-right-monotone-⊴ β α₁ α₂ k) l , ⊴-trans α₁ α₂ α k m
  P-bounded : Σ ε ꞉ Ordinal 𝓤 , ((δ : Ordinal 𝓤) → P δ → δ ⊴ ε)
  P-bounded = α , (λ δ p → pr₂ p)
  open greatest-element-satisfying-predicate P P-closed-under-suprema P-antitone P-bounded

open import Ordinals.Exponentiation.Supremum ua pt sr
aproximate-logarithm
 : (α β : Ordinal 𝓤) → 𝟙ₒ ⊴ β
 → Σ γ ꞉ Ordinal 𝓤 ,
    γ greatest-satisfying (λ - → (α ^ₒ - ⊴ β) × (- ⊴ β))
aproximate-logarithm {𝓤} α β β-pos = γ , γ-greatest-satisfying-P
 where
  P : Ordinal 𝓤 → 𝓤 ̇
  P δ = (α ^ₒ δ ⊴ β) × (δ ⊴ β)
  P-closed-under-suprema : {I : 𝓤 ̇ } (F : I → Ordinal 𝓤)
                         → ((i : I) → P (F i))
                         → P (sup F)
  P-closed-under-suprema {I} F ρ =
   transport⁻¹ (_⊴ β) (^ₒ-satisfies-strong-sup-specification α I F) (sup-is-lower-bound-of-upper-bounds _ β h) ,
   sup-is-lower-bound-of-upper-bounds F β (λ i → pr₂ (ρ i))
    where
     h : (x : 𝟙 + I) → cases (λ _ → 𝟙ₒ) (λ i → α ^ₒ F i) x ⊴ β
     h (inl ⋆) = β-pos
     h (inr i) = pr₁ (ρ i)
  P-antitone : (α₁ α₂ : Ordinal 𝓤) → α₁ ⊴ α₂ → P α₂ → P α₁
  P-antitone α₁ α₂ k (l , m) = ⊴-trans (α ^ₒ α₁) (α ^ₒ α₂) β (^ₒ-monotone-in-exponent α α₁ α₂ k) l , ⊴-trans α₁ α₂ β k m
  P-bounded : Σ ε ꞉ Ordinal 𝓤 , ((δ : Ordinal 𝓤) → P δ → δ ⊴ ε)
  P-bounded = β , (λ δ p → pr₂ p)
  open greatest-element-satisfying-predicate P P-closed-under-suprema P-antitone P-bounded

{-
Original silly version
approximate-division
 : (α β : Ordinal 𝓤) → 𝟘ₒ ⊲ β
 → Σ γ ꞉ Ordinal 𝓤 ,
    γ greatest-satisfying (λ - → Σ b ꞉ ⟨ β ⟩ , (β ×ₒ - +ₒ (β ↓ b) ⊴ α) × (- ⊴ α))
approximate-division {𝓤} α β β-pos = γ , γ-greatest-satisfying-P
 where
  b₀ : ⟨ β ⟩
  b₀ = pr₁ β-pos
  b₀-eq : β ↓ b₀ ＝ 𝟘ₒ
  b₀-eq = (pr₂ β-pos) ⁻¹
  fact : (δ : Ordinal 𝓤) → β ×ₒ δ +ₒ (β ↓ b₀) ＝ β ×ₒ δ
  fact δ = ap (β ×ₒ δ +ₒ_) b₀-eq ∙ 𝟘ₒ-right-neutral (β ×ₒ δ)

  P : Ordinal 𝓤 → 𝓤 ̇
  P δ = Σ b ꞉ ⟨ β ⟩ , (β ×ₒ δ +ₒ (β ↓ b) ⊴ α) × (δ ⊴ α)
  P-closed-under-suprema : {I : 𝓤 ̇ } (F : I → Ordinal 𝓤)
                         → ((i : I) → P (F i))
                         → P (sup F)
  P-closed-under-suprema {I} F ρ =
   b₀ ,
   transport⁻¹ (_⊴ α) (fact (sup F) ∙ ×ₒ-preserves-suprema pt sr β F) t ,
   sup-is-lower-bound-of-upper-bounds F α (λ i → pr₂ (pr₂ (ρ i)))
    where
     t : sup (λ i → β ×ₒ F i) ⊴ α
     t = sup-is-lower-bound-of-upper-bounds _ α s
      where
       s : (i : I) → β ×ₒ F i ⊴ α
       s i = ⊴-trans (β ×ₒ F i) (β ×ₒ F i +ₒ (β ↓ bᵢ)) α (+ₒ-left-⊴ (β ×ₒ F i) (β ↓ bᵢ)) (pr₁ (pr₂ (ρ i)))
        where
         bᵢ : ⟨ β ⟩
         bᵢ = pr₁ (ρ i)
  P-antitone : (α₁ α₂ : Ordinal 𝓤) → α₁ ⊴ α₂ → P α₂ → P α₁
  P-antitone α₁ α₂ k (b , l , m) = b₀ , transport⁻¹ (_⊴ α) (fact α₁) t , ⊴-trans α₁ α₂ α k m
   where
    t : β ×ₒ α₁ ⊴ α
    t = ⊴-trans (β ×ₒ α₁) (β ×ₒ α₂) α (×ₒ-right-monotone-⊴ β α₁ α₂ k) (⊴-trans (β ×ₒ α₂) (β ×ₒ α₂ +ₒ (β ↓ b)) α (+ₒ-left-⊴ (β ×ₒ α₂) (β ↓ b)) l)
  P-bounded : Σ ε ꞉ Ordinal 𝓤 , ((δ : Ordinal 𝓤) → P δ → δ ⊴ ε)
  P-bounded = α , (λ δ p → pr₂ (pr₂ p))
  open greatest-element-satisfying-predicate P P-closed-under-suprema P-antitone P-bounded
-}

{-
open import UF.Subsingletons-FunExt
experiment : (P : 𝓤 ̇ ) → is-prop P → Ordinal 𝓤
experiment {𝓤} P P-is-prop = γ
 where
  Pₒ ¬Pₒ α β : Ordinal 𝓤
  Pₒ = prop-ordinal P P-is-prop
  ¬Pₒ = prop-ordinal (¬ P) (negations-are-props fe')
  α = 𝟚ₒ{𝓤} ×ₒ Pₒ +ₒ ¬Pₒ
  β = 𝟚ₒ{𝓤}
  β-pos : 𝟘ₒ ⊲ β
  β-pos = inl ⋆ , (𝟙ₒ-↓ ⁻¹ ∙ +ₒ-↓-left ⋆)
  γ =  pr₁ (approximate-division α β β-pos)
  bit : 𝟙 + 𝟙
  bit = pr₁ (pr₁ (pr₂ (approximate-division α β β-pos)))
  I : ¬ P → bit ＝ inr ⋆
  I ν = {!!}
   where
    e : α ＝ 𝟙ₒ
    e = {!!}
    fact : 𝟘ₒ greatest-satisfying (λ - → Σ b ꞉ ⟨ β ⟩ , (β ×ₒ - +ₒ (β ↓ b) ⊴ α) × (- ⊴ α))
    fact = ((inr ⋆) , ({!-- OK using e!} , {!-- OK using e!})) , fact'
     where
      fact' : (α₁ : Ordinal 𝓤) →
                Sigma (Underlying.⟨ underlying-type-of-ordinal ⟩ β)
                (λ b → β ×ₒ α₁ +ₒ (β ↓ b) ⊴ α × α₁ ⊴ α) →
                α₁ ⊴ 𝟘ₒ
      fact' δ (b , k , l) = {!-- OK as δ must be empty by k and e!}
    foo : γ ⊴ 𝟘ₒ
    foo = pr₂ fact γ (pr₁ ((pr₂ (approximate-division α β β-pos))))
-}

\end{code}

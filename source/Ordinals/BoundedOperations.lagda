Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu.
14-15 July 2025.

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
                         → t (sup F) ＝ sup (cases (λ (_ : 𝟙{𝓤}) → δ₀) (t ∘ F)))
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
    II : t (sup F) ＝ sup (cases (λ _ → δ₀) (t ∘ F))
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

module Enderton'
        (t : Ordinal 𝓤 → Ordinal 𝓤)
        (δ : Ordinal 𝓤)
        (t-preserves-suprema : {I : 𝓤 ̇ } (F : I → Ordinal 𝓤)
                             → t (sup F) ＝ sup (t ∘ F))
       where

 t-preserves-suprema-up-to-join
  : {I : 𝓤 ̇} (F : I → Ordinal 𝓤)
  → t (sup F) ＝ sup (cases (λ _  → 𝟘ₒ) (t ∘ F))
 t-preserves-suprema-up-to-join {I} F =
  t-preserves-suprema F
  ∙ (⊴-antisym (sup (t ∘ F)) (sup G) u v)
  where
   G : 𝟙{𝓤} + I → Ordinal 𝓤
   G = cases (λ _ → 𝟘ₒ) (t ∘ F)
   u : sup (t ∘ F) ⊴ sup G
   u = sup-is-lower-bound-of-upper-bounds (t ∘ F) (sup G)
        (λ i → sup-is-upper-bound G (inr i))
   v : sup G ⊴ sup (t ∘ F)
   v = sup-is-lower-bound-of-upper-bounds G (sup (t ∘ F)) w
    where
     w : (x : 𝟙 + I)
       → cases (λ _ → 𝟘ₒ) (t ∘ F) x ⊴ sup (t ∘ F)
     w (inl ⋆) = 𝟘ₒ-least-⊴ (sup (t ∘ F))
     w (inr i) = sup-is-upper-bound (t ∘ F) i

 open Enderton t 𝟘ₒ δ (𝟘ₒ-least-⊴ δ) t-preserves-suprema-up-to-join public

module Enderton-classical-variation
        (t : Ordinal 𝓤 → Ordinal 𝓤)
        (δ₀ δ : Ordinal 𝓤)
        (δ₀-below-δ : δ₀ ⊴ δ)
        (t-preserves-suprema : {I : 𝓤 ̇ } (F : I → Ordinal 𝓤) -- TODO: rename
                         → t (sup F) ＝ sup (cases (λ (_ : 𝟙{𝓤}) → δ₀) (t ∘ F)))
        (t-increasing : (α : Ordinal 𝓤) → α ⊴ t α)
       where

 enderton-classical : Σ γ ꞉ Ordinal 𝓤 , γ ⊴ δ × γ greatest-satisfying (λ - → (t - ⊴ δ))
 enderton-classical = γ , γ-fact₂ , γ-fact₁ , γ-fact₄
  where
   open Enderton t δ₀ δ δ₀-below-δ t-preserves-suprema
   I : Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying (λ - → t - ⊴ δ × - ⊴ δ)
   I = enderton
   γ : Ordinal 𝓤
   γ = pr₁ I
   γ-fact₁ : t γ ⊴ δ
   γ-fact₁ = pr₁ (pr₁ (pr₂ I))
   γ-fact₂ : γ ⊴ δ
   γ-fact₂ = pr₂ (pr₁ (pr₂ I))
   γ-fact₃ : (α : Ordinal 𝓤) → (t α ⊴ δ) × (α ⊴ δ) → α ⊴ γ
   γ-fact₃ = pr₂ (pr₂ I)
   γ-fact₄ : (α : Ordinal 𝓤) → t α ⊴ δ → α ⊴ γ
   γ-fact₄ α l = γ-fact₃ α (l , (⊴-trans α (t α) δ (t-increasing α) l))

module Enderton-classical-variation'
        (t : Ordinal 𝓤 → Ordinal 𝓤)
        (δ : Ordinal 𝓤)
        (t-preserves-suprema : {I : 𝓤 ̇ } (F : I → Ordinal 𝓤)
                         → t (sup F) ＝ sup (t ∘ F))
        (t-increasing : (α : Ordinal 𝓤) → α ⊴ t α)
       where

 open Enderton-classical-variation t 𝟘ₒ δ (𝟘ₒ-least-⊴ δ) (Enderton'.t-preserves-suprema-up-to-join t δ t-preserves-suprema) t-increasing public

approximate-subtraction
 : (α β : Ordinal 𝓤) → α ⊴ β
 → Σ γ ꞉ Ordinal 𝓤 , γ greatest-satisfying (λ - → (α +ₒ - ⊴ β) × (- ⊴ β))
approximate-subtraction {𝓤} α β β-above-α = enderton
 where
  open Enderton (α +ₒ_) α β β-above-α (+ₒ-preserves-suprema pt sr α)

approximate-division
 : (α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α -- In our weakening this assumption becomes redundant
 → Σ γ ꞉ Ordinal 𝓤 ,
    γ greatest-satisfying (λ - → (α ×ₒ - ⊴ β) × (- ⊴ β))
approximate-division {𝓤} α β α-pos = enderton
 where
  open Enderton' (α ×ₒ_) β (×ₒ-preserves-suprema pt sr α)

open import Ordinals.Exponentiation.Supremum ua pt sr
aproximate-logarithm
 : (α β : Ordinal 𝓤) → 𝟙ₒ ⊴ β -- 𝟙ₒ ⊲ α should be included too, even if it's not technically necessary
 → Σ γ ꞉ Ordinal 𝓤 ,
    γ greatest-satisfying (λ - → (α ^ₒ - ⊴ β) × (- ⊴ β))
aproximate-logarithm {𝓤} α β β-pos = enderton
 where
 open Enderton (α ^ₒ_) 𝟙ₒ β β-pos (^ₒ-satisfies-strong-sup-specification α _)

\end{code}

TODO. The seemingly mild variation

approximate-subtraction'
 : (α β : Ordinal 𝓤) → α ⊴ β
 → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α +ₒ - ⊴ β)))

yields LEM, and similarly for division and logarithm.

\begin{code}

open import MLTT.Plus-Properties
open import UF.ClassicalLogic
open import Ordinals.Exponentiation.Taboos ua pt sr

-- TODO: Upstream
+ₒ-as-large-as-right-summand-implies-EM : ((α β : Ordinal 𝓤) → β ⊴ α +ₒ β)
                                     → EM 𝓤
+ₒ-as-large-as-right-summand-implies-EM hyp P P-is-prop = IV
 where
  α = prop-ordinal P P-is-prop
  β = 𝟙ₒ
  𝕗 : β ⊴ α +ₒ β
  𝕗 = hyp α β
  f = [ β , α +ₒ β ]⟨ 𝕗 ⟩
  I : (p : P) → f ⋆ ＝ inl p → P
  I p _ = p
  II : (p : P) → f ⋆ ＝ inl p
  II p = simulations-preserve-least β (α +ₒ β) ⋆ (inl p) f [ β , α +ₒ β ]⟨ 𝕗 ⟩-is-simulation 𝟙ₒ-least l
   where
    l : is-least (α +ₒ β) (inl p)
    l = minimal-is-least (α +ₒ β) (inl p) m
     where
      m : is-minimal (α +ₒ β) (inl p)
      m (inl p') = 𝟘-elim
      m (inr ⋆ ) = 𝟘-elim
  III : f ⋆ ＝ inr ⋆ → ¬ P
  III e p = +disjoint ((II p) ⁻¹ ∙ e)
  IV : P + ¬ P
  IV = equality-cases (f ⋆) (λ p → inl ∘ I p) (λ _ → inr ∘ III)

EM-implies-+ₒ-as-large-as-right-summand : EM 𝓤
                                        → ((α β : Ordinal 𝓤) → β ⊴ α +ₒ β)
EM-implies-+ₒ-as-large-as-right-summand em α β =
 ≼-gives-⊴ β (α +ₒ β)
           (EM-implies-order-preserving-gives-≼ em β (α +ₒ β) (f , I))
  where
   f : ⟨ β ⟩ → ⟨ α +ₒ β ⟩
   f = inr
   I : is-order-preserving β (α +ₒ β) f
   I y y' l = l
---

approximate-subtraction-variation-implies-EM
 : ((α β : Ordinal 𝓤) → α ⊴ β
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α +ₒ - ⊴ β))))
 → EM 𝓤
approximate-subtraction-variation-implies-EM {𝓤} hyp = +ₒ-as-large-as-right-summand-implies-EM I
 where
  I : (α β : Ordinal 𝓤) → β ⊴ α +ₒ β
  I α β = IV
   where
    II : Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ α +ₒ β) × (γ greatest-satisfying (λ - → α +ₒ - ⊴ α +ₒ β))
    II = hyp α (α +ₒ β) (+ₒ-left-⊴ α β)
    γ = pr₁ II
    III : β ⊴ γ
    III = pr₂ (pr₂ (pr₂ II)) β (⊴-refl (α +ₒ β))
    IV : β ⊴ α +ₒ β
    IV = ⊴-trans β γ (α +ₒ β) III (pr₁ (pr₂ II))

EM-implies-approximate-subtraction-variation
 : EM 𝓤
 → (α β : Ordinal 𝓤) → α ⊴ β
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α +ₒ - ⊴ β)))
EM-implies-approximate-subtraction-variation {𝓤} em α β l = enderton-classical
 where
  open Enderton-classical-variation (α +ₒ_) α β l (+ₒ-preserves-suprema pt sr α) (EM-implies-+ₒ-as-large-as-right-summand em α)

-- TODO: Upstream
+ₒ-minimal : (α β : Ordinal 𝓤) (a₀ : ⟨ α ⟩)
           → is-minimal α a₀ → is-minimal (α +ₒ β) (inl a₀)
+ₒ-minimal α β a₀ a₀-minimal (inl a) = a₀-minimal a
+ₒ-minimal α β a₀ a₀-minimal (inr b) = 𝟘-elim

+ₒ-least : (α β : Ordinal 𝓤) (a₀ : ⟨ α ⟩)
         → is-least α a₀ → is-least (α +ₒ β) (inl a₀)
+ₒ-least α β  a₀ a₀-least =
 minimal-is-least (α +ₒ β) (inl a₀) (+ₒ-minimal α β a₀ (least-is-minimal α a₀ a₀-least))

-- TODO: Upstream
×ₒ-as-large-as-right-factor-implies-EM : ((α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α → β ⊴ α ×ₒ β)
                                     → EM 𝓤
×ₒ-as-large-as-right-factor-implies-EM  hyp P P-is-prop = IV (f (inr ⋆)) refl
 where
  Pₒ = prop-ordinal P P-is-prop
  α = 𝟙ₒ +ₒ Pₒ
  β = 𝟚ₒ
  𝕗 : β ⊴ α ×ₒ β
  𝕗 = hyp α β (inl ⋆ , (𝟙ₒ-↓ ⁻¹ ∙ +ₒ-↓-left ⋆))
  f = [ β , α ×ₒ β ]⟨ 𝕗 ⟩
  I : (p : P) → f (inr ⋆) ＝ (inr p , inl ⋆)
  I p = ↓-lc (α ×ₒ β) (f (inr ⋆)) (inr p , inl ⋆) e
   where
    e = (α ×ₒ β) ↓ f (inr ⋆) ＝⟨ (simulations-preserve-↓ β (α ×ₒ β) 𝕗 (inr ⋆)) ⁻¹ ⟩
        β ↓ inr ⋆ ＝⟨ +ₒ-↓-right ⋆ ⁻¹ ∙ ap (𝟙ₒ +ₒ_) 𝟙ₒ-↓ ∙ 𝟘ₒ-right-neutral 𝟙ₒ ⟩
        𝟙ₒ ＝⟨ (𝟘ₒ-right-neutral 𝟙ₒ) ⁻¹ ∙ ap (𝟙ₒ +ₒ_) ((prop-ordinal-↓ P-is-prop p) ⁻¹) ∙ +ₒ-↓-right p ⟩
        α ↓ inr p ＝⟨ (ap (_+ₒ (α ↓ inr p)) (×ₒ-𝟘ₒ-right α) ∙ 𝟘ₒ-left-neutral (α ↓ inr p)) ⁻¹ ⟩
        α ×ₒ 𝟘ₒ +ₒ (α ↓ inr p) ＝⟨ ap (λ - → α ×ₒ - +ₒ (α ↓ inr p)) (𝟙ₒ-↓ ⁻¹ ∙ +ₒ-↓-left ⋆) ⟩
        α ×ₒ (β ↓ inl ⋆) +ₒ (α ↓ inr p) ＝⟨ ×ₒ-↓ α β ⁻¹ ⟩
        (α ×ₒ β) ↓ (inr p , inl ⋆)      ∎
  II : (x : ⟨ α ⟩) → f (inr ⋆) ＝ (x , inr ⋆) → ¬ P
  II x e p = +disjoint (ap pr₂ ((I p) ⁻¹ ∙ e))
  III : f (inr ⋆) ≠ (inl ⋆ , inl ⋆)
  III h = +disjoint (simulations-are-lc β (α ×ₒ β) f [ β , α ×ₒ β ]⟨ 𝕗 ⟩-is-simulation (e ∙ h ⁻¹))
   where
    e : f (inl ⋆) ＝ (inl ⋆ , inl ⋆)
    e = simulations-preserve-least β (α ×ₒ β) (inl ⋆) (inl ⋆ , inl ⋆) f [ β , α ×ₒ β ]⟨ 𝕗 ⟩-is-simulation β-least (×ₒ-least α β (inl ⋆) (inl ⋆) (+ₒ-least 𝟙ₒ Pₒ ⋆ 𝟙ₒ-least) β-least)
     where
      β-least : is-least β (inl ⋆)
      β-least = +ₒ-least 𝟙ₒ 𝟙ₒ ⋆ 𝟙ₒ-least
  IV : (x : ⟨ α ×ₒ β ⟩) → f (inr ⋆) ＝ x → P + ¬ P
  IV (inl ⋆ , inl ⋆) e = 𝟘-elim (III e)
  IV (inr p , inl ⋆) e = inl p
  IV (inl ⋆ , inr ⋆) e = inr (II (inl ⋆) e)
  IV (inr p , inr ⋆) e = inl p

EM-implies-×ₒ-as-large-as-right-factor
 : EM 𝓤
 → (α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α → β ⊴ α ×ₒ β
EM-implies-×ₒ-as-large-as-right-factor em α β (a₀ , _) =
 ≼-gives-⊴ β (α ×ₒ β)
           (EM-implies-order-preserving-gives-≼ em β (α ×ₒ β) (f , I))
  where
   f : ⟨ β ⟩ → ⟨ α ×ₒ β ⟩
   f b = (a₀ , b)
   I : is-order-preserving β (α ×ₒ β) f
   I b b' l = inl l
---

approximate-division-variation-implies-EM
 : ((α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α ×ₒ - ⊴ β))))
 → EM 𝓤
approximate-division-variation-implies-EM {𝓤} hyp = ×ₒ-as-large-as-right-factor-implies-EM I
 where
  I : (α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α → β ⊴ α ×ₒ β
  I α β α-pos = IV
   where
    II : Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ α ×ₒ β) × (γ greatest-satisfying (λ - → α ×ₒ - ⊴ α ×ₒ β))
    II = hyp α (α ×ₒ β) α-pos
    γ = pr₁ II
    III : β ⊴ γ
    III = pr₂ (pr₂ (pr₂ II)) β (⊴-refl (α ×ₒ β))
    IV : β ⊴ α ×ₒ β
    IV = ⊴-trans β γ (α ×ₒ β) III (pr₁ (pr₂ II))

EM-implies-approximate-division-variation
 : EM 𝓤
 → (α β : Ordinal 𝓤) → 𝟘ₒ ⊲ α
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α ×ₒ - ⊴ β)))
EM-implies-approximate-division-variation em α β α-pos = enderton-classical
 where
  open Enderton-classical-variation' (α ×ₒ_) β (×ₒ-preserves-suprema pt sr α) (λ δ → EM-implies-×ₒ-as-large-as-right-factor em α δ α-pos)

approximate-logarithm-variation-implies-EM
 : ((α β : Ordinal 𝓤) → 𝟙ₒ ⊴ β → 𝟙ₒ ⊲ α
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α ^ₒ - ⊴ β))))
 → EM 𝓤
approximate-logarithm-variation-implies-EM {𝓤} hyp = ^ₒ-as-large-as-exponent-implies-EM I
 where
  I : (α β : Ordinal 𝓤) → 𝟙ₒ ⊲ α → β ⊴ α ^ₒ β
  I α β α-strictly-pos = IV
   where
    II : Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ α ^ₒ β) × (γ greatest-satisfying (λ - → α ^ₒ - ⊴ α ^ₒ β))
    II = hyp α (α ^ₒ β) (^ₒ-has-least-element α β) α-strictly-pos
    γ = pr₁ II
    III : β ⊴ γ
    III = pr₂ (pr₂ (pr₂ II)) β (⊴-refl (α ^ₒ β))
    IV : β ⊴ α ^ₒ β
    IV = ⊴-trans β γ (α ^ₒ β) III (pr₁ (pr₂ II))

EM-implies-approximate-logarithm-variation
 : EM 𝓤
 → (α β : Ordinal 𝓤) → 𝟙ₒ ⊴ β → 𝟙ₒ ⊲ α
   → Σ γ ꞉ Ordinal 𝓤 , (γ ⊴ β) × (γ greatest-satisfying (λ - → (α ^ₒ - ⊴ β)))
EM-implies-approximate-logarithm-variation em α β β-pos α-strictly-pos = enderton-classical
  where
   open Enderton-classical-variation (α ^ₒ_) 𝟙ₒ β β-pos (^ₒ-satisfies-strong-sup-specification α _) (λ δ → EM-implies-^ₒ-as-large-as-exponent em α δ α-strictly-pos)

\end{code}
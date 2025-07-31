Tom de Jong, 31 July 2025.
In collaboration with Nicolai Kraus, Fredrik Nordvall Forsberg and Chuangjie Xu.

We formalize cancel-exp.pdf [TODO. Write a proper description.]

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.ArithmeticReflection
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import MLTT.Plus-Properties
open import MLTT.Spartan hiding (J)
open import UF.Base
open import UF.ClassicalLogic
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import Ordinals.AdditionProperties ua
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Exponentiation.Supremum ua pt sr
open import Ordinals.Exponentiation.Taboos ua pt sr
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.MultiplicationProperties ua
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Propositions ua
open import Ordinals.Type
open import Ordinals.Underlying

open PropositionalTruncation pt
open suprema pt sr

-- This should be moved elsewhere eventually

is-⊴-reflecting : (Ordinal 𝓤 → Ordinal 𝓥) → 𝓤 ⁺ ⊔ 𝓥 ̇
is-⊴-reflecting {𝓤} {𝓥} f = (α β : Ordinal 𝓤) → f α ⊴ f β → α ⊴ β

⊴-gives-not-⊲ : (α β : Ordinal 𝓤) → α ⊴ β → ¬ (β ⊲ α)
⊴-gives-not-⊲ α β (f , f-sim) =
 order-preserving-gives-not-⊲ α β
  (f , simulations-are-order-preserving α β f f-sim)

_≤ᶜˡ_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α ≤ᶜˡ β = Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-order-preserving α β f

_<ᶜˡ_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥 ̇
α <ᶜˡ β = Σ (f , _) ꞉ α ≤ᶜˡ β , Σ b₀ ꞉ ⟨ β ⟩ , ((a : ⟨ α ⟩) → f a ≺⟨ β ⟩ b₀)

-- Lemma 2
module _ (α : Ordinal 𝓤) (β : Ordinal 𝓥) where

 ⊴-gives-≤ᶜˡ : α ⊴ β → α ≤ᶜˡ β
 ⊴-gives-≤ᶜˡ (f , f-sim) = f , (simulations-are-order-preserving α β f f-sim)

 ≤ᶜˡ-transitivity : (γ : Ordinal 𝓦) → α ≤ᶜˡ β → β ≤ᶜˡ γ → α ≤ᶜˡ γ
 ≤ᶜˡ-transitivity γ (f , f-order-pres) (g , g-order-pres) =
  g ∘ f , (λ a a' l → g-order-pres (f a) (f a') (f-order-pres a a' l))

 <ᶜˡ-≤ᶜˡ-to-<ᶜˡ : (γ : Ordinal 𝓦) → α <ᶜˡ β → β ≤ᶜˡ γ → α <ᶜˡ γ
 <ᶜˡ-≤ᶜˡ-to-<ᶜˡ γ (𝕗@(f , _) , b₀ , f-below-b₀) 𝕘@(g , g-order-pres) =
  ≤ᶜˡ-transitivity γ 𝕗 𝕘 , g b₀ , (λ a → g-order-pres (f a) b₀ (f-below-b₀ a))

 ≤ᶜˡ-<ᶜˡ-to-<ᶜˡ : (γ : Ordinal 𝓦) → α ≤ᶜˡ β → β <ᶜˡ γ → α <ᶜˡ γ
 ≤ᶜˡ-<ᶜˡ-to-<ᶜˡ γ 𝕗@(f , _) (𝕘@(g , _) , c₀ , g-below-c₀) =
  ≤ᶜˡ-transitivity γ 𝕗 𝕘 , c₀ , (λ a → g-below-c₀ (f a))

⊲-gives-<ᶜˡ : (α β : Ordinal 𝓤) → α ⊲ β → α <ᶜˡ β
⊲-gives-<ᶜˡ α β (b₀ , refl) =
 ⊴-gives-≤ᶜˡ (β ↓ b₀) β (segment-⊴ β b₀) , b₀ , segment-inclusion-bound β b₀

-- Lemma 3(2)
⊲-gives-not-≤ᶜˡ : (α β : Ordinal 𝓤) → α ⊲ β → ¬ (β ≤ᶜˡ α)
⊲-gives-not-≤ᶜˡ α β α-strictly-below-β β-below-α =
 order-preserving-gives-not-⊲ β α β-below-α α-strictly-below-β

-- Lemma 4
<ᶜˡ-irrefl : (α : Ordinal 𝓤) → ¬ (α <ᶜˡ α)
<ᶜˡ-irrefl α ((f , f-order-pres) , a₀ , f-below-a₀) =
 ⊲-gives-not-≤ᶜˡ (α ↓ a₀) α (a₀ , refl) I
  where
   I : α ≤ᶜˡ (α ↓ a₀)
   I = (λ a → f a , f-below-a₀ a) , f-order-pres

-- Lemma 3(1)
⊴-gives-not-<ᶜˡ : (α : Ordinal 𝓤) (β : Ordinal 𝓥) → α ⊴ β → ¬ (β <ᶜˡ α)
⊴-gives-not-<ᶜˡ α β 𝕗 𝕘 =
 <ᶜˡ-irrefl β (<ᶜˡ-≤ᶜˡ-to-<ᶜˡ β α β 𝕘 (⊴-gives-≤ᶜˡ α β 𝕗))

-- Lemma 11
module uo-order
        (A : 𝓤 ̇ ) (_≺_ : A → A → 𝓥 ̇ )
       where

 _≺ᵤₒ_ : A × A → A × A → 𝓥 ̇
 (a₁ , b₁) ≺ᵤₒ (a₂ , b₂) = ((a₁ ≺ a₂) × (b₁ ≺ b₂)) + (a₁ ≺ b₂) × (b₁ ≺ a₂)

 ≺ᵤₒ-is-well-founded : is-well-founded _≺_ → is-well-founded _≺ᵤₒ_
 ≺ᵤₒ-is-well-founded wf = (λ (a , b) → pr₁ (II a b))
  where
   P : A → A → 𝓤 ⊔ 𝓥 ̇
   P a b = is-accessible _≺ᵤₒ_ (a , b) × is-accessible _≺ᵤₒ_ (b , a)
   I : (a : A)
     → ((a' : A) → a' ≺ a → (b : A) → P a' b)
     → (b : A) → P a b
   I a IH = transfinite-induction _≺_ wf (P a) h
    where
     h : (b : A) → ((b' : A) → b' ≺ b → P a b') → P a b
     h b IH' = acc h₁ , acc h₂
      where
       h₁ : (x : A × A) → x ≺ᵤₒ (a , b) → is-accessible _≺ᵤₒ_ x
       h₁ (a' , b') (inl (l₁ , l₂)) = pr₁ (IH a' l₁ b')
       h₁ (a' , b') (inr (l₁ , l₂)) = pr₂ (IH b' l₂ a')
       h₂ : (x : A × A) → x ≺ᵤₒ (b , a) → is-accessible _≺ᵤₒ_ x
       h₂ (a' , b') (inl (l₁ , l₂)) = pr₂ (IH b' l₂ a')
       h₂ (a' , b') (inr (l₁ , l₂)) = pr₁ (IH a' l₁ b')
   II : (a b : A) → P a b
   II = transfinite-induction _≺_ wf (λ a → (b : A) → P a b) I


extended-sup : {I : 𝓤 ̇ } (J : I → Ordinal 𝓤) (Z : Ordinal 𝓤) → Ordinal 𝓤
extended-sup {𝓤} J Z = sup (cases (λ (_ : 𝟙{𝓤}) → Z) J)

private
 module framework
         (F : Ordinal 𝓤 → Ordinal 𝓤)
         (S : Ordinal 𝓤 → Ordinal 𝓤)
         (Z : Ordinal 𝓤)
         (F-succ : (β : Ordinal 𝓤) → F (β +ₒ 𝟙ₒ) ＝ S (F β))
         (F-sup : (I : 𝓤 ̇ ) (J : I → Ordinal 𝓤)
                → F (sup J) ＝ extended-sup (F ∘ J) Z)
        where

  Assumption-1 : 𝓤 ⁺ ̇
  Assumption-1 =
   Σ H ꞉ (Ordinal 𝓤 → Ordinal 𝓤) , ((β : Ordinal 𝓤) → S β ＝ β +ₒ H β)

  Assumption-2 : 𝓤 ⁺ ̇
  Assumption-2 = Σ (H , _) ꞉ Assumption-1 , ((β : Ordinal 𝓤) → 𝟘ₒ ⊲ H (F β))

  Assumption-3 : 𝓤 ⁺ ̇
  Assumption-3 = (β γ : Ordinal 𝓤) → β ≤ᶜˡ γ → S β ≤ᶜˡ S γ

-- See below for examples (cf. BoundedOperations.lagda).

  -- Lemma 7
  F-preserves-⊴ : (β γ : Ordinal 𝓤) → β ⊴ γ → F β ⊴ F γ
  F-preserves-⊴ β γ l = III
   where
    J : 𝟙{𝓤} + 𝟙{𝓤} → Ordinal 𝓤
    J = cases (λ _ → β) (λ _ → γ)
    I : sup J ＝ γ
    I = ⊴-antisym (sup J) γ
         (sup-is-lower-bound-of-upper-bounds J γ
           (dep-cases (λ _ → l) (λ _ → ⊴-refl γ)))
         (sup-is-upper-bound J (inr ⋆))
    II : F β ⊴ extended-sup (F ∘ J) Z
    II = sup-is-upper-bound _ (inr (inl ⋆))
    III : F β ⊴ F γ
    III = transport⁻¹ (F β ⊴_) (ap F (I ⁻¹) ∙ F-sup (𝟙 + 𝟙) J) II

  -- Remark 7
  F-eq : (β : Ordinal 𝓤)
       → F β ＝ extended-sup (λ (b : ⟨ β ⟩) → S (F (β ↓ b))) Z
  F-eq β = F β ＝⟨ ap F (supremum-of-successors-of-initial-segments pt sr β) ⟩
           F (sup λ b → (β ↓ b) +ₒ 𝟙ₒ) ＝⟨ F-sup ⟨ β ⟩ (λ b → (β ↓ b) +ₒ 𝟙ₒ) ⟩
           extended-sup (F ∘ (λ b → (β ↓ b) +ₒ 𝟙ₒ)) Z ＝⟨ ap (λ - → extended-sup - Z) (dfunext fe' (λ b → F-succ (β ↓ b))) ⟩
           extended-sup (λ b → S (F (β ↓ b))) Z ∎

  Z-is-F𝟘ₒ : Z ＝ F 𝟘ₒ
  Z-is-F𝟘ₒ = Z ＝⟨ I ⟩
             extended-sup (F ∘ J) Z ＝⟨ F-sup 𝟘 J ⁻¹ ⟩
             F (sup J) ＝⟨ ap F II ⟩
             F 𝟘ₒ ∎
   where
    J : 𝟘 → Ordinal 𝓤
    J = 𝟘-elim
    I = ⊴-antisym Z (extended-sup (F ∘ J) Z)
         (sup-is-upper-bound _ (inl ⋆))
         (sup-is-lower-bound-of-upper-bounds _ Z
           (dep-cases (λ _ → ⊴-refl Z) 𝟘-induction))
    II : sup J ＝ 𝟘ₒ
    II = ⊴-antisym (sup J) 𝟘ₒ
          (sup-is-lower-bound-of-upper-bounds J 𝟘ₒ 𝟘-induction)
          (𝟘ₒ-least-⊴ (sup J))

  Z-below-all-values-of-F : (β : Ordinal 𝓤) → Z ⊴ F β
  Z-below-all-values-of-F β =
   transport⁻¹ (_⊴ F β) Z-is-F𝟘ₒ (F-preserves-⊴ 𝟘ₒ β (𝟘ₒ-least-⊴ β))

  -- Lemma 8
  F-preserves-⊲ : Assumption-2
                → (β γ : Ordinal 𝓤) → β ⊲ γ → F β ⊲ F γ
  F-preserves-⊲ ((H , S-H-eq) , H-has-min) β γ (c₀ , refl) = III
   where
    h₀ : ⟨ H (F (γ ↓ c₀)) ⟩
    h₀ = pr₁ (H-has-min (γ ↓ c₀))
    h₀-eq : H (F (γ ↓ c₀)) ↓ h₀ ＝ 𝟘ₒ
    h₀-eq = (pr₂ (H-has-min (γ ↓ c₀))) ⁻¹
    J : ⟨ γ ⟩ → Ordinal 𝓤
    J c = F (γ ↓ c) +ₒ H (F (γ ↓ c))
    [_,_] : (c : ⟨ γ ⟩) (h : ⟨ H (F (γ ↓ c)) ⟩) → ⟨ sup J ⟩
    [ c , h ] =
     [ F (γ ↓ c) +ₒ H (F (γ ↓ c)) , sup J ]⟨ sup-is-upper-bound J c ⟩ (inr h)

    I : sup J ↓ [ c₀ , h₀ ] ＝ F (γ ↓ c₀)
    I = sup J ↓ [ c₀ , h₀ ] ＝⟨ initial-segment-of-sup-at-component J c₀ (inr h₀) ⟩
        J c₀ ↓ inr h₀ ＝⟨ (+ₒ-↓-right h₀) ⁻¹ ⟩
        F (γ ↓ c₀) +ₒ (H (F (γ ↓ c₀)) ↓ h₀) ＝⟨ ap (F (γ ↓ c₀) +ₒ_) h₀-eq ⟩
        F (γ ↓ c₀) +ₒ 𝟘ₒ ＝⟨ 𝟘ₒ-right-neutral (F (γ ↓ c₀)) ⟩
        F (γ ↓ c₀) ∎

    II : sup J ＝ F γ
    II = sup J ＝⟨ II₁ ⟩
         extended-sup J Z ＝⟨ refl ⟩
         extended-sup (λ c → F (γ ↓ c) +ₒ H (F (γ ↓ c))) Z ＝⟨ II₂ ⟩
         extended-sup (λ c → S (F (γ ↓ c))) Z ＝⟨ (F-eq γ ⁻¹) ⟩
         F γ ∎
      where
       II₁ = ⊴-antisym (sup J) (extended-sup J Z)
              (sup-composition-⊴ inr (cases (λ _ → Z) J))
              (sup-is-lower-bound-of-upper-bounds (cases (λ _ → Z) J) (sup J) ub)
        where
         ub : (i : 𝟙 + ⟨ γ ⟩) → cases (λ _ → Z) J i ⊴ sup J
         ub (inl ⋆) = ⊴-trans Z (F (γ ↓ c₀)) (sup J)
                       (Z-below-all-values-of-F (γ ↓ c₀))
                       (⊴-trans (F (γ ↓ c₀)) (J c₀) (sup J)
                         (+ₒ-left-⊴ (F (γ ↓ c₀)) (H (F (γ ↓ c₀))))
                         (sup-is-upper-bound J c₀))
         ub (inr c) = sup-is-upper-bound J c
       II₂ = ap (λ - → extended-sup - Z) (dfunext fe' (λ c → (S-H-eq (F (γ ↓ c))) ⁻¹))

    III : F (γ ↓ c₀) ⊲ F γ
    III = _ , (I ⁻¹ ∙ Idtofunₒ-↓-lemma II)

  -- Lemma 9
  -- This ought to be cleaned up.
  F-tightening-bounds
   : Assumption-1
   → (β : Ordinal 𝓤)
   → F 𝟘ₒ ⊴ β
   → (γ : Ordinal 𝓤)
   → β ⊲ F γ
   → ∃ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ γ) × (F γ' ⊴ β) × (β ⊲ F (γ' +ₒ 𝟙ₒ))
  F-tightening-bounds (H , H-S-eq) β β-ineq = transfinite-induction-on-OO _ I
   where
    I : (γ : Ordinal 𝓤)
      → ((c : ⟨ γ ⟩)
            → β ⊲ F (γ ↓ c)
            → ∃ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ γ ↓ c)
                               × (F γ' ⊴ β)
                               × (β ⊲ F (γ' +ₒ 𝟙ₒ)))
      → β ⊲ F γ
      → ∃ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ γ) × (F γ' ⊴ β) × (β ⊲ F (γ' +ₒ 𝟙ₒ))
    I γ IH (x' , refl) =
     ∥∥-rec ∃-is-prop IV
       (initial-segment-of-sup-is-initial-segment-of-some-component _ x)
      where
       II : F γ ＝ extended-sup (λ c → S (F (γ ↓ c))) Z
       II = F-eq γ

       x = Idtofunₒ (F-eq γ) x'
       III : β ＝ (extended-sup (λ c → S (F (γ ↓ c))) Z) ↓ x
       III = Idtofunₒ-↓-lemma II

       IV : (Σ i ꞉ 𝟙 + ⟨ γ ⟩ ,
             Σ y ꞉ ⟨ cases (λ _ → Z) (λ c → S (F (γ ↓ c))) i ⟩ ,
              sup (cases (λ _ → Z) (λ c → S (F (γ ↓ c)))) ↓ x
              ＝ cases (λ _ → Z) (λ c → S (F (γ ↓ c))) i ↓ y)
          → ∃ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ γ) × (F γ' ⊴ β) × (β ⊲ F (γ' +ₒ 𝟙ₒ))
       IV (inl ⋆ , y , p) = 𝟘-elim (⊴-gives-not-⊲ (F 𝟘ₒ) β β-ineq l')
        where
         l : β ⊲ Z
         l = y , (III ∙ p)
         l' : β ⊲ F 𝟘ₒ
         l' = transport (β ⊲_) Z-is-F𝟘ₒ l
       IV (inr c , y , p) = V y' (p' ∙ Idtofunₒ-↓-lemma (H-S-eq (F (γ ↓ c))))
        where
         p' : β ＝ S (F (γ ↓ c)) ↓ y
         p' = III ∙ p
         y' : ⟨ F (γ ↓ c) +ₒ H (F (γ ↓ c)) ⟩
         y' = Idtofunₒ (H-S-eq (F (γ ↓ c))) y

         V : (y' : ⟨ F (γ ↓ c) +ₒ H (F (γ ↓ c)) ⟩)
           → β ＝ (F (γ ↓ c) +ₒ H (F (γ ↓ c))) ↓ y'
           → ∃ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ γ) × (F γ' ⊴ β) × (β ⊲ F (γ' +ₒ 𝟙ₒ))
         V (inl z) q = ∥∥-functor V' ih
          where
           ih : ∃ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ (γ ↓ c)) × (F γ' ⊴ β) × (β ⊲ F (γ' +ₒ 𝟙ₒ))
           ih = IH c (z , (q ∙ (+ₒ-↓-left z) ⁻¹))
           V' : (Σ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ (γ ↓ c)) × (F γ' ⊴ β) × (β ⊲ F (γ' +ₒ 𝟙ₒ)))
              → (Σ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ γ) × (F γ' ⊴ β) × (β ⊲ F (γ' +ₒ 𝟙ₒ)))
           V' (γ' , k , l , m) =
            γ' , ⊲-⊴-gives-⊲ γ' (γ ↓ c) γ k (segment-⊴ γ c) , l , m
         V (inr z) q = ∣ γ ↓ c , (c , refl) , V₁ , V₂ ∣
          where
           e : β ＝ F (γ ↓ c) +ₒ (H (F (γ ↓ c)) ↓ z)
           e = q ∙ (+ₒ-↓-right z) ⁻¹
           V₁ : F (γ ↓ c) ⊴ β
           V₁ = transport⁻¹ (F (γ ↓ c) ⊴_) e
                            (+ₒ-left-⊴ (F (γ ↓ c)) (H (F (γ ↓ c)) ↓ z))
           V₂ : β ⊲ F ((γ ↓ c) +ₒ 𝟙ₒ)
           V₂ = Idtofunₒ ((F-succ (γ ↓ c)) ⁻¹) y ,
                (III ∙ p ∙ Idtofunₒ-↓-lemma ((F-succ (γ ↓ c)) ⁻¹))

  -- Lemma 10
  F-impossibility : Assumption-1
                  → Assumption-3
                  → (β γ δ : Ordinal 𝓤) (b : ⟨ β ⟩)
                  → F γ ⊴ F (β ↓ b)
                  → F β ⊴ F γ +ₒ δ
                  → F γ +ₒ δ ⊲ F (γ +ₒ 𝟙ₒ)
                  → 𝟘
  F-impossibility ams-1 asm-3 β γ δ b l₁ l₂ l₃ =
   <ᶜˡ-irrefl (S (F γ)) IV
    where
     I : S (F γ) ≤ᶜˡ S (F (β ↓ b))
     I = asm-3 (F γ) (F (β ↓ b)) (⊴-gives-≤ᶜˡ (F γ) (F (β ↓ b)) l₁)

     II : S (F γ) ≤ᶜˡ F ((β ↓ b) +ₒ 𝟙ₒ)
     II = transport⁻¹ (S (F γ) ≤ᶜˡ_) (F-succ (β ↓ b)) I

     III : F ((β ↓ b) +ₒ 𝟙ₒ) ≤ᶜˡ (F γ +ₒ δ)
     III = ≤ᶜˡ-transitivity (F ((β ↓ b) +ₒ 𝟙ₒ)) (F β) (F γ +ₒ δ)
            (⊴-gives-≤ᶜˡ (F ((β ↓ b) +ₒ 𝟙ₒ)) (F β)
              (F-preserves-⊴ ((β ↓ b) +ₒ 𝟙ₒ) β
                (upper-bound-of-successors-of-initial-segments β b)))
            (⊴-gives-≤ᶜˡ (F β) (F γ +ₒ δ) l₂)

     IV₁ : S (F γ) ≤ᶜˡ (F γ +ₒ δ)
     IV₁ = ≤ᶜˡ-transitivity (S (F γ)) (F ((β ↓ b) +ₒ 𝟙ₒ)) (F γ +ₒ δ) II III

     IV₂ : (F γ +ₒ δ) <ᶜˡ S (F γ)
     IV₂ = transport ((F γ +ₒ δ) <ᶜˡ_) (F-succ γ)
                     (⊲-gives-<ᶜˡ (F γ +ₒ δ) (F (γ +ₒ 𝟙ₒ)) l₃)

     IV : S (F γ) <ᶜˡ S (F γ)
     IV = ≤ᶜˡ-<ᶜˡ-to-<ᶜˡ (S (F γ)) (F γ +ₒ δ) (S (F γ)) IV₁ IV₂

  -- Lemma 12
  F-reflects-⊴' : -- Assumption-1 -- redundant in the presence of Assumption-2
                  Assumption-2
                → Assumption-3
                → (β γ δ : Ordinal 𝓤)
                → F β ⊴ F γ +ₒ δ
                → F γ +ₒ δ ⊲ F (γ +ₒ 𝟙ₒ)
                → β ⊴ γ
  F-reflects-⊴' asm-2@((H , H-S-eq) , H-has-min) asm-3 = (λ β γ → I (β , γ))
   where
    open uo-order (Ordinal 𝓤) _⊲_
    P : Ordinal 𝓤 × Ordinal 𝓤 → 𝓤 ⁺ ̇
    P (β , γ) =
     (δ : Ordinal 𝓤) → F β ⊴ F γ +ₒ δ → F γ +ₒ δ ⊲ F (γ +ₒ 𝟙ₒ) → β ⊴ γ

    II : (X : Ordinal 𝓤 × Ordinal 𝓤)
       → ((Y : Ordinal 𝓤 × Ordinal 𝓤) → Y ≺ᵤₒ X → P Y)
       → P X
    II (β , γ) IH δ l₁ l₂ = to-⊴ β γ goal
     where
      module _ (b : ⟨ β ⟩) where
       III₁ : F 𝟘ₒ ⊴ F (β ↓ b)
       III₁ = F-preserves-⊴ 𝟘ₒ (β ↓ b) (𝟘ₒ-least-⊴ (β ↓ b))
       III₂ : F (β ↓ b) ⊲ F (γ +ₒ 𝟙ₒ)
       III₂ = ⊲-⊴-gives-⊲ (F (β ↓ b)) (F β) (F (γ +ₒ 𝟙ₒ))
               (F-preserves-⊲ asm-2 (β ↓ b) β (b , refl))
               (⊴-trans (F β) (F γ +ₒ δ) (F (γ +ₒ 𝟙ₒ))
                 l₁
                 (⊲-gives-⊴ (F γ +ₒ δ) (F (γ +ₒ 𝟙ₒ)) l₂))
       III₃ : ∃ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ γ +ₒ 𝟙ₒ)
                               × (F γ' ⊴ F (β ↓ b))
                               × (F (β ↓ b) ⊲ F (γ' +ₒ 𝟙ₒ))
       III₃ = F-tightening-bounds (H , H-S-eq) (F (β ↓ b)) III₁ (γ +ₒ 𝟙ₒ) III₂

       IV₁ : F ((γ +ₒ 𝟙ₒ) ↓ inr ⋆) ⊴ F (β ↓ b) → 𝟘
       IV₁ l = F-impossibility (H , H-S-eq) asm-3 β γ δ b k l₁ l₂
        where
         k : F γ ⊴ F (β ↓ b)
         k = transport⁻¹ (_⊴ F (β ↓ b)) (ap F ((successor-lemma-right γ) ⁻¹)) l

       IV₂ : (c : ⟨ γ ⟩)
           → F (γ ↓ c) ⊴ F (β ↓ b)
           → F (β ↓ b) ⊲ F ((γ ↓ c) +ₒ 𝟙ₒ)
           → β ↓ b ＝ γ ↓ c
       IV₂ c k₁ k₂ = ⊴-antisym (β ↓ b) (γ ↓ c) VI V
        where
         V : γ ↓ c ⊴ β ↓ b
         V = IH (γ ↓ c , β ↓ b) (inr ((c , refl) , (b , refl))) 𝟘ₒ
              (transport⁻¹ (F (γ ↓ c) ⊴_) (𝟘ₒ-right-neutral (F (β ↓ b))) k₁)
              (transport⁻¹ (_⊲ F ((β ↓ b) +ₒ 𝟙ₒ)) (𝟘ₒ-right-neutral (F (β ↓ b)))
                (F-preserves-⊲ asm-2 (β ↓ b) ((β ↓ b) +ₒ 𝟙ₒ) (successor-increasing (β ↓ b))))

         VI : β ↓ b ⊴ γ ↓ c
         VI = VI₂ z z-eq
          where
           VI₁ : F ((γ ↓ c) +ₒ 𝟙ₒ) ＝ F (γ ↓ c) +ₒ H (F (γ ↓ c))
           VI₁ = F-succ (γ ↓ c) ∙ H-S-eq (F (γ ↓ c))
           z : ⟨ F (γ ↓ c) +ₒ H (F (γ ↓ c)) ⟩
           z = Idtofunₒ VI₁ (pr₁ k₂)
           z-eq : F (β ↓ b) ＝ (F (γ ↓ c) +ₒ H (F (γ ↓ c))) ↓ z
           z-eq = pr₂ k₂ ∙ Idtofunₒ-↓-lemma VI₁
           VI₂ : (z : ⟨ F (γ ↓ c) +ₒ H (F (γ ↓ c)) ⟩)
               → F (β ↓ b) ＝ (F (γ ↓ c) +ₒ H (F (γ ↓ c))) ↓ z
               → β ↓ b ⊴ γ ↓ c
           VI₂ (inl z₀) z-eq =
            𝟘-elim (⊴-gives-not-⊲ (F (γ ↓ c)) (F (β ↓ b))
                     k₁
                     (z₀ , (z-eq ∙ (+ₒ-↓-left z₀) ⁻¹)))
           VI₂ (inr z₀) z-eq =
            IH (β ↓ b , γ ↓ c)
               (inl ((b , refl) , (c , refl)))
               δ' m₁ m₂
             where
              δ' = H (F (γ ↓ c)) ↓ z₀
              m₁ : F (β ↓ b) ⊴ F (γ ↓ c) +ₒ δ'
              m₁ = ＝-to-⊴ (F (β ↓ b)) (F (γ ↓ c) +ₒ δ') (z-eq ∙ (+ₒ-↓-right z₀) ⁻¹)
              m₂ : F (γ ↓ c) +ₒ δ' ⊲ F ((γ ↓ c) +ₒ 𝟙ₒ)
              m₂ = transport⁻¹ (_⊲ F ((γ ↓ c) +ₒ 𝟙ₒ)) (+ₒ-↓-right z₀ ∙ z-eq ⁻¹) k₂

       goal : β ↓ b ⊲ γ
       goal = ∥∥-rec (⊲-is-prop-valued (β ↓ b) γ) g III₃
        where
         g : (Σ γ' ꞉ Ordinal 𝓤 , (γ' ⊲ γ +ₒ 𝟙ₒ)
                               × (F γ' ⊴ F (β ↓ b))
                               × (F (β ↓ b) ⊲ F (γ' +ₒ 𝟙ₒ)))
           → β ↓ b ⊲ γ
         g (γ' , (inl c , refl) , k₁ , k₂) = c , (IV₂ c k₁' k₂')
          where
           k₁' : F (γ ↓ c) ⊴ F (β ↓ b)
           k₁' = transport⁻¹ (_⊴ F (β ↓ b)) (ap F (+ₒ-↓-left c)) k₁
           k₂' : F (β ↓ b) ⊲ F ((γ ↓ c) +ₒ 𝟙ₒ)
           k₂' = transport⁻¹ (F (β ↓ b) ⊲_) (ap F (ap (_+ₒ 𝟙ₒ) (+ₒ-↓-left c))) k₂
         g (γ' , (inr ⋆ , refl) , k₁ , k₂) = 𝟘-elim (IV₁ k₁)

    I : Π P
    I = transfinite-induction _≺ᵤₒ_ (≺ᵤₒ-is-well-founded ⊲-is-well-founded) P II

  module framework-with-assumptions
          (asm-2 : Assumption-2)
          (asm-3 : Assumption-3)
         where

   F-reflects-⊴ : (β γ : Ordinal 𝓤) → F β ⊴ F γ → β ⊴ γ
   F-reflects-⊴ β γ l =
    F-reflects-⊴' asm-2 asm-3 β γ 𝟘ₒ
     (transport⁻¹ (F β ⊴_) (𝟘ₒ-right-neutral (F γ)) l)
     (transport⁻¹
       (_⊲ F (γ +ₒ 𝟙ₒ))
       (𝟘ₒ-right-neutral (F γ))
       (F-preserves-⊲ asm-2 γ (γ +ₒ 𝟙ₒ) (successor-increasing γ)))

   -- Corollary 13
   F-left-cancellable : left-cancellable F
   F-left-cancellable p =
    ⊴-antisym _ _ (F-reflects-⊴ _ _ (＝-to-⊴ _ _ p))
                  (F-reflects-⊴ _ _ (＝-to-⊴ _ _ (p ⁻¹)))

-- Corollary 14

module _ (α : Ordinal 𝓤) where
 private
  open framework
        (α +ₒ_)
        (_+ₒ 𝟙ₒ)
        α
        (+ₒ-commutes-with-successor α)
        (+ₒ-preserves-suprema-up-to-join pt sr α)

  asm-2 : Σ (H , _) ꞉ (Σ H ꞉ (Ordinal 𝓤 → Ordinal 𝓤)
              , ((β : Ordinal 𝓤) → β +ₒ 𝟙ₒ ＝ β +ₒ H β))
              , ((β : Ordinal 𝓤) → 𝟘ₒ ⊲ H (α +ₒ β))
  asm-2 = ((λ β → 𝟙ₒ) , (λ β → refl)) , (λ β → ⋆ , (𝟙ₒ-↓ ⁻¹))

  asm-3 : (β γ : Ordinal 𝓤) → β ≤ᶜˡ γ → (β +ₒ 𝟙ₒ) ≤ᶜˡ (γ +ₒ 𝟙ₒ)
  asm-3 β γ (f , f-order-pres) = g , g-order-pres
   where
    g : ⟨ β +ₒ 𝟙ₒ ⟩ → ⟨ γ +ₒ 𝟙ₒ ⟩
    g (inl b) = inl (f b)
    g (inr ⋆) = inr ⋆
    g-order-pres : is-order-preserving (β +ₒ 𝟙ₒ) (γ +ₒ 𝟙ₒ) g
    g-order-pres (inl b) (inl b') l = f-order-pres b b' l
    g-order-pres (inl b) (inr ⋆)  l = ⋆
    g-order-pres (inr ⋆) (inl b)  l = l
    g-order-pres (inr ⋆) (inr ⋆)  l = l

  open framework-with-assumptions asm-2 asm-3

 +ₒ-reflects-⊴ : is-⊴-reflecting (α +ₒ_)
 +ₒ-reflects-⊴ = F-reflects-⊴

 +ₒ-left-cancellable' : left-cancellable (α +ₒ_)
 +ₒ-left-cancellable' = F-left-cancellable


-- TODO. Improve the dependencies
-- I do this to reuse Enderton-like'.preservation-of-suprema-up-to-join
open import Ordinals.BoundedOperations ua pt sr

module _ (α : Ordinal 𝓤) where
 private
  open framework
        (α ×ₒ_)
        (_+ₒ α)
        𝟘ₒ
        (×ₒ-successor α)
        (Enderton-like'.preservation-of-suprema-up-to-join (α ×ₒ_) 𝟘ₒ (×ₒ-preserves-suprema pt sr α))

  asm-2 : 𝟘ₒ ⊲ α
        → Σ (H , _) ꞉ (Σ H ꞉ (Ordinal 𝓤 → Ordinal 𝓤)
              , ((β : Ordinal 𝓤) → β +ₒ α ＝ β +ₒ H β))
              , ((β : Ordinal 𝓤) → 𝟘ₒ ⊲ H (α ×ₒ β))
  asm-2 α-pos =
   ((λ β → α) , (λ β → refl)) , (λ β → α-pos)

  asm-3 : (β γ : Ordinal 𝓤) → β ≤ᶜˡ γ → (β +ₒ α) ≤ᶜˡ (γ +ₒ α)
  asm-3 β γ (f , f-order-pres) = +functor f id , h
   where
    h : is-order-preserving (β +ₒ α) (γ +ₒ α) (+functor f id)
    h (inl b) (inl b') l = f-order-pres b b' l
    h (inl b) (inr a) l = ⋆
    h (inr a) (inl b) l = l
    h (inr a) (inr a') l = l

  module fwa (α-pos : 𝟘ₒ ⊲ α) where
   open framework-with-assumptions (asm-2 α-pos) asm-3 public

 ×ₒ-reflects-⊴ : 𝟘ₒ ⊲ α → is-⊴-reflecting (α ×ₒ_)
 ×ₒ-reflects-⊴ = fwa.F-reflects-⊴

 ×ₒ-left-cancellable' : 𝟘ₒ ⊲ α → left-cancellable (α ×ₒ_)
 ×ₒ-left-cancellable' = fwa.F-left-cancellable


open import Ordinals.Exponentiation.TrichotomousLeastElement ua pt

module _ (α : Ordinal 𝓤) (α-has-least : 𝟙ₒ ⊴ α) where
 private
  open framework
        (α ^ₒ_)
        (_×ₒ α)
        𝟙ₒ
        (^ₒ-satisfies-succ-specification α α-has-least)
        (^ₒ-satisfies-strong-sup-specification α)

  asm-2 : has-trichotomous-least-element α
        →  Σ (H , _) ꞉ (Σ H ꞉ (Ordinal 𝓤 → Ordinal 𝓤)
              , ((β : Ordinal 𝓤) → β ×ₒ α ＝ β +ₒ H β))
              , ((β : Ordinal 𝓤) → 𝟘ₒ ⊲ H (α ^ₒ β))
  asm-2 h = (H , e) , H-has-min
   where
    e : (β : Ordinal 𝓤) → β ×ₒ α ＝ β +ₒ (β ×ₒ α ⁺[ h ])
    e β = β ×ₒ α ＝⟨ ap (β ×ₒ_) (α ⁺[ h ]-part-of-decomposition) ⟩
          β ×ₒ (𝟙ₒ +ₒ α ⁺[ h ]) ＝⟨ ×ₒ-distributes-+ₒ-right β 𝟙ₒ (α ⁺[ h ]) ⟩
          β ×ₒ 𝟙ₒ +ₒ β ×ₒ (α ⁺[ h ]) ＝⟨ ap (_+ₒ β ×ₒ (α ⁺[ h ])) (𝟙ₒ-right-neutral-×ₒ β) ⟩
          β +ₒ β ×ₒ (α ⁺[ h ]) ∎
    H : Ordinal 𝓤 → Ordinal 𝓤
    H β = β ×ₒ (α ⁺[ h ])
    H-has-min' : (γ : Ordinal 𝓤) → 𝟙ₒ ⊴ γ → 𝟙ₒ ⊴ H γ
    H-has-min' γ l = {!!}
    H-has-min : (β : Ordinal 𝓤) → 𝟘ₒ ⊲ H (α ^ₒ β)
    H-has-min β = ({!!} , {!!}) , {!!}


  asm-3 : (β γ : Ordinal 𝓤) → β ≤ᶜˡ γ → (β ×ₒ α) ≤ᶜˡ (γ ×ₒ α)
  asm-3 β γ (f , f-order-pres) = g , g-order-pres
   where
    g : ⟨ β ×ₒ α ⟩ → ⟨ γ ×ₒ α ⟩
    g (b , a) = (f b , a)
    g-order-pres : is-order-preserving (β ×ₒ α) (γ ×ₒ α) g
    g-order-pres (b , a) (c , a') (inl l) = inl l
    g-order-pres (b , a) (c , a') (inr (refl , l)) = inr (refl , f-order-pres b c l)

  module fwa (α-htle : has-trichotomous-least-element α) where
   open framework-with-assumptions (asm-2 α-htle) asm-3 public

 ^ₒ-reflects-⊴ : has-trichotomous-least-element α
               → is-⊴-reflecting (α ^ₒ_)
 ^ₒ-reflects-⊴ = fwa.F-reflects-⊴

 ^ₒ-left-cancellable : has-trichotomous-least-element α
                     → left-cancellable (α ^ₒ_)
 ^ₒ-left-cancellable = fwa.F-left-cancellable

\end{code}

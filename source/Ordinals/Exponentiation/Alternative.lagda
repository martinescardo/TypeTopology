Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
23 April 2023.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.Exponentiation.Alternative
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.Base
open import UF.ClassicalLogic
open import UF.Equiv
open import UF.FunExt
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt
open import UF.ImageAndSurjection pt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua


open import Naturals.Order

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Sigma
open import MLTT.List

open import Ordinals.Arithmetic fe
open import Ordinals.ArithmeticProperties ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying
open import Ordinals.WellOrderingTaboo
open import Ordinals.OrdinalOfOrdinalsSuprema ua

open import Ordinals.Exponentiation.DecreasingList ua pt sr

open PropositionalTruncation pt

open suprema pt sr
\end{code}


We define `exp α β = sup_{1 + ⟨ β ⟩} (inl _ ↦ 𝟙ₒ; inr b ↦ exp α (β ↓ b) ×ₒ α)
by transfinite recursion on β.

\begin{code}

exp-bundled : Σ f ꞉ (Ordinal 𝓤 → Ordinal 𝓥 → Ordinal (𝓤 ⊔ 𝓥)) ,
                ((α : Ordinal 𝓤) (β : Ordinal 𝓥)
                → f α β ＝ sup {I = 𝟙 {𝓤} + ⟨ β ⟩}
                              (cases {X = 𝟙} (λ _ → 𝟙ₒ)
                              (λ b → f α (β ↓ b) ×ₒ α)))
exp-bundled {𝓤} {𝓥} =
 (λ α → transfinite-recursion-on-OO
         (Ordinal (𝓤 ⊔ 𝓥))
         (λ β ih → sup {I = 𝟙 {𝓤} + ⟨ β ⟩} (cases (λ _ → 𝟙ₒ) λ b → ih b ×ₒ α))) ,
 (λ α → transfinite-recursion-on-OO-behaviour
         (Ordinal (𝓤 ⊔ 𝓥))
         (λ β ih → sup {I = 𝟙 {𝓤} + ⟨ β ⟩} (cases (λ _ → 𝟙ₒ) λ b → ih b ×ₒ α)))

abstract
 exp : (α : Ordinal 𝓤) → (β : Ordinal 𝓥) → Ordinal (𝓤 ⊔ 𝓥)
 exp = pr₁ exp-bundled

 exp-behaviour : (α : Ordinal 𝓤) → (β : Ordinal 𝓥) →
                 exp α β ＝ sup {I = 𝟙 {𝓤} + ⟨ β ⟩} (cases {X = 𝟙} (λ _ → 𝟙ₒ) (λ b → exp α (β ↓ b) ×ₒ α))
 exp-behaviour = pr₂ exp-bundled

sup-composition : {B : 𝓤 ̇ }{C : 𝓤 ̇ } → (f : B → C) → (F : C → Ordinal 𝓤) → sup (F ∘ f) ⊴ sup F
sup-composition f F = sup-is-lower-bound-of-upper-bounds (F ∘ f) (sup F) (λ i → sup-is-upper-bound F (f i))

exp-monotone-in-exponent : (α : Ordinal 𝓤) → (β γ : Ordinal 𝓥)
                         → β ⊴ γ → exp α β ⊴ exp α γ
exp-monotone-in-exponent α β γ p = transport₂⁻¹ _⊴_ (exp-behaviour α β) (exp-behaviour α γ) (transport (λ - → sup -  ⊴ sup F) claim' (sup-composition f F))
  where
    F : 𝟙 {𝓤} + ⟨ γ ⟩ → Ordinal _
    F  = cases (λ _ → 𝟙ₒ) (λ c → exp α (γ ↓ c) ×ₒ α)

    f : 𝟙 {𝓤} + ⟨ β ⟩ → 𝟙 {𝓤} + ⟨ γ ⟩
    f (inl x) = inl x
    f (inr b) = inr (pr₁ p b)

    F' : 𝟙 {𝓤} + ⟨ β ⟩ → Ordinal _
    F' = cases (λ _ → 𝟙ₒ) (λ b → exp α (β ↓ b) ×ₒ α)

    initial-segments-agree : (b : ⟨ β ⟩) → β ↓ b ＝ γ ↓ (pr₁ p b)
    initial-segments-agree b = pr₂ (from-≼ (⊴-gives-≼ β γ p) b)

    claim : (i : 𝟙 {𝓤} + ⟨ β ⟩) → F (f i) ＝ F' i
    claim (inl x) = refl
    claim (inr b) = ap (λ - → exp α - ×ₒ α) (initial-segments-agree b ⁻¹)

    claim' : F ∘ f ＝ F'
    claim' = dfunext fe' claim

exp-has-least-element : (α : Ordinal 𝓤) → (β : Ordinal 𝓥) → 𝟙ₒ {𝓤 ⊔ 𝓥} ⊴ exp α β
exp-has-least-element {𝓤} α β = transport⁻¹ (𝟙ₒ ⊴_) (exp-behaviour α β) q
  where
    q : 𝟙ₒ ⊴ sup (cases (λ _ → 𝟙ₒ) (λ b → exp α (β ↓ b) ×ₒ α))
    q = sup-is-upper-bound (cases (λ _ → 𝟙ₒ) (λ b → exp α (β ↓ b) ×ₒ α)) (inl ⋆)

exp-satisfies-zero-specification : (α : Ordinal 𝓤) → exp α (𝟘ₒ {𝓥}) ＝ 𝟙ₒ
exp-satisfies-zero-specification α = ⊴-antisym (exp α 𝟘ₒ) 𝟙ₒ II III
  where
    I : (i : 𝟙 + 𝟘) → cases (λ _ → 𝟙ₒ) (λ b → exp α (𝟘ₒ ↓ b) ×ₒ α) i ⊴ 𝟙ₒ
    I (inl _) = ⊴-refl 𝟙ₒ

    II : exp α 𝟘ₒ ⊴ 𝟙ₒ
    II = transport⁻¹ (_⊴ 𝟙ₒ) (exp-behaviour α 𝟘ₒ) (sup-is-lower-bound-of-upper-bounds (cases (λ _ → 𝟙ₒ) (λ b → exp α (𝟘ₒ ↓ b) ×ₒ α)) 𝟙ₒ I)

    III : 𝟙ₒ ⊴ exp α 𝟘ₒ
    III = exp-has-least-element α 𝟘ₒ

exp-satisfies-succ-specification : (α β : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α
                                 → exp α (β +ₒ 𝟙ₒ) ＝ (exp α β) ×ₒ α
exp-satisfies-succ-specification {𝓤} α β p = transport⁻¹ (λ - → - ＝ (exp α β) ×ₒ α) (exp-behaviour α (β +ₒ 𝟙ₒ) ∙ ap sup eq')
                                                     (⊴-antisym _ _ (sup-is-lower-bound-of-upper-bounds F _ upper-bound) (sup-is-upper-bound F (inr (inr ⋆))))
  where
   F : 𝟙 + (⟨ β ⟩ + 𝟙) → Ordinal 𝓤
   F (inl _) = 𝟙ₒ
   F (inr (inl b)) = exp α (β ↓ b) ×ₒ α
   F (inr (inr _)) = exp α β ×ₒ α

   right-add-α : exp α β ⊴ (exp α β ×ₒ α)
   right-add-α = (transport (_⊴ (exp α β ×ₒ α)) (𝟙ₒ-right-neutral-×ₒ (exp α β)) (×ₒ-right-monotone-⊴ (exp α β) 𝟙ₒ α p))

   upper-bound : (i : 𝟙 + (⟨ β ⟩ + 𝟙)) → F i ⊴ (exp α β ×ₒ α)
   upper-bound (inl _) = ⊴-trans 𝟙ₒ (exp α β) (exp α β ×ₒ α) (exp-has-least-element α β) right-add-α
   upper-bound (inr (inl b)) = ⊴-trans (exp α (β ↓ b) ×ₒ α) (exp α β) (exp α β ×ₒ α)
                                       (transport ((exp α (β ↓ b) ×ₒ α) ⊴_) (exp-behaviour α β ⁻¹) (sup-is-upper-bound (cases (λ _ → 𝟙ₒ) (λ b → exp α (β ↓ b) ×ₒ α)) (inr b)))
                                       right-add-α
   upper-bound (inr (inr _)) = ⊴-refl (exp α β ×ₒ α)

   eq : (i : 𝟙 + (⟨ β ⟩ + 𝟙)) → (cases (λ _ → 𝟙ₒ) (λ b → exp α ((β +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) i ＝ F i
   eq (inl _) = refl
   eq (inr (inl b)) = ap (λ z → exp α z ×ₒ α) (+ₒ-↓-left b ⁻¹)
   eq (inr (inr _)) = ap (λ z → exp α z ×ₒ α) (successor-lemma-right β)

   eq' : (cases (λ _ → 𝟙ₒ) (λ b → exp α ((β +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) ＝ F
   eq' = dfunext fe' eq


exp-power-one-is-identity : (α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → exp α (𝟙ₒ {𝓤}) ＝ α
exp-power-one-is-identity {𝓤} α p =
  exp α (𝟙ₒ {𝓤})      ＝⟨ ap (exp α) (𝟘ₒ-left-neutral 𝟙ₒ ⁻¹)  ⟩
  exp α (𝟘ₒ +ₒ 𝟙ₒ)     ＝⟨ exp-satisfies-succ-specification α 𝟘ₒ p ⟩
  exp α (𝟘ₒ {𝓤}) ×ₒ α ＝⟨ ap (_×ₒ α) (exp-satisfies-zero-specification α) ⟩
  𝟙ₒ ×ₒ α              ＝⟨ 𝟙ₒ-left-neutral-×ₒ α ⟩
  α ∎


curiosity : (P : 𝓤 ̇ ) → (pp : is-prop P) → exp {𝓤} 𝟚ₒ (prop-ordinal P pp) ＝ 𝟙ₒ +ₒ prop-ordinal P pp
curiosity {𝓤} P pp = transport⁻¹ (λ - → - ＝ 𝟙ₒ +ₒ (prop-ordinal P pp))
                                 (exp-behaviour 𝟚ₒ (prop-ordinal P pp) ∙ ap sup (dfunext fe' eq))
                                 (⊴-antisym (sup F) (𝟙ₒ +ₒ prop-ordinal P pp)
                                            (sup-is-lower-bound-of-upper-bounds F _ upper-bound)
                                            (g , g-is-simulation))
 where
  F : 𝟙 + P → Ordinal 𝓤
  F (inl _) = 𝟙ₒ
  F (inr p) = 𝟚ₒ

  eq : (i : 𝟙 + P) → (cases (λ _ → 𝟙ₒ) (λ b → exp 𝟚ₒ (prop-ordinal P pp ↓ b) ×ₒ 𝟚ₒ)) i ＝ F i
  eq (inl _) = refl
  eq (inr p) = exp 𝟚ₒ (prop-ordinal P pp ↓ p) ×ₒ 𝟚ₒ ＝⟨ ap (λ z → exp 𝟚ₒ z ×ₒ 𝟚ₒ) (prop-ordinal-↓ P pp p) ⟩
               exp 𝟚ₒ 𝟘ₒ ×ₒ 𝟚ₒ                      ＝⟨ ap (_×ₒ 𝟚ₒ) (exp-satisfies-zero-specification 𝟚ₒ) ⟩
               𝟙ₒ ×ₒ 𝟚ₒ                             ＝⟨ 𝟙ₒ-left-neutral-×ₒ 𝟚ₒ ⟩
               𝟚ₒ ∎

  upper-bound : (i : 𝟙 + P) → F i ⊴ (𝟙ₒ +ₒ prop-ordinal P pp)
  upper-bound (inl _) = (λ _ → inl _) , (λ x → dep-cases (λ _ → 𝟘-elim) (λ p → 𝟘-elim)) , (λ _ _ q → 𝟘-elim q)
  upper-bound (inr p) = cases inl (λ _ → inr p) , (λ { (inr p') (inl _) _ → (inl _) , (⋆ , refl)
                                                     ; (inl _) (inr p') q → 𝟘-elim q
                                                     ; (inr p') (inr p'') q → 𝟘-elim q})
                                                , (λ { (inl _) (inr p') q → ⋆
                                                     ; (inl _) (inl _) q → 𝟘-elim q})

  f : (i : ⟨ 𝟙ₒ +ₒ prop-ordinal P pp ⟩) → ⟨ F i ⟩
  f (inl _) = ⋆
  f (inr p) = inr ⋆

  g : (i : ⟨ 𝟙ₒ +ₒ prop-ordinal P pp ⟩) → ⟨ sup F ⟩
  g i = pr₁ (sup-is-upper-bound F i) (f i)

  g-is-initial-segment : is-initial-segment (𝟙ₒ +ₒ prop-ordinal P pp) (sup F) g
  g-is-initial-segment (inl _) y q = inl ⋆ , pr₂ (pr₁ (pr₂ (sup-is-upper-bound F (inl _))) ⋆ y q)
  g-is-initial-segment (inr p) y q with pr₁ (pr₂ (sup-is-upper-bound F (inr p))) (inr ⋆) y q
  ... | inl _ , _ , refl = inl ⋆ , ⋆ , ↓-lc (sup F)
                                            (pr₁ (sup-is-upper-bound F (inl ⋆)) ⋆)
                                            (pr₁ (sup-is-upper-bound F (inr p)) (inl ⋆))
                                            e
   where
    e = (sup F ↓ pr₁ (sup-is-upper-bound F (inl ⋆)) ⋆)
          ＝⟨ initial-segment-of-sup-at-component F (inl ⋆) ⋆ ⟩
        (𝟙ₒ ↓ ⋆)
          ＝⟨ +ₒ-↓-left ⋆ ⟩
        (𝟚ₒ ↓ inl ⋆)
          ＝⟨ initial-segment-of-sup-at-component F (inr p) (inl ⋆) ⁻¹ ⟩
        (sup F ↓ pr₁ (sup-is-upper-bound F (inr p)) (inl ⋆))
          ∎

  g-is-order-preserving : is-order-preserving (𝟙ₒ +ₒ prop-ordinal P pp) (sup F) g
  g-is-order-preserving (inl _) (inr p) _ = ↓-reflects-order (sup F) (g (inl _)) (g (inr p)) q
   where
    eq₁ = sup F ↓ pr₁ (sup-is-upper-bound F (inl ⋆)) ⋆
            ＝⟨ initial-segment-of-sup-at-component F (inl ⋆) ⋆ ⟩
          𝟙ₒ ↓ ⋆
            ＝⟨ prop-ordinal-↓ 𝟙 𝟙-is-prop ⋆ ⟩
          𝟘ₒ
            ∎
    eq₂ = sup F ↓ pr₁ (sup-is-upper-bound F (inr p)) (inr ⋆)
            ＝⟨ initial-segment-of-sup-at-component F (inr p) (inr ⋆) ⟩
          (𝟚ₒ ↓ inr ⋆)
            ＝⟨ successor-lemma-right 𝟙ₒ ⟩
          𝟙ₒ
            ∎
    q : (sup F ↓ pr₁ (sup-is-upper-bound F (inl ⋆)) ⋆) ⊲ (sup F ↓ pr₁ (sup-is-upper-bound F (inr p)) (inr ⋆))
    q = transport₂⁻¹ _⊲_ eq₁ eq₂ (⋆ , (prop-ordinal-↓ 𝟙 𝟙-is-prop ⋆ ⁻¹))
  g-is-order-preserving (inl _) (inl _) q = 𝟘-elim q

  g-is-simulation : is-simulation (𝟙ₒ +ₒ prop-ordinal P pp) (sup F) g
  g-is-simulation = g-is-initial-segment , g-is-order-preserving

exp-satisfies-sup-specification : (α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α
                                → {I : 𝓤 ̇ } → ∥ I ∥ → (F : I → Ordinal 𝓤)
                                → exp α (sup F) ＝ sup (λ i → exp α (F i))
exp-satisfies-sup-specification {𝓤} α p {I} i₀ F =
  ∥∥-rec (the-type-of-ordinals-is-a-set (ua _) fe')
         (λ i₀ → transport⁻¹ (λ - → - ＝ sup (λ i → exp α (F i)))
                             (exp-behaviour α (sup F))
                             (⊴-antisym _ _ (sup-is-lower-bound-of-upper-bounds _ _ (left-to-right i₀))
                             (sup-is-lower-bound-of-upper-bounds _ _ right-to-left)))
         i₀
 where
  left-to-right : I → (x : 𝟙 + ⟨ sup F ⟩) → (cases (λ _ → 𝟙ₒ) (λ b → exp α (sup F ↓ b) ×ₒ α)) x ⊴ sup (λ i → exp α (F i))
  left-to-right i₀ (inl _) = ⊴-trans 𝟙ₒ (exp α (F i₀)) (sup (λ i → exp α (F i))) (exp-has-least-element α (F i₀)) (sup-is-upper-bound (λ i → exp α (F i)) i₀)
  left-to-right i₀ (inr y) = ∥∥-rec (⊴-is-prop-valued _ _) (λ (j , y' , eq) → transport⁻¹ (λ - → (exp α - ×ₒ α) ⊴ sup (λ i → exp α (F i))) eq (claim j y')) (initial-segment-of-sup-is-initial-segment-of-some-component F y)
   where
    claim : (j : I) → (y' : ⟨ F j ⟩) → (exp α (F j ↓ y') ×ₒ α) ⊴ sup (λ i → exp α (F i))
    claim j y' = ⊴-trans (exp α (F j ↓ y') ×ₒ α) (exp α (F j)) (sup (λ i → exp α (F i)))
                         (transport⁻¹ ((exp α (F j ↓ y') ×ₒ α) ⊴_) (exp-behaviour α (F j)) (sup-is-upper-bound _ (inr y')))
                         (sup-is-upper-bound (λ i → exp α (F i)) j)

  right-to-left : (i : I) → exp α (F i) ⊴ sup (cases (λ _ → 𝟙ₒ) (λ b → exp α (sup F ↓ b) ×ₒ α))
  right-to-left i = transport⁻¹ (_⊴ sup (cases (λ _ → 𝟙ₒ) (λ b → exp α (sup F ↓ b) ×ₒ α))) (exp-behaviour α (F i)) (sup-is-lower-bound-of-upper-bounds _ _ right-to-left')
   where
    right-to-left' : (x : 𝟙 + ⟨ F i ⟩) → (cases (λ _ → 𝟙ₒ) (λ y → exp α (F i ↓ y) ×ₒ α)) x ⊴ sup (cases {𝓤} {X = 𝟙} (λ _ → 𝟙ₒ) (λ b → exp α (sup F ↓ b) ×ₒ α))
    right-to-left' (inl _) = sup-is-upper-bound (cases {X = 𝟙} (λ _ → 𝟙ₒ) (λ b → exp α (sup F ↓ b) ×ₒ α)) (inl ⋆)
    right-to-left' (inr y) = transport (_⊴ sup (cases {X = 𝟙} (λ _ → 𝟙ₒ) (λ b → exp α (sup F ↓ b) ×ₒ α))) eq (sup-is-upper-bound (cases (λ _ → 𝟙ₒ) (λ b → exp α (sup F ↓ b) ×ₒ α)) (inr y'))
     where
      y' : ⟨ sup F ⟩
      y' = pr₁ (sup-is-upper-bound F i) y
      eq : exp α (sup F ↓ y') ×ₒ α ＝ exp α (F i ↓ y) ×ₒ α
      eq = ap (λ - → exp α - ×ₒ α) (initial-segment-of-sup-at-component F i y)
\end{code}

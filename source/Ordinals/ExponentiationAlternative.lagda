Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
23 April 2023.

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split --lossy-unification #-}

open import UF.Univalence
open import UF.PropTrunc
open import UF.Size

module Ordinals.ExponentiationAlternative
       (ua : Univalence)
       (pt : propositional-truncations-exist)
       (sr : Set-Replacement pt)
       where

open import UF.Base
open import UF.Equiv
open import UF.ExcludedMiddle
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

open import Ordinals.Exponentiation ua pt sr

open PropositionalTruncation pt

open suprema pt sr
\end{code}


We define `exp α β = sup_{1 + ⟨ β ⟩} (inl _ ↦ 𝟙ₒ; inr b ↦ exp α (β ↓ b) ×ₒ α)
by transfinite recursion on β.

\begin{code}

exp : (α : Ordinal 𝓤) → (β : Ordinal 𝓥) → Ordinal (𝓤 ⊔ 𝓥)
exp {𝓤} {𝓥} α = transfinite-recursion-on-OO
                  (Ordinal (𝓤 ⊔ 𝓥))
                  (λ β ih → sup {I = 𝟙 {𝓤} + ⟨ β ⟩}
                                  (cases
                                    (λ _ → 𝟙ₒ)
                                    (λ b → ih b ×ₒ α))) -- exp α (β ↓ b) ×ₒ α

exp-behaviour : (α : Ordinal 𝓤) → (β : Ordinal 𝓥) →
                exp α β ＝ sup {I = 𝟙 {𝓤} + ⟨ β ⟩} (cases (λ _ → 𝟙ₒ) (λ b → exp α (β ↓ b) ×ₒ α))
exp-behaviour {𝓤} {𝓥} α β = {!transfinite-recursion-on-OO-behaviour (Ordinal (𝓤 ⊔ 𝓥)) ((λ β ih → sup {I = 𝟙 {𝓤} + ⟨ β ⟩} (cases (λ _ → 𝟙ₒ) (λ b → ih b ×ₒ α)))exp-body α) β!}

\end{code}

\begin{code}

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
   eq (inr (inr _)) = ap (λ z → exp α z ×ₒ α) (+ₒ-𝟙ₒ-↓-right β)

   eq' : (cases (λ _ → 𝟙ₒ) (λ b → exp α ((β +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) ＝ F
   eq' = dfunext fe' eq


exp-power-one-is-identity : (α : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α → exp α (𝟙ₒ {𝓤}) ＝ α
exp-power-one-is-identity {𝓤} α p =
  exp α (𝟙ₒ {𝓤})      ＝⟨ ap (exp α) (𝟘ₒ-left-neutral 𝟙ₒ ⁻¹)  ⟩
  exp α (𝟘ₒ +ₒ 𝟙ₒ)     ＝⟨ exp-satisfies-succ-specification α 𝟘ₒ p ⟩
  exp α (𝟘ₒ {𝓤}) ×ₒ α ＝⟨ ap (_×ₒ α) (exp-satisfies-zero-specification α) ⟩
  𝟙ₒ ×ₒ α              ＝⟨ 𝟙ₒ-left-neutral-×ₒ α ⟩
  α ∎


\end{code}

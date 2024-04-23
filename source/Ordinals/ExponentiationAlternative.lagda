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

-- exp-preserves-having-least-element

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

exp-satisfies-succ-specification : (α β : Ordinal 𝓤) → 𝟙ₒ {𝓤} ⊴ α
                                 → exp α (β +ₒ 𝟙ₒ) ＝ (exp α β) ×ₒ α
exp-satisfies-succ-specification α β p = transport⁻¹ (λ - → - ＝ (exp α β) ×ₒ α) (exp-behaviour α (β +ₒ 𝟙ₒ))
                                           (surjective-simulation-gives-equality _ (exp α β ×ₒ α) f f-is-simulation f-is-surjective)
 where
  h : sup (cases (λ _ → 𝟙ₒ) (λ b → exp α ((β +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) ⊴ ((exp α β) ×ₒ α)
  h = (sup-is-lower-bound-of-upper-bounds (cases (λ _ → 𝟙ₒ) (λ b → exp α ((β +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) ((exp α β) ×ₒ α) k)
    where
      k : (i : 𝟙 + pr₁ (β +ₒ 𝟙ₒ)) → cases (λ _ → 𝟙ₒ) (λ b → exp α ((β +ₒ 𝟙ₒ) ↓ b) ×ₒ α) i ⊴ (exp α β ×ₒ α)
      k (inl _) = {!!}
      k (inr (inl b)) = {!!}
      k (inr (inr _)) = {!!}

  f : ⟨ sup (cases (λ _ → 𝟙ₒ) (λ b → exp α ((β +ₒ 𝟙ₒ) ↓ b) ×ₒ α)) ⟩ →  ⟨ (exp α β) ×ₒ α ⟩
  f = pr₁ h

  f-is-simulation : is-simulation _ (exp α β ×ₒ α) f
  f-is-simulation = pr₂ h

  f-is-surjective : is-surjection f
  f-is-surjective = {!!}

{-

-}

\end{code}

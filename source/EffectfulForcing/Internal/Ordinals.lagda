\begin{code}
{-# OPTIONS --allow-unsolved-metas --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence

module EffectfulForcing.Internal.Ordinals
        (ua : Univalence)
        (pt : propositional-truncations-exist)
        (sr : Set-Replacement pt)
       where

private
 fe : Fun-Ext
 fe {𝓤} {𝓥} = univalence-gives-funext' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

 pe : Prop-Ext
 pe {𝓤} = univalence-gives-propext (ua 𝓤)

open import Ordinals.Brouwer
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.OrdinalOfOrdinalsSuprema ua
open import Ordinals.Type
open import Ordinals.Underlying

import Ordinals.NotationInterpretation0 ua pt as NotationInterpretation

open suprema pt sr

-- TODO decide where to place all of this, I suggest
-- Ordinals.BrouwerArithmetic for arithmetic operations on Brouwer codes
-- Ordinals.BrouwerOrderingProperties for the ordering properties

-- TODO remove --allow-unsolved-metas and add back --safe

⦅_⦆ : B → Ordinal 𝓤₀
⦅ b ⦆ = NotationInterpretation.⟦_⟧₀ sr b

B-⊲-S : (b : B) → ⦅ b ⦆ ⊲ ⦅ S b ⦆
B-⊲-S b = (inr ⋆) , eqtoidₒ (ua 𝓤₀) fe ⦅ b ⦆ (⦅ S b ⦆ ↓ inr ⋆) goal
 where
  f : ⟨ ⦅ b ⦆ ⟩ → ⟨ ⦅ S b ⦆ ↓ inr ⋆ ⟩
  f a = inl a , ⋆

  g : ⟨ ⦅ S b ⦆ ↓ inr ⋆ ⟩ → ⟨ ⦅ b ⦆ ⟩
  g (inl a , inla<inr⋆) = a

  gf : ∀ x → g (f x) ＝ x
  gf _ = refl

  fg : ∀ x → f (g x) ＝ x
  fg (inl a , inla<inr⋆) = refl

  f-is-order-preserving : is-order-preserving ⦅ b ⦆ (⦅ S b ⦆ ↓ inr ⋆) f
  f-is-order-preserving a b a<b = a<b

  g-is-order-preserving : is-order-preserving (⦅ S b ⦆ ↓ inr ⋆) ⦅ b ⦆ g
  g-is-order-preserving (inl a , inla<inr⋆) (inl b , inlb<inr⋆) a<b = a<b

  goal : ⦅ b ⦆ ≃ₒ (⦅ S b ⦆ ↓ inr ⋆)
  goal = f , f-is-order-preserving , qinvs-are-equivs f (g , gf , fg) , g-is-order-preserving

B-⊴-L : (ϕ : ℕ → B) (n : ℕ) → ⦅ ϕ n ⦆ ⊴ ⦅ L ϕ ⦆
B-⊴-L ϕ n = sup-is-upper-bound (λ i → ⦅ ϕ i ⦆) n

⊴-and-⊲-implies-⊲ : (α β γ :  Ordinal 𝓤) → α ⊴ β → β ⊲ γ → α ⊲ γ
⊴-and-⊲-implies-⊲ α β γ (f , hf) (c , eq) = {!!}

B-rec : {X : 𝓤₀ ̇ } → X → (X → X) → ((ℕ → X) → X) → B → X
B-rec z s l Z     = z
B-rec z s l (S d) = s (B-rec z s l d)
B-rec z s l (L ϕ) = l (B-rec z s l ∘ ϕ)

B-add : B → B → B
B-add u v = B-rec v S L u

B-mul : B → B → B
B-mul u v = B-rec Z (λ r → B-add u r) L v

B-exp : B → B → B
B-exp u v = B-rec (S Z) (λ r → B-mul u r) L v

B-finite : ℕ → B
B-finite = rec Z S

B-ω : B
B-ω = L B-finite

B-ω-tower : ℕ → B
B-ω-tower = rec B-ω (B-exp B-ω)

B-ε₀ : B
B-ε₀ = L B-ω-tower

ε₀ : Ordinal 𝓤₀
ε₀ = ⦅ B-ε₀ ⦆

\end{code}

Tom de Jong, Nicolai Kraus, Fredrik Nordvall Forsberg, Chuangjie Xu,
13 November 2023.

TEMPORARILY SPLIT UP TO SPEED UP TYPECHECKING

\begin{code}

{-# OPTIONS --safe --without-K --no-exact-split #-}

open import UF.Univalence

module Ordinals.Exponentiation-More
       (ua : Univalence)
       where

open import UF.Base
open import UF.Embeddings hiding (⌊_⌋)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import MLTT.Plus-Properties
open import MLTT.Spartan hiding (cases ; Cases)
open import MLTT.Sigma
-- open import Notation.CanonicalMap
open import Ordinals.Arithmetic fe
open import Ordinals.ArithmeticProperties ua
open import Ordinals.ConvergentSequence ua
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.Underlying

-- our imports
open import MLTT.List
open import Ordinals.Exponentiation ua

\end{code}

\begin{code}

module _ (pt : propositional-truncations-exist)
         (sr : Set-Replacement pt)
       where

 open PropositionalTruncation pt

 open import Ordinals.OrdinalOfOrdinalsSuprema ua
 open suprema pt sr

 open import UF.ImageAndSurjection pt

 is-continuous : (Ordinal 𝓤 → Ordinal 𝓤) → 𝓤 ⁺ ̇
 is-continuous {𝓤} F = {I : 𝓤 ̇  } (γ : I → Ordinal 𝓤) → F (sup γ) ＝ sup (F ∘ γ)

 is-monotone-if-continuous : (F : Ordinal 𝓤 → Ordinal 𝓤)
                           → is-continuous F
                           → is-monotone (OO 𝓤) (OO 𝓤) F
 is-monotone-if-continuous {𝓤} F F-cont α β α-less-than-β = conclusion
  where
   γ : 𝟙{𝓤} + 𝟙{𝓤} → Ordinal 𝓤
   γ (inl _) = α
   γ (inr _) = β
   eq : F (sup γ) ＝ sup (F ∘ γ)
   eq = F-cont γ
   β-is-upper-bound : (i : 𝟙 + 𝟙) → γ i ⊴ β
   β-is-upper-bound (inl _) = ≼-gives-⊴ α β α-less-than-β
   β-is-upper-bound (inr _) = ⊴-refl β
   I : sup γ ＝ β
   I = ⊴-antisym (sup γ) β (sup-is-lower-bound-of-upper-bounds γ β β-is-upper-bound) (sup-is-upper-bound γ (inr ⋆))
   ineq : F α ⊴ sup (F ∘ γ)
   ineq = sup-is-upper-bound (F ∘ γ) (inl ⋆)
   conclusion : F α ≼ F β
   conclusion = ⊴-gives-≼ (F α) (F β) (transport (F α ⊴_) (eq ⁻¹ ∙ ap F I) ineq)

 module _
         (exp : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤)
        where

  full-sup-spec : 𝓤 ⁺ ̇
  full-sup-spec = (α : Ordinal 𝓤) → is-continuous (exp α)

  full-succ-spec : 𝓤 ⁺ ̇
  full-succ-spec = (α : Ordinal 𝓤) (β : Ordinal 𝓤) → exp α (β +ₒ 𝟙ₒ) ＝ exp α β ×ₒ α

  full-zero-spec : 𝓤 ⁺ ̇
  full-zero-spec = (α : Ordinal 𝓤) → exp α 𝟘ₒ ＝ 𝟙ₒ

  full-spec : 𝓤 ⁺ ̇
  full-spec = full-zero-spec × full-succ-spec × full-sup-spec

  exp-is-monotone-gives-EM : full-zero-spec
                           → full-succ-spec
                           → ((α : Ordinal 𝓤) → is-monotone (OO 𝓤) (OO 𝓤) (exp α))
                           → EM 𝓤
  exp-is-monotone-gives-EM spec₀ specₛ mon P P-is-prop = P-is-decidable
   where
    α : Ordinal 𝓤
    α = prop-ordinal (P + ¬ P) (decidability-of-prop-is-prop fe' P-is-prop)
    ineq : exp α 𝟘ₒ ⊴ exp α 𝟙ₒ
    ineq = ≼-gives-⊴ (exp α 𝟘ₒ) (exp α 𝟙ₒ) (mon α 𝟘ₒ 𝟙ₒ (𝟘ₒ-least 𝟙ₒ))
    eq₁ : exp α 𝟘ₒ ＝ 𝟙ₒ
    eq₁ = spec₀ α
    eq₂ : exp α 𝟙ₒ ＝ α
    eq₂ = exp α 𝟙ₒ ＝⟨ ap (exp α) ((𝟘ₒ-left-neutral 𝟙ₒ) ⁻¹) ⟩
          exp α (𝟘ₒ +ₒ 𝟙ₒ) ＝⟨ specₛ α 𝟘ₒ ⟩
          (exp α 𝟘ₒ ×ₒ α) ＝⟨ ap (_×ₒ α) eq₁ ⟩
          𝟙ₒ ×ₒ α ＝⟨ 𝟙ₒ-left-neutral-×ₒ α ⟩
          α ∎
    ineq' : 𝟙ₒ ⊴ α
    ineq' = transport₂ _⊴_ eq₁ eq₂ ineq
    P-is-decidable : P + ¬ P
    P-is-decidable = pr₁ ineq' ⋆

  exp-full-spec-gives-EM : full-spec → EM 𝓤
  exp-full-spec-gives-EM (spec₀ , specₛ , specₗ) =
   exp-is-monotone-gives-EM spec₀ specₛ
    (λ α → is-monotone-if-continuous (exp α) (specₗ α))

\end{code}

And conversely...

\begin{code}


 -- TODO: Reduce to EM 𝓤

 private
  case : (α : Ordinal 𝓤) → 𝓤 ⁺ ̇
  case {𝓤} α = (Σ α' ꞉ Ordinal 𝓤 , α ＝ 𝟙ₒ +ₒ α')

  case-is-prop : (α : Ordinal 𝓤) → is-prop (case α)
  case-is-prop α = {!!}

  cases : (α : Ordinal 𝓤) → 𝓤 ⁺ ̇
  cases α = case α + (α ＝ 𝟘ₒ)

  Cases : 𝓤 ⁺ ̇
  Cases {𝓤} = (α : Ordinal 𝓤) → cases α

 Cases-gives-full-spec : Cases → Σ exp ꞉ (Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤) , full-spec exp
 Cases-gives-full-spec {𝓤} cs = {!!}
  where
   exp-aux : (α : Ordinal 𝓤)
           → cases α
           → Ordinal 𝓤 → Ordinal 𝓤
   exp-aux α (inl (α' , _)) β = [𝟙+ α' ]^ β
   exp-aux α (inr _) β = prop-ordinal (β ≃ₒ 𝟘ₒ{𝓤}) (≃ₒ-is-prop-valued fe' β 𝟘ₒ)
   exp : Ordinal 𝓤 → Ordinal 𝓤 → Ordinal 𝓤
   exp α = exp-aux α (cs α)

\end{code}

Martin Escardo 4th May 2022.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module Ordinals.ToppedAdditionProperties
       (ua : Univalence)
       where

open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

 pe : PropExt
 pe = Univalence-gives-PropExt ua

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import Notation.CanonicalMap
open import Ordinals.Arithmetic fe
open import Ordinals.Closure fe using (∑-≃ₒ)
open import Ordinals.Equivalence
open import Ordinals.Injectivity
open import Ordinals.Maps
open import Ordinals.ToppedArithmetic fe
open import Ordinals.ToppedType fe
open import Ordinals.Type
open import Ordinals.Underlying
open import TypeTopology.SquashedSum fe
open import UF.Embeddings

open topped-ordinals-injectivity fe

alternative-plusₒ : (τ₀ τ₁ : Ordinalᵀ 𝓤)
                  → [ τ₀ +ᵒ τ₁ ] ≃ₒ ([ τ₀ ] +ₒ [ τ₁ ])
alternative-plusₒ τ₀ τ₁ = e
 where
  υ = cases (λ ⋆ → τ₀) (λ ⋆ → τ₁)

  f : ⟨ ∑ 𝟚ᵒ υ ⟩ → ⟨ [ τ₀ ] +ₒ [ τ₁ ] ⟩
  f (inl ⋆ , x) = inl x
  f (inr ⋆ , y) = inr y

  g : ⟨ [ τ₀ ] +ₒ [ τ₁ ] ⟩ → ⟨ ∑ 𝟚ᵒ υ ⟩
  g (inl x) = (inl ⋆ , x)
  g (inr y) = (inr ⋆ , y)

  η : g ∘ f ∼ id
  η (inl ⋆ , x) = refl
  η (inr ⋆ , y) = refl

  ε : f ∘ g ∼ id
  ε (inl x) = refl
  ε (inr y) = refl

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , η , ε)
  f-is-op : is-order-preserving [ ∑ 𝟚ᵒ υ ] ([ τ₀ ] +ₒ [ τ₁ ]) f

  f-is-op (inl ⋆ , _) (inl ⋆ , _) (inr (refl , l)) = l
  f-is-op (inl ⋆ , _) (inr ⋆ , _) (inl ⋆)          = ⋆
  f-is-op (inr ⋆ , _) (inl ⋆ , _) (inl l)          = l
  f-is-op (inr ⋆ , _) (inr ⋆ , _) (inr (refl , l)) = l

  g-is-op : is-order-preserving ([ τ₀ ] +ₒ [ τ₁ ]) [ ∑ 𝟚ᵒ υ ] g
  g-is-op (inl _) (inl _) l = inr (refl , l)
  g-is-op (inl _) (inr _) ⋆ = inl ⋆
  g-is-op (inr _) (inl _) ()
  g-is-op (inr _) (inr _) l = inr (refl , l)

  e : [ ∑ 𝟚ᵒ υ ] ≃ₒ ([ τ₀ ] +ₒ [ τ₁ ])
  e = f , f-is-op , f-is-equiv , g-is-op

alternative-plus : (τ₀ τ₁ : Ordinalᵀ 𝓤)
                 → [ τ₀ +ᵒ τ₁ ] ＝ ([ τ₀ ] +ₒ [ τ₁ ])
alternative-plus τ₀ τ₁ = eqtoidₒ (ua _) fe' _ _ (alternative-plusₒ τ₀ τ₁)

\end{code}

Added by Martin Escardo 2nd September 2026.

The successor sum of a countable family is the successor of the sum of
the family over ω.

\begin{code}

∑₁-is-successorₒ : (τ : ℕ → Ordᵀ) → [ ∑₁ τ ] ≃ₒ (∑ₒ ω τ +ₒ 𝟙ₒ)
∑₁-is-successorₒ τ = ≃ₒ-trans
                      [ ∑₁ τ ]
                      [ ∑ (succₒ ω) (cases τ (λ _ → 𝟙ᵒ)) ]
                      (∑ₒ ω τ +ₒ 𝟙ₒ)
                      II
                      III
 where
  𝓮 : ℕ ↪ ℕ + 𝟙
  𝓮 = over , over-embedding

  I : (z : ℕ + 𝟙)
    → [ (τ ↗ 𝓮) z ] ≃ₒ [ cases τ (λ _ → 𝟙ᵒ) z ]
  I (inl n) = ↗-propertyₒ τ 𝓮 n
  I (inr ⋆) = ↗-out-of-range τ 𝓮 (inr ⋆) (λ n → +disjoint)

  II : [ ∑₁ τ ] ≃ₒ [ ∑ (succₒ ω) (cases τ (λ _ → 𝟙ᵒ)) ]
  II = ∑-≃ₒ (succₒ ω) (τ ↗ 𝓮) (cases τ (λ _ → 𝟙ᵒ)) I

  υ : ℕ + 𝟙 → Ordᵀ
  υ = cases τ (λ _ → 𝟙ᵒ)

  f : ⟨ ∑ (succₒ ω) υ ⟩ → ⟨ ∑ₒ ω τ +ₒ 𝟙ₒ ⟩
  f (inl n , x) = inl (n , x)
  f (inr ⋆ , _) = inr ⋆

  g : ⟨ ∑ₒ ω τ +ₒ 𝟙ₒ ⟩ → ⟨ ∑ (succₒ ω) υ ⟩
  g (inl (n , x)) = inl n , x
  g (inr ⋆)       = inr ⋆ , ⋆

  η : g ∘ f ∼ id
  η (inl n , x) = refl
  η (inr ⋆ , ⋆) = refl

  ε : f ∘ g ∼ id
  ε (inl (n , x)) = refl
  ε (inr ⋆)       = refl

  f-is-equiv : is-equiv f
  f-is-equiv = qinvs-are-equivs f (g , η , ε)

  f-is-op : is-order-preserving [ ∑ (succₒ ω) υ ] (∑ₒ ω τ +ₒ 𝟙ₒ) f
  f-is-op (inl n , _) (inl m , _) (inl l)          = inl l
  f-is-op (inl n , _) (inl m , _) (inr (refl , l)) = inr (refl , l)
  f-is-op (inl n , _) (inr ⋆ , _) (inl ⋆)          = ⋆
  f-is-op (inr ⋆ , _) (inl m , _) (inl l)          = 𝟘-elim l
  f-is-op (inr ⋆ , _) (inr ⋆ , _) (inl l)          = 𝟘-elim l
  f-is-op (inr ⋆ , _) (inr ⋆ , _) (inr (refl , l)) = 𝟘-elim l

  g-is-op : is-order-preserving (∑ₒ ω τ +ₒ 𝟙ₒ) [ ∑ (succₒ ω) υ ] g
  g-is-op (inl (n , _)) (inl (m , _)) (inl l)          = inl l
  g-is-op (inl (n , _)) (inl (m , _)) (inr (refl , l)) = inr (refl , l)
  g-is-op (inl (n , _)) (inr ⋆)       ⋆                = inl ⋆
  g-is-op (inr ⋆)       (inr ⋆)       l                = 𝟘-elim l

  III : [ ∑ (succₒ ω) (cases τ (λ _ → 𝟙ᵒ)) ] ≃ₒ (∑ₒ ω τ +ₒ 𝟙ₒ)
  III = f , f-is-op , f-is-equiv , g-is-op

∑₁-is-successor : (τ : ℕ → Ordᵀ) → [ ∑₁ τ ] ＝ (∑ₒ ω τ +ₒ 𝟙ₒ)
∑₁-is-successor τ = eqtoidₒ (ua _) fe' _ _ (∑₁-is-successorₒ τ)

\end{code}

End of addition.

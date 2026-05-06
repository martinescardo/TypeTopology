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

open import MLTT.Spartan
open import Notation.CanonicalMap
open import Ordinals.Arithmetic fe
open import Ordinals.Equivalence
open import Ordinals.Maps
open import Ordinals.ToppedArithmetic fe
open import Ordinals.ToppedType fe
open import Ordinals.Type
open import Ordinals.Underlying

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

Martin Escardo, 18 January 2021.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-Univalence

module OrdinalArithmetic-Properties
       (ua : Univalence)
       where

open import UF-Equiv
open import UF-UA-FunExt
open import UF-FunExt
open import UF-EquivalenceExamples

private
 fe : FunExt
 fe = FunExt-from-Univalence ua

open import SpartanMLTT
open import OrdinalsType
open import OrdinalOfOrdinals ua
open import OrdinalArithmetic fe

𝟘ₒ-left-neutral : (α : Ordinal 𝓤) → 𝟘ₒ +ₒ α ≡ α
𝟘ₒ-left-neutral α = eqtoidₒ (𝟘ₒ +ₒ α) α h
 where
  f : 𝟘 + ⟨ α ⟩ → ⟨ α ⟩
  f = ⌜ 𝟘-lneutral ⌝

  f-preserves-order : (x y : 𝟘 + ⟨ α ⟩) → x ≺⟨ 𝟘ₒ +ₒ α ⟩ y → f x ≺⟨ α ⟩ f y
  f-preserves-order (inr x) (inr y) l = l

  f-reflects-order : (x y : 𝟘 + ⟨ α ⟩) → f x ≺⟨ α ⟩ f y → x ≺⟨ 𝟘ₒ +ₒ α ⟩ y
  f-reflects-order (inr x) (inr y) l = l


  h : (𝟘ₒ +ₒ α) ≃ₒ α
  h = f , order-equiv-criterion (𝟘ₒ +ₒ α) α f
           (⌜⌝-is-equiv 𝟘-lneutral) f-preserves-order f-reflects-order

𝟘ₒ-right-neutral : (α : Ordinal 𝓤) → α  +ₒ 𝟘ₒ ≡ α
𝟘ₒ-right-neutral α = eqtoidₒ (α +ₒ 𝟘ₒ) α h
 where
  f : ⟨ α ⟩ + 𝟘 → ⟨ α ⟩
  f = ⌜ 𝟘-rneutral' ⌝

  f-preserves-order : is-order-preserving (α  +ₒ 𝟘ₒ) α f
  f-preserves-order (inl x) (inl y) l = l

  f-reflects-order : is-order-reflecting (α  +ₒ 𝟘ₒ) α f
  f-reflects-order (inl x) (inl y) l = l


  h : (α +ₒ 𝟘ₒ) ≃ₒ α
  h = f , order-equiv-criterion (α +ₒ 𝟘ₒ) α f
           (⌜⌝-is-equiv 𝟘-rneutral') f-preserves-order f-reflects-order

+ₒ-assoc : (α β γ : Ordinal 𝓤) → (α  +ₒ β) +ₒ γ ≡ α  +ₒ (β +ₒ γ)
+ₒ-assoc α β γ = eqtoidₒ ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) h
 where
  f : ⟨ (α +ₒ β) +ₒ γ ⟩ → ⟨ α +ₒ (β +ₒ γ) ⟩
  f = ⌜ +assoc ⌝

  f-preserves-order : is-order-preserving  ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) f
  f-preserves-order (inl (inl x)) (inl (inl y)) l = l
  f-preserves-order (inl (inl x)) (inl (inr y)) l = l
  f-preserves-order (inl (inr x)) (inl (inr y)) l = l
  f-preserves-order (inl (inl x)) (inr y)       l = l
  f-preserves-order (inl (inr x)) (inr y)       l = l
  f-preserves-order (inr x)       (inr y)       l = l


  f-reflects-order : is-order-reflecting ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) f
  f-reflects-order (inl (inl x)) (inl (inl y)) l = l
  f-reflects-order (inl (inl x)) (inl (inr y)) l = l
  f-reflects-order (inl (inr x)) (inl (inr y)) l = l
  f-reflects-order (inl (inl x)) (inr y)       l = l
  f-reflects-order (inl (inr x)) (inr y)       l = l
  f-reflects-order (inr x)       (inl (inl y)) l = l
  f-reflects-order (inr x)       (inl (inr y)) l = l
  f-reflects-order (inr x)       (inr y)       l = l


  h : ((α  +ₒ β) +ₒ γ) ≃ₒ (α  +ₒ (β +ₒ γ))
  h = f , order-equiv-criterion ((α  +ₒ β) +ₒ γ) (α  +ₒ (β +ₒ γ)) f
           (⌜⌝-is-equiv +assoc) f-preserves-order f-reflects-order

\end{code}

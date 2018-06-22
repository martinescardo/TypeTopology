Martin Escardo, 21 June 2018

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module OrdinalConstructions where

open import SpartanMLTT hiding (_≤_)
open import Ordinals hiding (_≤_)
open import UF-Subsingletons

\end{code}

\begin{code}

module _ {U V} where

 _<[𝟘]_ : 𝟘 {U} → 𝟘 {U} → V ̇
 _<[𝟘]_ () ()

 𝟘-prop-valued : is-prop-valued-order _<[𝟘]_
 𝟘-prop-valued {()}

 𝟘-extensional : is-extensional _<[𝟘]_
 𝟘-extensional ()

 𝟘-transitive : is-transitive _<[𝟘]_
 𝟘-transitive ()

 𝟘-well-founded : is-well-founded _<[𝟘]_
 𝟘-well-founded ()

 𝟘-ordinal : is-ordinal _<[𝟘]_
 𝟘-ordinal = 𝟘-well-founded , 𝟘-extensional , 𝟘-transitive

\end{code}

The ordinal 𝟙.

\begin{code}

 _<[𝟙]_ : 𝟙 {U} → 𝟙 {U} → V ̇
 _<[𝟙]_ _ _ = 𝟘

 𝟙-prop-valued : is-prop-valued-order _<[𝟙]_
 𝟙-prop-valued = 𝟘-is-prop

 𝟙-extensional : is-extensional _<[𝟙]_
 𝟙-extensional * * f g = refl

 𝟙-transitive : is-transitive _<[𝟙]_
 𝟙-transitive x y z ()

 𝟙-well-founded : is-well-founded _<[𝟙]_
 𝟙-well-founded x = next x (λ y ())

 𝟙-ordinal : is-ordinal _<[𝟙]_
 𝟙-ordinal = 𝟙-well-founded , 𝟙-extensional , 𝟙-transitive

\end{code}

The sum of two ordinals.

\begin{code}

module _ {U V W} {X₀ : U ̇} (_<₀_ : X₀ → X₀ → W ̇) {X₁ : V ̇} (_<₁_ : X₁ → X₁ → W ̇) where

  private _<_ : X₀ + X₁ → X₀ + X₁ → W ̇
  (inl x₀) < (inl y₀) = x₀ <₀ y₀
  (inl x₀) < (inr y₁) = 𝟙
  (inr x₁) < (inl y₀) = 𝟘
  (inr x₁) < (inr y₁) = x₁ <₁ y₁

  addition = _<_
  
  addition-prop-valued : is-prop-valued-order _<₀_ → is-prop-valued-order _<₁_ → is-prop-valued-order _<_
  addition-prop-valued p₀ p₁ {inl x₀} {inl y₀} l m = p₀ l m
  addition-prop-valued p₀ p₁ {inl x₀} {inr y₁} * * = refl
  addition-prop-valued p₀ p₁ {inr x₁} {inl y₀} () m
  addition-prop-valued p₀ p₁ {inr x₁} {inr y₁} l m = p₁ l m

  addition-extensional : is-well-founded _<₀_ → is-extensional _<₀_ → is-extensional _<₁_ → is-extensional _<_
  addition-extensional w₀ e₀ e₁ (inl x₀) (inl y₀) f g = ap inl (e₀ x₀ y₀ (λ u l → f (inl u) l) (λ u l → g (inl u) l))
  addition-extensional w₀ e₀ e₁ (inl x₀) (inr y₁) f g = 𝟘-elim (≤-refl _<₀_ x₀ (w₀ x₀) (g (inl x₀) *))
  addition-extensional w₀ e₀ e₁ (inr x₁) (inl y₀) f g = 𝟘-elim (≤-refl _<₀_ y₀ (w₀ y₀) (f (inl y₀) *))
  addition-extensional w₀ e₀ e₁ (inr x₁) (inr y₁) f g = ap inr (e₁ x₁ y₁ (λ u l → f (inr u) l) (λ u l → g (inr u) l))

  addition-transitive : is-transitive _<₀_ → is-transitive _<₁_ → is-transitive _<_
  addition-transitive t₀ t₁ (inl x₀) (inl y₀) (inl z₀) l m = t₀ x₀ y₀ z₀ l m
  addition-transitive t₀ t₁ (inl x₀) (inl y₀) (inr z₁) l m = *
  addition-transitive t₀ t₁ (inl x₀) (inr y₁) (inl z₀) l ()
  addition-transitive t₀ t₁ (inl x₀) (inr y₁) (inr z₁) l m = *
  addition-transitive t₀ t₁ (inr x₁) (inl y₀) z () m
  addition-transitive t₀ t₁ (inr x₁) (inr y₁) (inl z₁) l ()
  addition-transitive t₀ t₁ (inr x₁) (inr y₁) (inr z₁) l m = t₁ x₁ y₁ z₁ l m
  
  addition-well-founded : is-well-founded _<₀_ → is-well-founded _<₁_ → is-well-founded _<_
  addition-well-founded w₀ w₁ = g
   where
    φ : (x₀ : X₀) → is-accessible _<₀_ x₀ → is-accessible _<_ (inl x₀)
    φ x₀ (next .x₀ σ) = next (inl x₀) τ
     where
      τ : (s : X₀ + X₁) → s < inl x₀ → is-accessible _<_ s
      τ (inl y₀) l = φ y₀ (σ y₀ l)
      τ (inr y₁) ()
    γ : (x₁ : X₁) → is-accessible _<₁_ x₁ → is-accessible _<_ (inr x₁)
    γ x₁ (next .x₁ σ) = next (inr x₁) τ
     where
      τ : (s : X₀ + X₁) → s < inr x₁ → is-accessible _<_ s
      τ (inl x₀) l = φ x₀ (w₀ x₀)
      τ (inr y₁) l = γ y₁ (σ y₁ l)
    g : is-well-founded _<_
    g (inl x₀) = φ x₀ (w₀ x₀) 
    g (inr x₁) = γ x₁ (w₁ x₁)

  addition-ordinal : is-ordinal _<₀_ → is-ordinal _<₁_ → is-ordinal _<_
  addition-ordinal (w₀ , e₀ , t₀) (w₁ , e₁ , t₁) = addition-well-founded w₀ w₁ ,
                                                   addition-extensional w₀ e₀ e₁ ,
                                                   addition-transitive t₀ t₁

\end{code}

Successor

\begin{code}

module _ {U V} {X : U ̇} (_<_ : X → X → V ̇) where

  private _<'_ : X + 𝟙 {U} → X + 𝟙 → V ̇
  _<'_ = addition _<_ _<[𝟙]_

  successor = _<'_

\end{code}

Many things to do. To begin with, 𝟙 is an ordinal for a suitable
(unique) order, so that then we get the successor operation on
ordinals using addition.

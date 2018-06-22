Martin Escardo, 21 June 2018

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module OrdinalConstructions where

open import SpartanMLTT hiding (_≤_)
open import Ordinals hiding (_≤_)
open import UF-Subsingletons

\end{code}

Any proposition is an ordinal under the empty ordering.

\begin{code}

module subsingleton-ordinal {U V} (P : U ̇) (isp : is-prop P) where

 private _<_ : P → P → V ̇
 _<_ x y = 𝟘

 order = _<_

 prop-valued : is-prop-valued-order _<_
 prop-valued x y = 𝟘-is-prop

 extensional : is-extensional _<_
 extensional x y f g = isp x y 

 transitive : is-transitive _<_
 transitive x y z ()

 well-founded : is-well-founded _<_
 well-founded x = next x (λ y ())

 ordinal : is-ordinal _<_
 ordinal = prop-valued , well-founded , extensional , transitive

\end{code}

Two particular cases are 𝟘 and 𝟙, of course.

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
  addition-prop-valued p₀ p₁ (inl x₀) (inl y₀) l m = p₀ x₀ y₀ l m
  addition-prop-valued p₀ p₁ (inl x₀) (inr y₁) * * = refl
  addition-prop-valued p₀ p₁ (inr x₁) (inl y₀) () m
  addition-prop-valued p₀ p₁ (inr x₁) (inr y₁) l m = p₁ x₁ y₁ l m

  addition-extensional : is-well-founded _<₀_ → is-extensional _<₀_ → is-extensional _<₁_ → is-extensional _<_
  addition-extensional w₀ e₀ e₁ (inl x₀) (inl y₀) f g = ap inl (e₀ x₀ y₀ (f ∘ inl) (g ∘ inl))
  addition-extensional w₀ e₀ e₁ (inl x₀) (inr y₁) f g = 𝟘-elim (≤-refl _<₀_ x₀ (w₀ x₀) (g (inl x₀) *))
  addition-extensional w₀ e₀ e₁ (inr x₁) (inl y₀) f g = 𝟘-elim (≤-refl _<₀_ y₀ (w₀ y₀) (f (inl y₀) *))
  addition-extensional w₀ e₀ e₁ (inr x₁) (inr y₁) f g = ap inr (e₁ x₁ y₁ (f ∘ inr) (g ∘ inr))

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
  addition-ordinal (p₀ , w₀ , e₀ , t₀) (p₁ , w₁ , e₁ , t₁) = addition-prop-valued p₀ p₁ ,
                                                           addition-well-founded w₀ w₁ ,
                                                           addition-extensional w₀ e₀ e₁ ,
                                                           addition-transitive t₀ t₁

\end{code}

Successor.

\begin{code}

module _ {U V} {X : U ̇} (_<_ : X → X → V ̇) where

  _<[𝟙]_ : 𝟙 → 𝟙 → V ̇
  _<[𝟙]_ = subsingleton-ordinal.order {U} 𝟙 𝟙-is-prop
  
  private _<'_ : X + 𝟙 → X + 𝟙 → V ̇
  _<'_ = addition _<_ _<[𝟙]_

  successor = _<'_

\end{code}

Multiplication



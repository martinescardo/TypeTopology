Martin Escardo, 21 March 2018

We prove the known (constructive) fact that

  X + 𝟙 ≃ Y + 𝟙 → X ≃ Y.

The proof may be new (or not).

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-FunExt
open import UF-Subsingletons-FunExt

module PlusOneLC (fe : ∀ U V → funext U V) where

_∖_ : ∀ {U} (X : U ̇) (a : X) → U ̇
X ∖ a = Σ \(x : X) → x ≢ a

add-and-remove-same-point : ∀ {U} {X : U ̇} →  X ≃ (X + 𝟙) ∖ (inr *)
add-and-remove-same-point {U} {X} = f , ((g , fg) , (g , gf))
 where
  f : X → (X + 𝟙) ∖ inr *
  f x = (inl x , λ ())
  g : (X + 𝟙) ∖ inr * → X
  g (inl x , u) = x
  g (inr * , u) = 𝟘-elim (u refl)
  fg : f ∘ g ∼ id
  fg (inl x , u) = to-Σ-≡'' (refl , neg-is-prop (fe U U₀) _ _)
  fg (inr * , u) = 𝟘-elim (u refl)
  gf : g ∘ f ∼ id
  gf x = refl

remove-points : ∀ {U} {V} {X : U ̇} {Y : V ̇} (f : X → Y) → qinv f → (a : X) → X ∖ a ≃ Y ∖ (f a)
remove-points {U} {V} {X} {Y} f (g , (gf , fg)) a = (f' , e')        
 where
  f' : X ∖ a → Y ∖ (f a)
  f' (x , u) = (f x , λ(p : f x ≡ f a) → u ((gf x)⁻¹ ∙ ap g p ∙ gf a))
  g' : Y ∖ (f a) → X ∖ a
  g' (y , v) = (g y , λ(p : g y ≡ a) → v ((fg y) ⁻¹ ∙ ap f p))
  gf' : g' ∘ f' ∼ id
  gf' (x , _) = to-Σ-≡'' (gf x , neg-is-prop (fe U U₀) _ _) 
  fg' : f' ∘ g' ∼ id
  fg' (y , _) = to-Σ-≡'' (fg y , neg-is-prop (fe V U₀) _ _)
  e' : is-equiv f'
  e' = qinv-is-equiv f' (g' , gf' , fg')

open import DiscreteAndSeparated

add-one-and-remove-isolated-point : ∀ {V} {Y : V ̇} (z : Y + 𝟙) → isolated z → ((Y + 𝟙) ∖ z) ≃ Y
add-one-and-remove-isolated-point {V} {Y} (inl b) i = (f , qinv-is-equiv f (g , gf , fg))
 where
  f : (Y + 𝟙) ∖ (inl b) → Y
  f (inl y , u) = y
  f (inr * , u) = b
  g' : (y : Y) → decidable (inl b ≡ inl y) → (Y + 𝟙) ∖ (inl b)
  g' y (inl p) = (inr * , λ ())
  g' y (inr u) = (inl y , contrapositive (λ p → p ⁻¹) u)
  g : Y → (Y + 𝟙) ∖ (inl b)
  g y = g' y (i (inl y))
  gf : g ∘ f ∼ id
  gf (inl y , u) = to-Σ-≡'' (p , neg-is-prop (fe V U₀) _ _)
   where
    φ : (p : inl b ≡ inl y) (q : i (inl y) ≡ inl p) → i (inl y) ≡ inr (≢-sym u)
    φ p q = 𝟘-elim (u (p ⁻¹))
    ψ : (v : inl b ≢ inl y) (q : i (inl y) ≡ inr v) → i (inl y) ≡ inr (≢-sym u)
    ψ v q = q ∙ ap inr (neg-is-prop (fe V U₀) _ _)
    h : i (inl y) ≡ inr (≢-sym u)
    h = equality-cases (i (inl y)) φ ψ
    p : pr₁(g' y (i (inl y))) ≡ inl y
    p = ap (pr₁ ∘ (g' y)) h
  gf (inr * , u) = equality-cases (i (inl b)) φ ψ
   where
    φ : (p : inl b ≡ inl b) → i (inl b) ≡ inl p → g (f (inr * , u)) ≡ (inr * , u)
    φ p q = r ∙ to-Σ-≡'' (refl , (neg-is-prop (fe V U₀) _ _))
     where
      r : g b ≡ (inr * , λ ())
      r = ap (g' b) q 
    ψ : (v : inl b ≢ inl b) → i (inl b) ≡ inr v → g (f (inr * , u)) ≡ (inr * , u)
    ψ v q = 𝟘-elim (v refl)
  fg : f ∘ g ∼ id
  fg y = equality-cases (i (inl y)) φ ψ
   where
    φ : (p : inl b ≡ inl y) → i (inl y) ≡ inl p → f (g' y (i (inl y))) ≡ y
    φ p q = ap (λ d → f (g' y d)) q ∙ inl-injective p
    ψ : (u : inl b ≢ inl y) → i (inl y) ≡ inr u → f (g' y (i (inl y))) ≡ y
    ψ _ = ap ((λ d → f (g' y d)))

add-one-and-remove-isolated-point {V} {Y} (inr *) _ = ≃-sym add-and-remove-same-point

+𝟙-cancellable : ∀ {U} {V} {X : U ̇} {Y : V ̇} → (X + 𝟙) ≃ (Y + 𝟙) → X ≃ Y
+𝟙-cancellable {U} {V} {X} {Y} (φ , e) =
   X                  ≃⟨ add-and-remove-same-point ⟩
  (X + 𝟙) ∖ inr *     ≃⟨ remove-points φ (is-equiv-qinv φ e) (inr *) ⟩
  (Y + 𝟙) ∖ φ (inr *) ≃⟨ add-one-and-remove-isolated-point
                              (φ (inr *))
                              (equivalences-preserve-isolatedness φ e (inr *) isolated-added-point) ⟩
   Y ■ 

\end{code}

\begin{code}

infix 2 _∖_

\end{code}

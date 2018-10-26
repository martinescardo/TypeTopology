Martin Escardo, 27 April 2014

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-PropIndexedPiSigma where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-Equiv

prop-indexed-product : funext U V → {X : U ̇} {Y : X → V ̇}
                     → is-prop X → (a : X) → Π Y ≃ Y a
prop-indexed-product {U} {V} fe {X} {Y} hp a = f , (g , fg) , (g , gf)
 where
  f : Π Y → Y a
  f φ = φ a
  g : Y a → Π Y
  g y x = transport Y (hp a x) y
  lemma : (x : X) → hp x x ≡ refl
  lemma x = prop-is-set hp (hp x x) refl
  fg : (y : Y a) → transport Y (hp a a) y ≡ y
  fg y = ap (λ - → transport Y - y) (lemma a)
  gf'' : (φ : Π Y) {x x' : X} → x ≡ x' → transport Y (hp x x') (φ x) ≡ φ x'
  gf'' t {x} refl = ap (λ - → transport Y - (t x)) (lemma x)
  gf' : (φ : Π Y) (x : X) → transport Y (hp a x) (φ a) ≡ φ x
  gf' φ x = gf'' φ (hp a x)
  gf : (φ : Π Y) → g(f φ) ≡ φ
  gf φ = dfunext fe (gf' φ)

prop-indexed-product-one : ∀ {T} → funext U V → {X : U ̇} {Y : X → V ̇} → (X → 𝟘 {W})
                         → Π Y ≃ 𝟙 {T}
prop-indexed-product-one {U} {V} {W} {T} fe {X} {Y} v = unique-to-𝟙 , (g , fg) , (g , gf)
 where
  g : 𝟙 {T} → Π Y
  g * x = unique-from-𝟘 {V} {W} (v x)
  fg : (u : 𝟙) → * ≡ u
  fg * = refl
  gf : (φ : Π Y) → g * ≡ φ
  gf φ = dfunext fe u
   where
    u : (x : X) → g (unique-to-𝟙 φ) x ≡ φ x
    u x = unique-from-𝟘 (v x)

\end{code}

Added 18th December 2017.

\begin{code}

prop-indexed-sum :{X : U ̇} {Y : X → V ̇}
                 → is-prop X → (a : X) → Σ Y ≃ Y a
prop-indexed-sum {U} {V} {X} {Y} hp a = f , (g , fg) , (g , gf)
 where
  f : Σ Y → Y a
  f (x , y) = transport Y (hp x a) y
  g : Y a → Σ Y
  g y = a , y
  lemma₁ : (x : X) → hp x x ≡ refl
  lemma₁ x = prop-is-set hp (hp x x) refl
  fg : (y : Y a) → f(a , y) ≡ y
  fg y = ap (λ - → transport Y - y) (lemma₁ a)
  lemma₂ : (x : X) (y : Y x) → x ≡ a → transport Y (hp a x) (f (x , y)) ≡ y
  lemma₂ _ y refl = fg (f (a , y)) ∙ fg y
  gf : (σ : Σ Y) → g(f σ) ≡ σ
  gf (x , y) = to-Σ-≡ (hp a x , lemma₂ x y (hp x a))

prop-indexed-sum-zero : {X : U ̇} {Y : X → V ̇} → (X → (𝟘 {W}))
                      → Σ Y ≃ (𝟘 {W})
prop-indexed-sum-zero {U} {V} {W} {X} {Y} φ = f , (g , fg) , (g , gf)
 where
  f : Σ Y → 𝟘 {W}
  f (x , y) = φ x
  g : 𝟘 → Σ Y
  g ()
  fg : (x : 𝟘) → f(g x) ≡ x
  fg x = 𝟘-elim x
  gf : (σ : Σ Y) → g(f σ) ≡ σ
  gf (x , y) = 𝟘-elim (φ x)

\end{code}

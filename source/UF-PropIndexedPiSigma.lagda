Martin Escardo, 27 April 2014

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-PropIndexedPiSigma where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-FunExt
open import UF-Equiv

prop-indexed-product : funext 𝓤 𝓥 → {X : 𝓤 ̇} {Y : X → 𝓥 ̇}
                     → is-prop X → (a : X) → Π Y ≃ Y a
prop-indexed-product {𝓤} {𝓥} fe {X} {Y} hp a = qinveq f (g , ε , η)
 where
  f : Π Y → Y a
  f φ = φ a
  g : Y a → Π Y
  g y x = transport Y (hp a x) y
  lemma : (x : X) → hp x x ≡ refl
  lemma x = props-are-sets hp (hp x x) refl
  η : (y : Y a) → transport Y (hp a a) y ≡ y
  η y = ap (λ - → transport Y - y) (lemma a)
  ε'' : (φ : Π Y) {x x' : X} → x ≡ x' → transport Y (hp x x') (φ x) ≡ φ x'
  ε'' t {x} refl = ap (λ - → transport Y - (t x)) (lemma x)
  ε' : (φ : Π Y) (x : X) → transport Y (hp a x) (φ a) ≡ φ x
  ε' φ x = ε'' φ (hp a x)
  ε : (φ : Π Y) → g(f φ) ≡ φ
  ε φ = dfunext fe (ε' φ)

prop-indexed-product-one : funext 𝓤 𝓥 → {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → (X → 𝟘 {𝓦})
                         → Π Y ≃ 𝟙 {𝓣}
prop-indexed-product-one {𝓤} {𝓥} {𝓦} {𝓣} fe {X} {Y} v = qinveq unique-to-𝟙 (g , ε , η)
 where
  g : 𝟙 → Π Y
  g * x = unique-from-𝟘 {𝓥} {𝓦} (v x)
  η : (u : 𝟙) → * ≡ u
  η * = refl
  ε : (φ : Π Y) → g * ≡ φ
  ε φ = dfunext fe u
   where
    u : (x : X) → g (unique-to-𝟙 φ) x ≡ φ x
    u x = unique-from-𝟘 (v x)

\end{code}

Added 18th December 2017.

\begin{code}

prop-indexed-sum :{X : 𝓤 ̇} {Y : X → 𝓥 ̇}
                 → is-prop X → (a : X) → Σ Y ≃ Y a
prop-indexed-sum {𝓤} {𝓥} {X} {Y} hp a = qinveq f (g , ε , η)
 where
  f : Σ Y → Y a
  f (x , y) = transport Y (hp x a) y
  g : Y a → Σ Y
  g y = a , y
  lemma₁ : (x : X) → hp x x ≡ refl
  lemma₁ x = props-are-sets hp (hp x x) refl
  η : (y : Y a) → f(a , y) ≡ y
  η y = ap (λ - → transport Y - y) (lemma₁ a)
  lemma₂ : (x : X) (y : Y x) → x ≡ a → transport Y (hp a x) (f (x , y)) ≡ y
  lemma₂ _ y refl = η (f (a , y)) ∙ η y
  ε : (σ : Σ Y) → g(f σ) ≡ σ
  ε (x , y) = to-Σ-≡ (hp a x , lemma₂ x y (hp x a))

prop-indexed-sum-zero : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → (X → 𝟘 {𝓦})
                      → Σ Y ≃ (𝟘 {𝓣})
prop-indexed-sum-zero {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} φ = qinveq f (g , ε , η)
 where
  f : Σ Y → 𝟘
  f (x , y) = 𝟘-elim(φ x)
  g : 𝟘 → Σ Y
  g ()
  η : (x : 𝟘) → f(g x) ≡ x
  η ()
  ε : (σ : Σ Y) → g(f σ) ≡ σ
  ε (x , y) = 𝟘-elim (φ x)

\end{code}

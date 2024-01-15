Martin Escardo, 27 April 2014

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.PropIndexedPiSigma where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-Properties


Π-proj : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } (a : X) → Π Y → Y a
Π-proj a f = f a

Π-inj : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ } → is-prop X → (a : X) → Y a → Π Y
Π-inj {𝓤} {𝓥} {X} {Y} i a y x = transport Y (i a x) y

Π-proj-is-equiv : funext 𝓤 𝓥
                → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                → is-prop X
                → (a : X) → is-equiv (Π-proj a)
Π-proj-is-equiv {𝓤} {𝓥} fe {X} {Y} i a = γ
 where
  l : (x : X) → i x x ＝ refl
  l x = props-are-sets i (i x x) refl

  η : (y : Y a) → transport Y (i a a) y ＝ y
  η y = ap (λ - → transport Y - y) (l a)

  ε'' : (f : Π Y) {x x' : X} → x ＝ x' → transport Y (i x x') (f x) ＝ f x'
  ε'' f {x} refl = ap (λ - → transport Y - (f x)) (l x)

  ε' : (f : Π Y) (x : X) → transport Y (i a x) (f a) ＝ f x
  ε' f x = ε'' f (i a x)

  ε : (f : Π Y) → Π-inj i a (Π-proj a f) ＝ f
  ε φ = dfunext fe (ε' φ)

  γ : is-equiv (Π-proj a)
  γ = qinvs-are-equivs (Π-proj a) (Π-inj i a , ε , η)

prop-indexed-product : funext 𝓤 𝓥
                     → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                     → is-prop X
                     → (a : X) → Π Y ≃ Y a
prop-indexed-product fe i a = Π-proj a , Π-proj-is-equiv fe i a

prop-indexed-product-one : funext 𝓤 𝓥
                         → {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                         → (X → 𝟘 {𝓦})
                         → Π Y ≃ 𝟙 {𝓣}
prop-indexed-product-one {𝓤} {𝓥} {𝓦} {𝓣} fe {X} {Y} v = γ
 where
  g : 𝟙 → Π Y
  g ⋆ x = unique-from-𝟘 {𝓥} {𝓦} (v x)

  η : (u : 𝟙) → ⋆ ＝ u
  η ⋆ = refl

  ε : (φ : Π Y) → g ⋆ ＝ φ
  ε φ = dfunext fe u
   where
    u : (x : X) → g (unique-to-𝟙 φ) x ＝ φ x
    u x = unique-from-𝟘 (v x)

  γ : Π Y ≃ 𝟙 {𝓣}
  γ = qinveq unique-to-𝟙 (g , ε , η)

\end{code}

Added 18th December 2017.

\begin{code}

prop-indexed-sum : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                 → is-prop X
                 → (a : X) → Σ Y ≃ Y a
prop-indexed-sum {𝓤} {𝓥} {X} {Y} i a = qinveq f (g , ε , η)
 where
  f : Σ Y → Y a
  f (x , y) = transport Y (i x a) y

  g : Y a → Σ Y
  g y = a , y

  l : (x : X) → i x x ＝ refl
  l x = props-are-sets i (i x x) refl

  η : (y : Y a) → f (a , y) ＝ y
  η y = ap (λ - → transport Y - y) (l a)

  c : (x : X) (y : Y x) → x ＝ a → transport Y (i a x) (f (x , y)) ＝ y
  c _ y refl = η (f (a , y)) ∙ η y

  ε : (σ : Σ Y) → g (f σ) ＝ σ
  ε (x , y) = to-Σ-＝ (i a x , c x y (i x a))

prop-indexed-sum-zero : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                      → (X → 𝟘 {𝓦})
                      → Σ Y ≃ (𝟘 {𝓣})
prop-indexed-sum-zero {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} φ = qinveq f (g , ε , η)
 where
  f : Σ Y → 𝟘
  f (x , y) = 𝟘-elim (φ x)

  g : 𝟘 → Σ Y
  g = unique-from-𝟘

  η : (x : 𝟘) → f (g x) ＝ x
  η = 𝟘-induction

  ε : (σ : Σ Y) → g (f σ) ＝ σ
  ε (x , y) = 𝟘-elim (φ x)

\end{code}

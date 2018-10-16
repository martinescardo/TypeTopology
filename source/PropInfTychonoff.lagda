Martin Escardo 28 July 2018

Adapted from the module PropTychnoff to take order into account.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT
open import UF-FunExt

module PropInfTychonoff (fe : ∀ U V → funext U V) where

open import Two
open import CompactTypes
open import InfCompact
open import Two-Prop-Density
open import UF-Base
open import UF-Subsingletons
open import UF-PropIndexedPiSigma
open import UF-Equiv
open import UF-EquivalenceExamples

prop-inf-tychonoff : ∀ {U V T} {X : U ̇} {Y : X → V ̇} → is-prop X
              → (_≺_ : {x : X} → Y x → Y x → T ̇)
              → ((x : X) → inf-compact(λ (y y' : Y x) → ¬(y' ≺ y)))
              → inf-compact (λ (φ γ : Π Y) → ¬ Σ \(x : X) → γ x ≺ φ x)
prop-inf-tychonoff {U} {V} {T} {X} {Y} hp _≺_ ε p =
 φ₀ , φ₀-is-conditional-root , a , b
 where
  _≼_ : {x : X} → Y x → Y x → T ̇
  y ≼ y' = ¬(y' ≺ y)

  _≤_ : Π Y → Π Y → U ⊔ T ̇
  φ ≤ γ = ¬ Σ \(x : X) → γ x ≺ φ x

  hip : (x : X) → Π Y ≃ Y x
  hip = prop-indexed-product (fe U V) hp

  h : (x : X) → Y x → Π Y
  h x = pr₁(pr₂(pr₂(hip x)))

  hf : (x : X) (φ : Π Y) → h x (φ x) ≡ φ
  hf x = pr₂(pr₂(pr₂(hip x)))

  q : (x : X) → Y x → 𝟚
  q x y = p (h x y)

  φ₀ : Π Y
  φ₀ x = pr₁(ε x (q x))

  cr : (x : X) → (Σ \(y : Y x) → p (h x y) ≡ ₀) → p (h x (φ₀ x)) ≡ ₀
  cr x = pr₁(pr₂(ε x (q x)))

  cr-particular-case : (x : X) → (Σ \(φ : Π Y) → p (h x (φ x)) ≡ ₀) → p (h x (φ₀ x)) ≡ ₀
  cr-particular-case x (φ , r) = cr x (φ x , r)

  φ₀-is-conditional-root-assuming-X : X → (Σ \(φ : Π Y) → p φ ≡ ₀) → p φ₀ ≡ ₀
  φ₀-is-conditional-root-assuming-X x (φ , r) = s ∙ t
   where
    s : p φ₀ ≡ p (h x (φ₀ x))
    s = ap p ((hf x φ₀)⁻¹)
    t : p (h x (φ₀ x)) ≡ ₀
    t = cr-particular-case x (φ , (ap p (hf x φ) ∙ r))

  φ₀-is-conditional-root-assuming-X-empty : ¬ X → (Σ \(φ : Π Y) → p φ ≡ ₀) → p φ₀ ≡ ₀
  φ₀-is-conditional-root-assuming-X-empty u (φ , r) = ap p c ∙ r
   where
    c : φ₀ ≡ φ
    c = dfunext (fe U V) (λ x → unique-from-𝟘(u x))

  c₀ : (Σ \(φ : Π Y) → p φ ≡ ₀) → X → p φ₀ ≡ ₀
  c₀ σ x = φ₀-is-conditional-root-assuming-X x σ

  C₁ : (Σ \(φ : Π Y) → p φ ≡ ₀) → p φ₀ ≡ ₁ → ¬ X
  C₁ σ = contrapositive(c₀ σ) ∘ Lemma[b≡₁→b≢₀]

  C₂ : (Σ \(φ : Π Y) → p φ ≡ ₀) → ¬ X → p φ₀ ≡ ₀
  C₂ σ u = φ₀-is-conditional-root-assuming-X-empty u σ

  C₃ : (Σ \(φ : Π Y) → p φ ≡ ₀) → p φ₀ ≡ ₁ → p φ₀ ≡ ₀
  C₃ σ = C₂ σ ∘ C₁ σ

  φ₀-is-conditional-root : (Σ \(φ : Π Y) → p φ ≡ ₀) → p φ₀ ≡ ₀
  φ₀-is-conditional-root σ = 𝟚-equality-cases id (C₃ σ)

  α : (x : X) → (y : Y x) → q x y ≡ ₀ → φ₀ x ≼ y
  α x = pr₁(pr₂(pr₂(ε x (q x))))

  β : (x : X) → (l : Y x) → root-lower-bound _≼_ (q x) l → l ≼ φ₀ x
  β x = pr₂(pr₂(pr₂(ε x (q x))))

  a : (φ : Π Y) → p φ ≡ ₀ → φ₀ ≤ φ
  a φ r (x , l) = α x (φ x) γ l
   where
    γ : p (h x (φ x)) ≡ ₀
    γ = ap p (hf x φ) ∙ r

  b : (l : Π Y) → root-lower-bound _≤_ p l → l ≤ φ₀
  b l u (x , m) = β x (l x) γ m
   where
    γ : (y : Y x) → p (h x y) ≡ ₀ → l x ≼ y
    γ y r n = u φ₀ g (x , m)
     where
      g : p φ₀ ≡ ₀
      g = φ₀-is-conditional-root (h x y , r)

\end{code}

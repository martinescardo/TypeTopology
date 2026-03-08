Ayberk Tosun, 28 February 2022.

This module was originally called `GaloisConnection.lagda`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt

module Locales.PosetalAdjunction
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
         where

open import Locales.Frame pt fe
open import UF.Logic
open import UF.SubtypeClassifier
open import UF.Subsingletons

open AllCombinators pt fe

\end{code}

\begin{code}

module PosetalAdjunctionBetween (P : Poset 𝓤 𝓥) (Q : Poset 𝓤' 𝓥') where

\end{code}

Definition of a pair of opposing monotonic maps forming an adjoint pair:

\begin{code}

 _⊣_ : (P ─m→ Q) → (Q ─m→ P) → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥')
 (f , _) ⊣ (g , _) = Ɐ x ꞉ ∣ P ∣ₚ , Ɐ y ꞉ ∣ Q ∣ₚ ,
                      (f x ≤[ Q ] y ⇒ x ≤[ P ] g y) ∧ (x ≤[ P ] g y ⇒ f x ≤[ Q ] y)

 has-right-adjoint : (P ─m→ Q) → 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
 has-right-adjoint f = Σ g ꞉ Q ─m→ P , (f ⊣ g) holds

 has-left-adjoint : (Q ─m→ P) → 𝓤 ⊔ 𝓥 ⊔ 𝓤' ⊔ 𝓥' ̇
 has-left-adjoint g = Σ f ꞉ P ─m→ Q , (f ⊣ g) holds

\end{code}

\begin{code}

 unit : (f : P ─m→ Q) (g : Q ─m→ P)
      → (f ⊣ g) holds
      → (x : ∣ P ∣ₚ)
      → (x ≤[ P ] (g .pr₁ ∘ f .pr₁) x) holds
 unit (f , _) g p x = pr₁ (p x (f x)) (≤-is-reflexive Q (f x))

 counit : (f⁺ : P ─m→ Q) (f₊ : Q ─m→ P)
        → (f⁺ ⊣ f₊) holds → (y : ∣ Q ∣ₚ) → ((f⁺ .pr₁ ∘ f₊ .pr₁) y ≤[ Q ] y) holds
 counit (f , _) (g , _) η y = pr₂ (η (g y) y) (≤-is-reflexive P (g y))

\end{code}

\begin{code}

 has-right-adjoint-is-prop : (f : P ─m→ Q)
                           → is-prop (Σ g ꞉ Q ─m→ P , ((f ⊣ g) holds))
 has-right-adjoint-is-prop 𝒻 (ℊ₁@(g₁ , _) , p₁) (ℊ₂@(g₂ , _) , p₂) =
  to-subtype-＝ υ (to-subtype-＝ ϕ (dfunext fe γ))
   where
    υ : (g : Q ─m→ P) → is-prop ((𝒻 ⊣ g) holds)
    υ ℊ = holds-is-prop (𝒻 ⊣ ℊ)

    ϕ : (ℊ : ∣ Q ∣ₚ → ∣ P ∣ₚ) → is-prop (is-monotonic Q P ℊ holds)
    ϕ = holds-is-prop ∘ is-monotonic Q P

    γ : g₁ ∼ g₂
    γ y = ≤-is-antisymmetric P α β
     where
      α : (g₁ y ≤[ P ] g₂ y) holds
      α = pr₁ (p₂ (g₁ y) y) (counit 𝒻 ℊ₁ p₁ y)

      β : ((g₂ y) ≤[ P ] (g₁ y)) holds
      β = pr₁ (p₁ (g₂ y) y) (counit 𝒻 ℊ₂ p₂ y)

 has-left-adjoint-is-prop : (g : Q ─m→ P)
                          → is-prop (Σ f ꞉ P ─m→ Q , (f ⊣ g) holds)
 has-left-adjoint-is-prop ℊ (𝒻₁@(f₁ , _) , p₁) (𝒻₂@(f₂ , _) , p₂) =
  to-subtype-＝ υ (to-subtype-＝ ϕ (dfunext fe γ))
   where
    υ : (𝒻 : P ─m→ Q) → is-prop ((𝒻 ⊣ ℊ) holds)
    υ 𝒻 = holds-is-prop (𝒻 ⊣ ℊ)

    ϕ : (f : ∣ P ∣ₚ → ∣ Q ∣ₚ) → is-prop (is-monotonic P Q f holds)
    ϕ = holds-is-prop ∘ is-monotonic P Q

    γ : f₁ ∼ f₂
    γ x = ≤-is-antisymmetric Q α β
     where
      α : (f₁ x ≤[ Q ] f₂ x) holds
      α = pr₂ (p₁ x (f₂ x)) (unit 𝒻₂ ℊ p₂ x)

      β : (f₂ x ≤[ Q ] f₁ x) holds
      β = pr₂ (p₂ x (f₁ x)) (unit 𝒻₁ ℊ p₁ x)

\end{code}

\begin{code}

 right-adjoints-are-unique : (f : P ─m→ Q) (g₁ g₂ : Q ─m→ P)
                           → (f ⊣ g₁) holds → (f ⊣ g₂) holds → g₁ ＝ g₂
 right-adjoints-are-unique f g₁ g₂ p₁ p₂ =
  pr₁ (from-Σ-＝ (has-right-adjoint-is-prop f (g₁ , p₁) (g₂ , p₂)))

 left-adjoints-are-unique : (f₁ f₂ : P ─m→ Q) (g : Q ─m→ P)
                          → (f₁ ⊣ g) holds → (f₂ ⊣ g) holds → f₁ ＝ f₂
 left-adjoints-are-unique f₁ f₂ g p₁ p₂ =
  pr₁ (from-Σ-＝ (has-left-adjoint-is-prop g (f₁ , p₁) (f₂ , p₂)))

\end{code}

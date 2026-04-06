Martin Escardo 28 July 2018

Adapted from the module TypeTopology.MicroTychnoff to take order into
account. The file MicrosTychonoff has many comments, but this one
doesn't.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt

module TypeTopology.MicroInfTychonoff (fe : FunExt) where

open import MLTT.Two-Properties
open import Ordinals.InfProperty
open import UF.Subsingletons
open import UF.PropIndexedPiSigma
open import UF.Equiv

micro-inf-tychonoff : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                    → is-prop X
                    → (_≺_ : {x : X} → Y x → Y x → 𝓦 ̇ )
                    → ((x : X) → has-inf (λ (y y' : Y x) → ¬ (y' ≺ y)))
                    → has-inf (λ (φ γ : Π Y) → ¬ (Σ x ꞉ X , γ x ≺ φ x))
micro-inf-tychonoff {𝓤} {𝓥} {𝓦} {X} {Y} X-is-prop _≺_ ε p =
 φ₀ , φ₀-is-conditional-root , a , b
 where
  _≼_ : {x : X} → Y x → Y x → 𝓦 ̇
  y ≼ y' = ¬ (y' ≺ y)

  _≤_ : Π Y → Π Y → 𝓤 ⊔ 𝓦 ̇
  φ ≤ γ = ¬ (Σ x ꞉ X , γ x ≺ φ x)

  𝕗 : (x : X) → Π Y ≃ Y x
  𝕗 x = prop-indexed-product x (fe 𝓤 𝓥) X-is-prop

  _ : (x : X) (φ : Π Y) → ⌜ 𝕗 x ⌝ φ ＝ φ x
  _ = λ x φ → refl

  f⁻¹ : (x : X) → Y x → Π Y
  f⁻¹ x = ⌜ 𝕗 x ⌝⁻¹

  q : (x : X) → Y x → 𝟚
  q x y = p (f⁻¹ x y)

  I : (x : X)
    → Σ y ꞉ Y x , is-conditional-root _≼_ (q x) y × is-roots-infimum _≼_ (q x) y
  I x = ε x (q x)

  φ₀ : Π Y
  φ₀ x = pr₁ (I x)

  II : (x : X) → (Σ y ꞉ Y x , q x y ＝ ₀) → q x (φ₀ x) ＝ ₀
  II x = pr₁ (pr₂ (I x))

  II' : (x : X) → (Σ φ ꞉ Π Y , p (f⁻¹ x (φ x)) ＝ ₀) → p (f⁻¹ x (φ₀ x)) ＝ ₀
  II' x (φ , r) = II x (φ x , r)

  α : (x : X) → (y : Y x) → q x y ＝ ₀ → φ₀ x ≼ y
  α x = pr₁ (pr₂ (pr₂ (I x)))

  β : (x : X) → (l : Y x) → is-roots-lower-bound _≼_ (q x) l → l ≼ φ₀ x
  β x = pr₂ (pr₂ (pr₂ (I x)))

  φ₀-is-conditional-root-assuming-X : X → (Σ φ ꞉ Π Y , p φ ＝ ₀) → p φ₀ ＝ ₀
  φ₀-is-conditional-root-assuming-X x (φ , r) =
    p φ₀             ＝⟨ a ⟩
    p (f⁻¹ x (φ₀ x)) ＝⟨ b ⟩
    ₀                ∎
     where
      a = ap p ((inverses-are-retractions' (𝕗 x) φ₀)⁻¹)
      b = II' x (φ , (ap p (inverses-are-retractions' (𝕗 x) φ) ∙ r))

  φ₀-is-conditional-root-assuming-X-empty
   : ¬ X → (Σ φ ꞉ Π Y , p φ ＝ ₀) → p φ₀ ＝ ₀
  φ₀-is-conditional-root-assuming-X-empty u (φ , r) =
   p φ₀ ＝⟨ ap p (dfunext (fe 𝓤 𝓥) (λ x → unique-from-𝟘 (u x))) ⟩
   p φ  ＝⟨ r ⟩
   ₀    ∎

  C₀ : (Σ φ ꞉ Π Y , p φ ＝ ₀) → X → p φ₀ ＝ ₀
  C₀ σ x = φ₀-is-conditional-root-assuming-X x σ

  C₁ : (Σ φ ꞉ Π Y , p φ ＝ ₀) → p φ₀ ＝ ₁ → ¬ X
  C₁ σ = contrapositive(C₀ σ) ∘ equal-₁-different-from-₀

  C₂ : (Σ φ ꞉ Π Y , p φ ＝ ₀) → ¬ X → p φ₀ ＝ ₀
  C₂ σ u = φ₀-is-conditional-root-assuming-X-empty u σ

  C₃ : (Σ φ ꞉ Π Y , p φ ＝ ₀) → p φ₀ ＝ ₁ → p φ₀ ＝ ₀
  C₃ σ = C₂ σ ∘ C₁ σ

  φ₀-is-conditional-root : (Σ φ ꞉ Π Y , p φ ＝ ₀) → p φ₀ ＝ ₀
  φ₀-is-conditional-root σ = 𝟚-equality-cases id (C₃ σ)

  a : (φ : Π Y) → p φ ＝ ₀ → φ₀ ≤ φ
  a φ r (x , l) = α x (φ x) γ l
   where
    γ : p (f⁻¹ x (φ x)) ＝ ₀
    γ = ap p (inverses-are-retractions' (𝕗 x) φ) ∙ r

  b : (l : Π Y) → is-roots-lower-bound _≤_ p l → l ≤ φ₀
  b l u (x , m) = β x (l x) γ m
   where
    γ : (y : Y x) → p (f⁻¹ x y) ＝ ₀ → l x ≼ y
    γ y r n = u φ₀ g (x , m)
     where
      g : p φ₀ ＝ ₀
      g = φ₀-is-conditional-root (f⁻¹ x y , r)

\end{code}

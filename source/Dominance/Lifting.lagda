Martin Escardo, January 2018, May 2020

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import Dominance.Definition
open import MLTT.Spartan

module Dominance.Lifting
        {𝓣 𝓚 : Universe}
        (d : 𝓣 ̇ → 𝓚 ̇ )
        (isd : is-dominance d)
       where

 D : Dominance
 D = (d , isd)

 L : ∀ {𝓥} (X : 𝓥 ̇ ) → 𝓣 ⁺ ⊔ 𝓚 ⊔ 𝓥 ̇
 L X = Σ P ꞉ 𝓣 ̇ , d P × (P → X)

 LL : ∀ {𝓥} (X : 𝓥 ̇ ) → 𝓣 ⁺ ⊔ 𝓚 ⊔ 𝓥 ̇
 LL X = L (L X)

 _⇀_ : ∀ {𝓥 𝓦} → 𝓥 ̇ → 𝓦 ̇ → 𝓣 ⁺ ⊔ 𝓚 ⊔ 𝓥 ⊔ 𝓦 ̇
 X ⇀ Y = X → L Y

 isDefined : ∀ {𝓥} {X : 𝓥 ̇ } → L X → 𝓣 ̇
 isDefined (P , (isdp , φ)) = P

 is-dominantisDefined : ∀ {𝓥} {X : 𝓥 ̇ } → (x̃ : L X) → is-dominant D (isDefined x̃)
 is-dominantisDefined (P , (isdp , φ)) = isdp

 value : ∀ {𝓥} {X : 𝓥 ̇ } → (x̃ : L X) → isDefined x̃ → X
 value (P , (isdp , φ)) = φ

 η : ∀ {𝓥} {X : 𝓥 ̇ } → X → L X
 η x = 𝟙 , 𝟙-is-dominant D , λ _ → x

 extension : ∀ {𝓥 𝓦} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } → (X ⇀ Y) → (L X → L Y)
 extension {𝓥} {𝓦} {X} {Y} f (P , (isdp , φ)) = (Q , (isdq , γ))
  where
   Q : 𝓣 ̇
   Q = Σ p ꞉ P , isDefined (f (φ p))

   isdq : is-dominant D Q
   isdq = dominant-closed-under-Σ D
            P
            (λ p → isDefined (f (φ p)))
            isdp
            (λ p → is-dominantisDefined (f (φ p)))

   γ : Q → Y
   γ (p , def) = value (f (φ p)) def

 _♯ : ∀ {𝓥 𝓦} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } → (X ⇀ Y) → (L X → L Y)
 f ♯ = extension f

 _◌_ : ∀ {𝓥 𝓦 𝓣} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } {Z : 𝓣 ̇ }
     → (Y ⇀ Z) → (X ⇀ Y) → (X ⇀ Z)
 g ◌ f = g ♯ ∘ f

 μ : ∀ {𝓥} {X : 𝓥 ̇ } → L (L X) → L X
 μ = extension id

 {- TODO:
 kleisli-law₀ : ∀ {𝓥} {X : 𝓥 ̇ } → extension (η {𝓥} {X}) ∼ id
 kleisli-law₀ {𝓥} {X} (P , (isdp , φ)) = {!!}

 kleisli-law₁ : ∀ {𝓥 𝓦)} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } (f : X ⇀ Y) → extension f ∘ η ∼ f
 kleisli-law₁ {𝓥} {𝓦} {X} {Y} f x = {!!}


 kleisli-law₂ : ∀ {𝓥 𝓦) T} {X : 𝓥 ̇ } {Y : 𝓦 ̇ } {Z : 𝓣 ̇ } (f : X ⇀ Y) (g : Y ⇀ Z)
              → (g ♯ ∘ f)♯ ∼ g ♯ ∘ f ♯
 kleisli-law₂ {𝓥} {𝓦} {𝓣} {X} {Y} {Z} f g (P , (isdp , φ)) = {!!}
 -}

\end{code}

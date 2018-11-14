LeftOvers from the past.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module LeftOvers where

KK : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
KK R X = (X → R) → R

K-functor : {R : 𝓤 ̇} {X : 𝓥 ̇} {Y : 𝓦 ̇} → (X → Y) → KK R X → KK R Y
K-functor = dual _ ∘ dual _

ηK : {R : 𝓤 ̇} {X : 𝓥 ̇} → X → KK R X
ηK x p = p x

K-unshift : {R : 𝓤 ̇} {X : 𝓥 ̇} {Y : X → 𝓦 ̇}
   → KK R ((x : X) → Y x) → (x : X) → KK R (Y x)
K-unshift = λ f x g → f(λ h → g(h x))

ku : {R : 𝓤 ̇} {X : 𝓥 ̇} {Y : 𝓦 ̇} → KK R (X × Y) → KK R X × KK R Y
ku φ = (K-functor pr₁ φ , K-functor pr₂ φ)

quant-prod : {X R : 𝓤 ̇} {Y : X → 𝓥 ̇}
    → KK R X → ((x : X)  → KK R (Y x)) → KK R ((Σ \(x : X)  → Y x))
quant-prod φ γ p = φ(λ x → γ x (λ y → p(x , y)))

JJ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
JJ R X = (X → R) → X

sel-prod : {R : 𝓤 ̇} {X : 𝓥 ̇} {Y : X → 𝓦 ̇}
         → JJ R X → ((x : X) → JJ R (Y x)) → JJ R (Σ \(x : X) → Y x)
sel-prod {𝓤} {𝓥} {𝓦} {R} {X} {Y} ε δ p = (x₀ , y₀)
   where
    next : (x : X) → Y x
    next x = δ x (λ y → p(x , y))
    x₀ : X
    x₀ = ε(λ x → p(x , next x))
    y₀ : Y x₀
    y₀ = next x₀

\end{code}

Alternative, equivalent, construction:

\begin{code}

overline : {R : 𝓤 ̇} {X : 𝓥 ̇} → JJ R X → KK R X
overline ε p = p(ε p)

sel-prod' : {R : 𝓤 ̇} {X : 𝓥 ̇} {Y : X → 𝓦 ̇}
          → JJ R X → ((x : X) → JJ R (Y x)) → JJ R (Σ \(x : X) → Y x)
sel-prod' {𝓤} {𝓥} {𝓦} {R} {X} {Y} ε δ p = (x₀ , y₀)
   where
    x₀ : X
    x₀ = ε(λ x → overline(δ x) (λ y → p(x , y)))
    y₀ : Y x₀
    y₀ = δ x₀ (λ y → p(x₀ , y))

\end{code}

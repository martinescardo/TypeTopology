LeftOvers from the past.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module LeftOvers where

KK : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
KK R X = (X → R) → R

K-functor : ∀ {U V W} {R : U ̇} {X : V ̇} {Y : W ̇} → (X → Y) → KK R X → KK R Y
K-functor = dual _ ∘ dual _

ηK : ∀ {U V} {R : U ̇} {X : V ̇} → X → KK R X
ηK x p = p x

K-unshift : ∀ {U V W} {R : U ̇} {X : V ̇} {Y : X → W ̇}
   → KK R ((x : X) → Y x) → (x : X) → KK R (Y x)
K-unshift = λ f x g → f(λ h → g(h x))

ku : ∀ {U V W} {R : U ̇} {X : V ̇} {Y : W ̇} → KK R (X × Y) → KK R X × KK R Y
ku φ = (K-functor pr₁ φ , K-functor pr₂ φ)

quant-prod : ∀ {U V} {X R : U ̇} {Y : X → V ̇}
    → KK R X → ((x : X)  → KK R (Y x)) → KK R ((Σ \(x : X)  → Y x))
quant-prod φ γ p = φ(λ x → γ x (λ y → p(x , y)))

JJ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
JJ R X = (X → R) → X

sel-prod : ∀ {U V W} {R : U ̇} {X : V ̇} {Y : X → W ̇}
         → JJ R X → ((x : X) → JJ R (Y x)) → JJ R (Σ \(x : X) → Y x)
sel-prod {U} {V} {W} {R} {X} {Y} ε δ p = (x₀ , y₀)
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

overline : ∀ {U V} {R : U ̇} {X : V ̇} → JJ R X → KK R X
overline ε p = p(ε p)

sel-prod' : ∀ {U V W} {R : U ̇} {X : V ̇} {Y : X → W ̇}
          → JJ R X → ((x : X) → JJ R (Y x)) → JJ R (Σ \(x : X) → Y x)
sel-prod' {U} {V} {W} {R} {X} {Y} ε δ p = (x₀ , y₀)
   where
    x₀ : X
    x₀ = ε(λ x → overline(δ x) (λ y → p(x , y)))
    y₀ : Y x₀
    y₀ = δ x₀ (λ y → p(x₀ , y))

\end{code}

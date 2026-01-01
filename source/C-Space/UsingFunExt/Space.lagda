Chuangjie Xu 2012 (updated in February 2015, ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module C-Space.UsingFunExt.Space where

open import MLTT.Spartan

open import C-Space.Preliminaries.Sequence
open import C-Space.UniformContinuity
open import C-Space.Coverage

\end{code}

Instead of working with whole category of sheaves over the above site, we
consider only those concrete sheaves which amount to the following C-spaces. To
topologize a set X, we use functions ₂ℕ → X, called probes, rather than subsets
of X, called open. Thus a topology on a set X, in our sense, is a set of maps
₂ℕ → X, called the probes, satisfying some conditions. We call it the C-topology.

\begin{code}

probe-axioms : (X : Set) → ((₂ℕ → X) → Set) → Set
probe-axioms X P =
    (∀(x : X) → (λ α → x) ∈ P)
  × (∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → X) → p ∈ P → p ∘ t ∈ P)
  × (∀(p : ₂ℕ → X) → (Σ \(n : ℕ) → ∀(s : ₂Fin n) → (p ∘ (cons s)) ∈ P) → p ∈ P)

TopologyOn : Set → Set₁
TopologyOn X = Σ \(P : (₂ℕ → X) → Set) → probe-axioms X P

Space : Set₁
Space = Σ \(X : Set) → TopologyOn X

U : Space → Set
U = pr₁

Probe : (X : Space) → (₂ℕ → U X) → Set
Probe X = pr₁ (pr₂ X)

cond₀ : (X : Space) →
        ∀(x : U X) → (λ α → x) ∈ Probe X
cond₀ (_ , _ , c₀ , _) = c₀

cond₁ : (X : Space) →
        ∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → U X) → p ∈ Probe X →
        p ∘ t ∈ Probe X
cond₁ (_ , _ , _ , c₁ , _) = c₁

cond₂ : (X : Space) →
        ∀(p : ₂ℕ → U X) → (Σ \(n : ℕ) → ∀(s : ₂Fin n) → p ∘ (cons s) ∈ Probe X) →
        p ∈ Probe X
cond₂ (_ , _ , _ , _ , c₂) = c₂

\end{code}

Then we define continuous functions between spaces and show that they do form a
category.

\begin{code}

continuous : (X Y : Space) → (U X → U Y) → Set
continuous X Y f = ∀ p → p ∈ Probe X → f ∘ p ∈ Probe Y

Map : Space → Space → Set
Map X Y = Σ \(f : U X → U Y) → continuous X Y f

Mapto : (Y : Space) → Set₁
Mapto Y = Σ \(X : Space) → Map X Y

id-is-continuous : ∀{X : Space} → continuous X X id
id-is-continuous p pinP = pinP

∘-preserves-continuity : (X Y Z : Space) →
    ∀(f : U X → U Y) → continuous X Y f →
    ∀(g : U Y → U Z) → continuous Y Z g →
    continuous X Z (g ∘ f)
∘-preserves-continuity X Y Z f cf g cg p pP = cg (f ∘ p) (cf p pP)

continuous-constant : (X Y : Space) → U Y → Map X Y
continuous-constant X Y y = (λ _ → y) , (λ _ _ → cond₀ Y y)

⟪_,_,_⟫_○_ : (X Y Z : Space) → Map Y Z → Map X Y → Map X Z
⟪ X , Y , Z ⟫ (g , cg) ○ (f , cf) = (g ∘ f) , λ p pP → cg (f ∘ p) (cf p pP)

\end{code}

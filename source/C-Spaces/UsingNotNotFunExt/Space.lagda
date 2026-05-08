Chuangjie Xu 2013 (updated in February 2015, ported to TypeTopology in 2025)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module C-Spaces.UsingNotNotFunExt.Space where

open import MLTT.Spartan

open import C-Spaces.Preliminaries.Sequence
open import C-Spaces.Coverage

\end{code}

C-topologies and C-spaces

\begin{code}

probe-axioms : (X : Set) → ((₂ℕ → X) → Set) → Set
probe-axioms X P =
    (∀(x : X) → (λ α → x) ∈ P)
  × (∀(t : ₂ℕ → ₂ℕ) → t ∈ C → ∀(p : ₂ℕ → X) → p ∈ P → p ∘ t ∈ P)
  × (∀(p : ₂ℕ → X) → (Σ n ꞉ ℕ , ∀(s : ₂Fin n) → p ∘ cons s ∈ P) → p ∈ P)
  × (∀(p q : ₂ℕ → X) → p ∈ P → (∀ α → ¬¬ (p α ＝ q α)) → q ∈ P)

TopologyOn : Set → Set₁
TopologyOn X = Σ P ꞉ ((₂ℕ → X) → Set) , probe-axioms X P

Space : Set₁
Space = Σ X ꞉ Set , TopologyOn X

U : Space → Set
U = pr₁

Probe : (X : Space) → (₂ℕ → U X) → Set
Probe X = pr₁ (pr₂ X)

cond₀ : (X : Space) →
        ∀ x → (λ α → x) ∈ Probe X
cond₀ (_ , _ , c₀ , _) = c₀

cond₁ : (X : Space) →
        ∀ t → t ∈ C → ∀ p → p ∈ Probe X →
        p ∘ t ∈ Probe X
cond₁ (_ , _ , _ , c₁ , _) = c₁

cond₂ : (X : Space) →
        ∀ p → (Σ n ꞉ ℕ , ∀(s : ₂Fin n) → p ∘ cons s ∈ Probe X) →
        p ∈ Probe X
cond₂ (_ , _ , _ , _ , c₂ , _) = c₂

cond₃ : (X : Space) →
        ∀ p q → p ∈ Probe X → (∀ α → ¬¬ (p α ＝ q α)) →
        q ∈ Probe X
cond₃ (_ , _ , _ , _ , _ , c₃) = c₃

cond₃' : (X : Space) →
         ∀ p q → p ∈ Probe X → p ∼ q →
         q ∈ Probe X
cond₃' X p q pX e = cond₃ X p q pX (λ α → ¬¬-intro (e α))

\end{code}

Continuous maps

\begin{code}

continuous : (X Y : Space) → (U X → U Y) → Set
continuous X Y f = ∀ p → p ∈ Probe X → f ∘ p ∈ Probe Y

Map : Space → Space → Set
Map X Y = Σ f ꞉ (U X → U Y) , continuous X Y f

id-is-continuous : ∀{X : Space} → continuous X X id
id-is-continuous p pinP = pinP

∘-preserves-continuity : (X Y Z : Space) →
    ∀(f : U X → U Y) → continuous X Y f →
    ∀(g : U Y → U Z) → continuous Y Z g →
    continuous X Z (g ∘ f)
∘-preserves-continuity X Y Z f cf g cg p pP = cg (f ∘ p) (cf p pP)

continuous-constant : (X Y : Space) → U Y → Map X Y
continuous-constant X Y y = (λ _ → y) , (λ _ _ → cond₀ Y y)

\end{code}

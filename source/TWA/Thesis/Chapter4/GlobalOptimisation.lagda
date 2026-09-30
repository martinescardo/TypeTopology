Todd Waugh Ambridge, January 2024

# Global optimisation

\begin{code}
{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import Fin.Type
open import Fin.Bishop


module TWA.Thesis.Chapter4.GlobalOptimisation (fe : FunExt) where

open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter4.ApproxOrder fe
\end{code}

## Absolute global optimisation

\begin{code}
is-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (_≤_ : Y → Y → 𝓦 ̇ )
                  → (X → Y) → X → 𝓤 ⊔ 𝓦 ̇
is-global-minimal {𝓤} {𝓥} {𝓦'} {X} _≤_ f x₀ = (x : X) → f x₀ ≤ f x

has-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (_≤_ : Y → Y → 𝓦 ̇ )
                   → (X → Y) → 𝓤 ⊔ 𝓦 ̇
has-global-minimal f = Σ ∘ (is-global-minimal f)

Fin-global-minimal : (n : ℕ) → Fin n → {Y : 𝓤 ̇ }
                 → (_≤_ : Y → Y → 𝓦 ̇ )
                 → is-linear-preorder _≤_
                 → (f : Fin n → Y)
                 → has-global-minimal _≤_ f
Fin-global-minimal 0 i       _≤_ l       f = 𝟘-elim i
Fin-global-minimal 1 (suc i) _≤_ l       f = 𝟘-elim i
Fin-global-minimal 1 𝟎 _≤_ (p , _) f = 𝟎 , γ
 where
  γ : is-global-minimal _≤_ f 𝟎
  γ 𝟎       = ≤-refl⟨ p ⟩ (f 𝟎)
  γ (suc i) = 𝟘-elim i
Fin-global-minimal (succ (succ n)) x _≤_ l@(p , _) f
 with Fin-global-minimal (succ n) 𝟎 _≤_ l (f ∘ suc)
... | (x'₀ , m) = Cases (≤-linear⟨ l ⟩ (f (suc x'₀)) (f 𝟎)) γ₁ γ₂
 where
  γ₁ : f (suc x'₀) ≤ f 𝟎 → has-global-minimal _≤_ f
  γ₁ x'₀≤𝟎 = suc x'₀ , γ
   where
    γ : (x : Fin (succ (succ n))) → f (suc x'₀) ≤ f x
    γ 𝟎 = x'₀≤𝟎
    γ (suc x) = m x
  γ₂ : f 𝟎 ≤ f (suc x'₀) → has-global-minimal _≤_ f
  γ₂ 𝟎≤x'₀ = 𝟎 , γ
   where
    γ : (x : Fin (succ (succ n))) → f 𝟎 ≤ f x
    γ 𝟎 = ≤-refl⟨ p ⟩ (f 𝟎)
    γ (suc x)
     = ≤-trans⟨ p ⟩ (f 𝟎) (f (suc x'₀)) (f (suc x)) 𝟎≤x'₀ (m x)

finite-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                      → X → finite-linear-order X
                      → (_≤_ : Y → Y → 𝓦 ̇ )
                      → is-linear-preorder _≤_
                      → (f : X → Y)
                      → has-global-minimal _≤_ f
finite-global-minimal x (n , e@(g , _ , (h , μ))) _≤_ l f
 = h x₀ , λ x → transport (f (h x₀) ≤_) (ap f (μ x)) (γ₀ (g x))
 where
 γ : has-global-minimal _≤_ (f ∘ h)
 γ = Fin-global-minimal n (g x) _≤_ l (f ∘ h)
 x₀ : Fin n
 x₀ = pr₁ γ
 γ₀ : is-global-minimal _≤_ (f ∘ h) x₀
 γ₀ = pr₂ γ
\end{code}

## Approximate global optimisation

\begin{code}
is_global-minimal : ℕ → {𝓤 𝓥 : Universe}
                  → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → (_≤ⁿ_ : Y → Y → ℕ → 𝓦 ̇ )
                  → (f : X → Y) → X → 𝓦 ⊔ 𝓤 ̇
(is ϵ global-minimal) {𝓤} {𝓥} {X} _≤ⁿ_ f x₀
 = (x : X) → (f x₀ ≤ⁿ f x) ϵ

has_global-minimal : ℕ → {𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
                   → {Y : 𝓥 ̇ }
                   → (_≤ⁿ_ : Y → Y → ℕ → 𝓦 ̇ )
                   → (f : X → Y) → (𝓦 ⊔ 𝓤) ̇
(has ϵ global-minimal) {𝓤} {𝓥} {𝓦} {X} _≤ⁿ_ f
 = Σ ((is ϵ global-minimal) {𝓤} {𝓥} {𝓦} {X} _≤ⁿ_ f)

F-ϵ-global-minimal : {X : 𝓤 ̇ } (Y : ClosenessSpace 𝓥)
                   → X → finite-linear-order X
                   → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦' ̇ )
                   → is-approx-order Y _≤ⁿ_
                   → (ϵ : ℕ) → (f : X → ⟨ Y ⟩)
                   → (has ϵ global-minimal) _≤ⁿ_ f
F-ϵ-global-minimal Y x l _≤ⁿ_ a ϵ
 = finite-global-minimal x l (λ x y → (x ≤ⁿ y) ϵ) (≤ⁿ-all-linear Y a ϵ)
\end{code}

## Global optimisation theorem

\begin{code}
cover-continuity-lemma
 : (X : ClosenessSpace 𝓤) {X' : 𝓤' ̇ } (Y : ClosenessSpace 𝓥)
 → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦' ̇ )
 → is-approx-order Y _≤ⁿ_
 → (ϵ : ℕ) → (f : ⟨ X ⟩ → ⟨ Y ⟩) (ϕ : f-ucontinuous X Y f)
 → let δ = pr₁ (ϕ ϵ) in (((g , _) , _) : X' is δ net-of X)
 → finite-linear-order X'
 → (x : ⟨ X ⟩) → Σ x' ꞉ X' , (f (g x') ≤ⁿ f x) ϵ
cover-continuity-lemma
 X Y _≤ⁿ_ a ϵ f ϕ ((g , h , η) , _) e x
 = h x
 , ≤ⁿ-close Y a ϵ (f (g (h x))) (f x)
     (C-sym Y ϵ (f x) (f (g (h x)))
       (pr₂ (ϕ ϵ) x (g (h x))
         (η x)))

global-opt : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
           → ⟨ X ⟩
           → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦' ̇ )
           → is-approx-order Y _≤ⁿ_
           → (ϵ : ℕ)
           → (f : ⟨ X ⟩ → ⟨ Y ⟩) (ϕ : f-ucontinuous X Y f)
           → totally-bounded X 𝓤'
           → (has ϵ global-minimal) _≤ⁿ_ f
global-opt {𝓤} {𝓥} {𝓦'} {𝓤'} X Y x₁ _≤ⁿ_ a ϵ f ϕ t
 = (g x'₀)
 , (λ x → ≤ⁿ-trans Y a ϵ
            (f (g x'₀)) (f (g (h x))) (f x)
            (m (h x)) (h-min x))
 where
  δ : ℕ
  δ = pr₁ (ϕ ϵ)
  X' : 𝓤' ̇
  X' =  pr₁ (t δ)
  X'-is-δ-net : X' is δ net-of X
  X'-is-δ-net  = pr₂ (t δ)
  X'-is-finite : finite-linear-order X'
  X'-is-finite = pr₂ X'-is-δ-net
  g :   X'  → ⟨ X ⟩
  g = pr₁ (pr₁ X'-is-δ-net)
  h : ⟨ X ⟩ →   X'
  h = pr₁ (pr₂ (pr₁ X'-is-δ-net))
  η : (x : ⟨ X ⟩) → Σ x' ꞉ X' , (f (g x') ≤ⁿ f x) ϵ
  η = cover-continuity-lemma X Y _≤ⁿ_
        a ϵ f ϕ X'-is-δ-net X'-is-finite
  h-min : (x : ⟨ X ⟩) → (f (g (h x)) ≤ⁿ f x) ϵ
  h-min x = pr₂ (η x)
  first  : has ϵ global-minimal _≤ⁿ_ (f ∘ g)
  first
   = F-ϵ-global-minimal Y (h x₁) X'-is-finite _≤ⁿ_ a ϵ (f ∘ g)
  x'₀ : X'
  x'₀ = pr₁ first
  m  : is ϵ global-minimal _≤ⁿ_ (f ∘ g) x'₀
  m  = pr₂ first
\end{code}

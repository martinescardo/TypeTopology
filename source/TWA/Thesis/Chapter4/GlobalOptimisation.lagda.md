```agda

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt

open import TWA.Thesis.Chapter2.FiniteDiscrete

module TWA.Thesis.Chapter4.GlobalOptimisation (fe : FunExt) where

open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter4.ApproxOrder fe

-- Definition 4.1.18
is-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (_≤_ : Y → Y → 𝓦 ̇ )
                  → (X → Y) → X → 𝓤 ⊔ 𝓦  ̇
is-global-minimal {𝓤} {𝓥} {𝓦'} {X} _≤_ f x₀ = (x : X) → f x₀ ≤ f x

has-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (_≤_ : Y → Y → 𝓦 ̇ )
                   → (X → Y) → 𝓤 ⊔ 𝓦  ̇
has-global-minimal f = Σ ∘ (is-global-minimal f)

-- Lemma 4.1.19
𝔽-global-minimal : (n : ℕ) → 𝔽 n → {Y : 𝓤 ̇ }
                 → (_≤_ : Y → Y → 𝓦 ̇ )
                 → is-linear-order _≤_
                 → (f : 𝔽 n → Y)
                 → has-global-minimal _≤_ f
𝔽-global-minimal 1 (inl ⋆) _≤_ l f = inl ⋆ , γ
 where
  ≤𝔽-refl = (pr₁ ∘ pr₁) l
  γ : is-global-minimal _≤_ f (inl ⋆)
  γ (inl ⋆) = ≤𝔽-refl (f (inl ⋆))
𝔽-global-minimal (succ (succ n)) x _≤_ l f
 with 𝔽-global-minimal (succ n) (inl ⋆) _≤_ l (f ∘ inr)
... | (x'₀ , m) = Cases (≤𝔽-linear (f (inr x'₀)) (f (inl ⋆))) γ₁ γ₂
 where
  ≤𝔽-linear = pr₂ l
  ≤𝔽-refl = (pr₁ ∘ pr₁) l
  ≤𝔽-trans = (pr₁ ∘ pr₂ ∘ pr₁) l
  γ₁ : f (inr x'₀) ≤ f (inl ⋆  ) → has-global-minimal _≤_ f
  γ₁ x'₀≤⋆ = inr x'₀ , γ
   where
    γ : (x : 𝔽 (succ (succ n))) → f (inr x'₀) ≤ f x
    γ (inl ⋆) = x'₀≤⋆
    γ (inr x) = m x
  γ₂ : f (inl ⋆  ) ≤ f (inr x'₀) → has-global-minimal _≤_ f
  γ₂ ⋆≤x'₀ = inl ⋆ , γ
   where
    γ : (x : 𝔽 (succ (succ n))) → f (inl ⋆) ≤ f x
    γ (inl ⋆) = ≤𝔽-refl  (f (inl ⋆))
    γ (inr x) = ≤𝔽-trans (f (inl ⋆)) (f (inr x'₀)) (f (inr x))
                  ⋆≤x'₀ (m x)

finite-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥  ̇ }
                      → X → finite-discrete X
                      → (_≤_ : Y → Y → 𝓦 ̇ )
                      → is-linear-order _≤_
                      → (f : X → Y)
                      → has-global-minimal _≤_ f
finite-global-minimal x (0 , (_ , (h , _) , _)) _≤_ l f
 = 𝟘-elim (h x)
finite-global-minimal x (succ n , e@(g , (h , η) , _)) _≤_ l f
 with 𝔽-global-minimal (succ n) (inl ⋆) _≤_ l (f ∘ g)
... | (x₀ , γ₀) = g x₀
                , λ x → transport (f (g x₀) ≤_) (ap f (η x)) (γ₀ (h x))

-- Definition 4.1.20
-- COMMENT: Maybe prove that if the set of minima is a proposition
-- then there exists a minimum
is_global-minimal : ℕ → {𝓤 𝓥 : Universe}
                  → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → (_≤ⁿ_ : Y → Y → ℕ → 𝓦 ̇ )
                  → (f : X → Y) → X → 𝓦 ⊔ 𝓤  ̇ 
(is ϵ global-minimal) {𝓤} {𝓥} {X} _≤ⁿ_ f x₀
 = (x : X) → (f x₀ ≤ⁿ f x) ϵ

has_global-minimal : ℕ → {𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
                   → {Y : 𝓥 ̇ }
                   → (_≤ⁿ_ : Y → Y → ℕ → 𝓦 ̇ )
                   → (f : X → Y) → (𝓦 ⊔ 𝓤) ̇ 
(has ϵ global-minimal) {𝓤} {𝓥} {𝓦} {X} _≤ⁿ_ f
 = Σ ((is ϵ global-minimal) {𝓤} {𝓥} {𝓦} {X} _≤ⁿ_ f)

-- Lemma 4.1.21
𝔽-ϵ-global-minimal : (n : ℕ) → 𝔽 n
                   → (Y : ClosenessSpace 𝓥)
                   → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦'  ̇ )
                   → is-approx-order' Y _≤ⁿ_
                   → (ϵ : ℕ) → (f : 𝔽 n → ⟨ Y ⟩)
                   → (has ϵ global-minimal) _≤ⁿ_ f
𝔽-ϵ-global-minimal 1 (inl ⋆) Y _≤ⁿ_ a ϵ f
 = inl ⋆ , γ
 where
  γ : is ϵ global-minimal _≤ⁿ_ f (inl ⋆)
  γ (inl ⋆) = ≤ⁿ-refl Y a ϵ (f (inl ⋆)) 
𝔽-ϵ-global-minimal (succ (succ n)) _ Y _≤ⁿ_ a ϵ f 
 with 𝔽-ϵ-global-minimal (succ n) (inl ⋆) Y _≤ⁿ_ a ϵ (f ∘ inr) 
... | (x₀ , m)
 = Cases (≤ⁿ-linear Y a ϵ (f (inr x₀)) (f (inl ⋆)))
     γ₁ γ₂
 where
  γ₁ : (f (inr x₀) ≤ⁿ f (inl ⋆)) ϵ → has ϵ global-minimal _≤ⁿ_ f
  γ₁ x₀≤⋆ = inr x₀ , γ
   where
    γ : is ϵ global-minimal _≤ⁿ_ f (inr x₀)
    γ (inl ⋆) = x₀≤⋆
    γ (inr x) = m x
  γ₂ : (f (inl ⋆) ≤ⁿ f (inr x₀)) ϵ → has ϵ global-minimal _≤ⁿ_ f
  γ₂ ⋆≤x₀ = inl ⋆ , γ
   where
    γ : is ϵ global-minimal _≤ⁿ_ f (inl ⋆)
    γ (inl ⋆) = ≤ⁿ-refl Y a ϵ (f (inl ⋆))
    γ (inr x) = ≤ⁿ-trans Y a ϵ
                  (f (inl ⋆)) (f (inr x₀)) (f (inr x))
                  ⋆≤x₀ (m x)

{-
𝔽-ϵ-global-minimal : (n : ℕ) → 𝔽 n
                   → (Y : ClosenessSpace 𝓥)
                   → (_≤_  : ⟨ Y ⟩ → ⟨ Y ⟩ → 𝓦 ̇ )
                   → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦'  ̇ )
                   → is-approx-order Y _≤_ _≤ⁿ_
                   → (ϵ : ℕ) → (f : 𝔽 n → ⟨ Y ⟩)
                   → (has ϵ global-minimal) _≤ⁿ_ f
𝔽-ϵ-global-minimal 1 (inl ⋆) Y _≤_ _≤ⁿ_ a ϵ f
 = inl ⋆ , γ
 where
  γ : is ϵ global-minimal _≤ⁿ_ f (inl ⋆)
  γ (inl ⋆) = ≤ⁿ-refl Y a ϵ (f (inl ⋆)) 
𝔽-ϵ-global-minimal (succ (succ n)) _ Y _≤_ _≤ⁿ_ a ϵ f 
 with 𝔽-ϵ-global-minimal (succ n) (inl ⋆) Y _≤_ _≤ⁿ_ a ϵ (f ∘ inr) 
... | (x₀ , m)
 = Cases (≤ⁿ-linear Y a ϵ (f (inr x₀)) (f (inl ⋆)))
     γ₁ γ₂
 where
  γ₁ : (f (inr x₀) ≤ⁿ f (inl ⋆)) ϵ → has ϵ global-minimal _≤ⁿ_ f
  γ₁ x₀≤⋆ = inr x₀ , γ
   where
    γ : is ϵ global-minimal _≤ⁿ_ f (inr x₀)
    γ (inl ⋆) = x₀≤⋆
    γ (inr x) = m x
  γ₂ : (f (inl ⋆) ≤ⁿ f (inr x₀)) ϵ → has ϵ global-minimal _≤ⁿ_ f
  γ₂ ⋆≤x₀ = inl ⋆ , γ
   where
    γ : is ϵ global-minimal _≤ⁿ_ f (inl ⋆)
    γ (inl ⋆) = ≤ⁿ-refl Y a ϵ (f (inl ⋆))
    γ (inr x) = ≤ⁿ-trans Y a ϵ
                  (f (inl ⋆)) (f (inr x₀)) (f (inr x))
                  ⋆≤x₀ (m x) -}

F-ϵ-global-minimal : {X : 𝓤 ̇ } (Y : ClosenessSpace 𝓥)
                   → X → finite-discrete X
                   → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦'  ̇ )
                   → is-approx-order' Y _≤ⁿ_
                   → (ϵ : ℕ) → (f : X → ⟨ Y ⟩)
                   → (has ϵ global-minimal) _≤ⁿ_ f
F-ϵ-global-minimal Y x (n , (g , (h , η) , _)) _≤ⁿ_ a ϵ f
 with 𝔽-ϵ-global-minimal n (h x) Y _≤ⁿ_ a ϵ (f ∘ g)
... | (x₀ , m)
 = g x₀
 , λ x → transport (λ - → (f (g x₀) ≤ⁿ f -) ϵ) (η x) (m (h x))

-- Lemma 4.1.23

cover-continuity-lemma
 : (X : ClosenessSpace 𝓤) {X' : 𝓤' ̇ } (Y : ClosenessSpace 𝓥)
 → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦'  ̇ )
 → is-approx-order' Y _≤ⁿ_
 → (ϵ : ℕ) → (f : ⟨ X ⟩ → ⟨ Y ⟩) (ϕ : f-ucontinuous X Y f)
 → let δ = pr₁ (ϕ ϵ) in (((g , _) , _) : X' is δ net-of X)
 → finite-discrete X'
 → (x : ⟨ X ⟩) → Σ x' ꞉ X' , (f (g x') ≤ⁿ f x) ϵ
cover-continuity-lemma
 X Y _≤ⁿ_ a ϵ f ϕ ((g , h , η) , _) e x
 = h x
 , ≤ⁿ-close Y a ϵ (f (g (h x))) (f x)
     (C-sym Y ϵ (f x) (f (g (h x)))
       (pr₂ (ϕ ϵ) x (g (h x))
         (η x)))
         
-- Theorem 4.1.22

global-opt : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
           → ⟨ X ⟩
           → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦'  ̇ )
           → is-approx-order' Y _≤ⁿ_
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
  X' : 𝓤'  ̇
  X' =  pr₁ (t δ)
  X'-is-δ-net : X' is δ net-of X
  X'-is-δ-net  = pr₂ (t δ)
  X'-is-finite : finite-discrete X'
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

```

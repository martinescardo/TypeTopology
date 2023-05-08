\begin{code}

{-# OPTIONS --without-K --exact-split
            --no-sized-types --no-guardedness --auto-inline
            --allow-unsolved-metas #-}

open import MLTT.Spartan
open import UF.FunExt
open import NotionsOfDecidability.Complemented
open import TypeTopology.DiscreteAndSeparated
-- open import Notation.Order
open import Naturals.Order
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient
open import UF.Miscelanea
open import MLTT.Two-Properties
open import UF.Equiv

module Thesis.GlobalOptimisatio (fe : FunExt) where

open import Thesis.SearchableTypes fe

-- Definition 4.1.4
record ordered (X : 𝓤 ̇ ) (𝓦' : Universe) : 𝓤 ⊔ 𝓦' ⁺  ̇ where
 field
  _≤_ : X → X → Ω 𝓦'
 _≤'_ = λ x y → (x ≤ y) holds
 field
  reflex  : (x     : X) →    x ≤' x
  trans   : (x y z : X) →    x ≤' y  → y ≤' z → x ≤' z
  antisym : (x y   : X) → ¬ (x ≤' y) → y ≤' x
  
open ordered hiding (_≤_)

-- Definition 4.1.5
totally-ordered : {X : 𝓤 ̇ } → ordered X 𝓦' → 𝓤 ⊔ 𝓦' ̇
totally-ordered {𝓤} {𝓦'} {X} o
 = (x y : X) → decidable (x ≤ y)
 where _≤_ = _≤'_ o

-- Definition 4.1.6
order-preserving : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → ordered X 𝓦' → ordered Y 𝓥'
                 → (f : X → Y) → 𝓤 ⊔ 𝓦' ⊔ 𝓥' ̇
order-preserving {𝓤} {𝓥} {𝓦'} {𝓥'} {X} {Y} ox oy f
 = (x₁ x₂ : X) → x₁ ≤x x₂ → f x₁ ≤y f x₂ 
 where
  _≤x_ = _≤'_ ox
  _≤y_ = _≤'_ oy

-- Lemma 4.1.7 [ TODO ]

-- Lemma 4.1.8 [ Should be a definition ]
has-minimal : {X : 𝓤 ̇ } → ordered X 𝓦' → 𝓤 ⊔ 𝓦'  ̇
has-minimal {𝓤} {𝓦'} {X} o = Σ x₀ ꞉ X , ((x : X) → x₀ ≤ x)
 where _≤_ = _≤'_ o

-- Lemma 4.1.9
-- [ TODO paper needs the below? ]
→-ordered : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (Y → X)
          → ordered X 𝓦' → ordered Y 𝓦'
ordered._≤_ (→-ordered f o) x y = f x ≤ f y
 where open ordered o
reflex  (→-ordered f o) x     = reflex  o (f x)
trans   (→-ordered f o) x y z = trans   o (f x) (f y) (f z)
antisym (→-ordered f o) x y   = antisym o (f x) (f y)

→-totally-ordered : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : Y → X)
                  → (o : ordered X 𝓦') → totally-ordered o
                  → totally-ordered (→-ordered f o)
→-totally-ordered f o t x y = t (f x) (f y)

-- [ TODO paper needs inhabited requirement ]
𝔽-minimal : (n : ℕ) → 𝔽 n
          → (o : ordered (𝔽 n) 𝓦') → totally-ordered o
          → has-minimal o
𝔽-minimal 1 (inl ⋆) o t = (inl ⋆) , γ
 where
  _≤_ = _≤'_ o
  γ : (x : 𝔽 1) → inl ⋆ ≤ x
  γ (inl ⋆) = reflex o (inl ⋆)
𝔽-minimal (succ (succ n)) _ o t with
 𝔽-minimal (succ n) (inl ⋆)
  (→-ordered         inr o  )
  (→-totally-ordered inr o t)
... | (x'₀ , m) = Cases (t (inr x'₀) (inl ⋆)) γ₁ γ₂
 where
  _≤_ = _≤'_ o
  γ₁ : inr x'₀ ≤ inl ⋆ → has-minimal o
  γ₁ x'₀≤⋆ = inr x'₀ , γ
   where
    γ : (x : 𝔽 (succ (succ n))) → inr x'₀ ≤ x
    γ (inl ⋆) = x'₀≤⋆
    γ (inr x) = m x
  γ₂ : ¬ (inr x'₀ ≤ inl ⋆) → has-minimal o
  γ₂ ⋆≤x'₀ = inl ⋆ , γ
   where
    γ : (x : 𝔽 (succ (succ n))) → inl ⋆ ≤ x
    γ (inl ⋆) = reflex o (inl ⋆)
    γ (inr x) = trans  o (inl ⋆) (inr x'₀) (inr x)
                  (antisym o (inr x'₀) (inl ⋆) ⋆≤x'₀)
                  (m x)

finite-minimal : {X : 𝓤 ̇ } → X → finite X
               → (o : ordered X 𝓦') → totally-ordered o
               → has-minimal o
finite-minimal y (0 , (_ , (g , _) , _)) o t = 𝟘-elim (g y)
finite-minimal y (succ n , e@(f , (g , η) , _)) o t
 = f x₀ , λ x → transport (f x₀ ≤_) (η x) (γ₀ (g x))
 where
   _≤_  = _≤'_ o
   _≤𝔽_ = _≤'_ (→-ordered f o)
   γ = 𝔽-minimal (succ n) (g y) (→-ordered         f o  )
                                (→-totally-ordered f o t)
   x₀ : 𝔽 (succ n)
   x₀ = pr₁ γ
   γ₀ : (x : 𝔽 (succ n)) → x₀ ≤𝔽 x
   γ₀ = pr₂ γ

-- Definition 4.1.10
record approx-ordered (X : ClosenessSpace 𝓤 ) (𝓦' : Universe)
 : 𝓤 ⊔ 𝓦' ⁺  ̇ where
  field
   o : ordered ⟨ X ⟩ 𝓦'
  open ordered o
  field
   _≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → Ω 𝓦'
   close-trivial
    : (ϵ : ℕ) (x y : ⟨ X ⟩) →    B X ϵ x y  → (x ≤ⁿ y) ϵ holds
   far-ordereded
    : (ϵ : ℕ) (x y : ⟨ X ⟩) → ¬ (B X ϵ x y)
    → (x ≤ⁿ y) ϵ holds → (x ≤ y) holds

-- Definition 4.1.11 [ TODO says ℝ incorrectly in paper ]
totally-approx-ordered : (X : ClosenessSpace 𝓤)
                       → approx-ordered X 𝓦' → 𝓤 ⊔ 𝓦' ̇
totally-approx-ordered X o
 = (x y : ⟨ X ⟩) (ϵ : ℕ) → decidable ((x ≤ⁿ y) ϵ holds)
 where open approx-ordered o

-- Definition 4.1.12
has_minimal : ℕ → {𝓤 : Universe} {X : ClosenessSpace 𝓤}
            → approx-ordered X 𝓦' → 𝓤 ⊔ 𝓦'  ̇
(has ϵ minimal) {𝓤} {X} o
 = Σ x₀ ꞉ ⟨ X ⟩ , ((x : ⟨ X ⟩) → (x₀ ≤ⁿ x) ϵ holds)
 where open approx-ordered o

-- Definition 4.1.13
has_global-minimal : ℕ → {𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
                   → {Y : ClosenessSpace 𝓥} → approx-ordered Y 𝓦'
                   → (f : X → ⟨ Y ⟩) → (𝓦' ⊔ 𝓤) ̇ 
(has ϵ global-minimal) {𝓤} {𝓥} {X} o f 
 = Σ x₀ ꞉ X , ((x : X) → (f x₀ ≤ⁿ f x) ϵ holds)
 where open approx-ordered o

-- Lemma 4.1.14


\end{code}

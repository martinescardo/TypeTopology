{-# OPTIONS --without-K --exact-split --safe #-}

open import Prelude
open import NaturalsOrder
open import DecidableAndDetachable
open import UF-FunExt
open import GenericConvergentSequence
open import Two-Properties
open import UF-Subsingletons
open import DiscreteAndSeparated

module SearchableTypes (fe : FunExt) where

open import Codistance fe
open import Codistances fe
open sequences

searchable : (X : 𝓤 ̇ ) → 𝓤ω 
searchable {𝓤} X 
 = {𝓥 : Universe}
 → (p : X → 𝓥 ̇ ) → detachable p
 → Σ x₀ ꞉ X , (Σ p → p x₀)

c-searchable : {X : 𝓤 ̇ } → (X → X → ℕ∞) → 𝓤ω 
c-searchable {𝓤} {X} c
 = {𝓥 : Universe} (p : X → 𝓥 ̇ ) → detachable p → continuous c p
 → Σ x₀ ꞉ X , (Σ p → p x₀)

searchable→c-searchable : {X : 𝓤 ̇ } → (cx : X → X → ℕ∞)
                        → searchable X → c-searchable cx
searchable→c-searchable {𝓤} {𝓥} cx 𝓔Sx p d _ = 𝓔Sx p d

𝓔⟨_,_⟩ : {X : 𝓤 ̇ }
       → (c : X → X → ℕ∞) (𝓔S : c-searchable c)
       → (p : X → 𝓥 ̇ ) → detachable p → continuous c p → X
S⟨_,_⟩ : {X : 𝓤 ̇ }
       → (c : X → X → ℕ∞) (𝓔S : c-searchable c)
       → (p : X → 𝓥 ̇ ) (d : detachable p) (ϕ : continuous c p)
       → Σ p → p (𝓔⟨ c , 𝓔S ⟩ p d ϕ)

𝓔⟨ _ , 𝓔S ⟩ p d ϕ = pr₁ (𝓔S p d ϕ)
S⟨ _ , 𝓔S ⟩ p d ϕ = pr₂ (𝓔S p d ϕ)

𝓔S-dec : {X : 𝓤 ̇ } (c : X → X → ℕ∞)
      → (𝓔S : c-searchable c)
      → (p : X → 𝓥 ̇ ) → detachable p → continuous c p
      → Σ p + ((x : X) → ¬ p x)
𝓔S-dec {𝓤} {𝓥} {X} c 𝓔S p d ϕ
 = Cases (d x₀)
     (λ  px₀ → inl (x₀ , px₀)) 
     (λ ¬px₀ → inr λ x px → ¬px₀ (γ₀ (x , px)))
 where
  x₀ : X
  x₀ = pr₁ (𝓔S p d ϕ)
  γ₀ : Σ p → p x₀
  γ₀ = pr₂ (𝓔S p d ϕ)

∶∶-indistinguishable : {X : 𝓤 ̇ } (d≡ : is-discrete X)
                     → (α : ℕ → X) (m : ℕ∞)
                     → m ≼ (codistance X d≡) α (head α ∶∶ tail α)
∶∶-indistinguishable {𝓤} {X} d≡ α m n p
  = codistance-conceptually₁ X d≡
      α (head α ∶∶ tail α)
      n (λ k _ → head-tail-sim α k)

increase-distance : {X : 𝓤 ̇ } (d : is-discrete X)
                  → let c = codistance X d in
                    (xs ys : ℕ → X) (m : ℕ) → under m ≼ c xs ys
                  → (x : X) → Succ (under m) ≼ c (x ∶∶ xs) (x ∶∶ ys)
increase-distance {𝓤} {X} d xs ys m m≼cxsys x n n<sm
 = codistance-conceptually₁ X d (x ∶∶ xs) (x ∶∶ ys) n (γ n n<sm)
 where
   γ : (n : ℕ) → n ⊏ Succ (under m)
     → (k : ℕ) → k ≤ n → (x ∶∶ xs) k ≡ (x ∶∶ ys) k
   γ n x zero k≤n = refl
   γ (succ n) x (succ k) k≤n
     = codistance-conceptually₂ X d xs ys n (m≼cxsys n x) k k≤n

→-c-searchable : {X : 𝓤 ̇ } (d≡ : is-discrete X)
              → searchable X
              → c-searchable (codistance X d≡)
→-c-searchable {𝓤} {X} d≡ 𝓔Sx = λ p d (m , ϕ) → η m p d ϕ where
  Xᴺ = ℕ → X
  cixs = codistance X d≡
  η : (m : ℕ) → (p : Xᴺ → 𝓥 ̇ ) → detachable p → uc-mod-of cixs p m
    → Σ xs₀ ꞉ Xᴺ , (Σ p → p xs₀)
  η 0 p d ϕ = (λ _ → pr₁ (𝓔Sx {𝓤} (λ _ → 𝟙) (λ _ → inl *)))
            , (λ (xs₀ , pxs₀)
            → ϕ xs₀ (λ _ → pr₁ (𝓔Sx (λ _ → 𝟙) (λ _ → inl *))) (λ _ ()) pxs₀)
  η (succ m) p d ϕ = (x ∶∶ x→xs x) , γ
   where
     px→xs = λ x xs → p (x ∶∶ xs)
     dx→xs = λ x xs → d (x ∶∶ xs)
     ϕx→xs : (x : X) → uc-mod-of (codistance X d≡) (px→xs x) m
     ϕx→xs x xs₁ xs₂ m≼cxs
      = ϕ (x ∶∶ xs₁) (x ∶∶ xs₂) (increase-distance d≡ xs₁ xs₂ m m≼cxs x)
     x→xs : X → (ℕ → X)
     x→xs x = pr₁ (η m (px→xs x) (dx→xs x) (ϕx→xs x))
     px = λ x → p (x ∶∶ x→xs x)
     dx = λ x → d (x ∶∶ x→xs x)
     x : X
     x = pr₁ (𝓔Sx px dx)
     γ : Σ p → p (x ∶∶ x→xs x)
     γ (xs₀ , pxs₀)
      = pr₂ (𝓔Sx px dx)
          (head xs₀ , pr₂ (η m (px→xs (head xs₀))
                               (dx→xs (head xs₀)) (ϕx→xs (head xs₀)))
          (tail xs₀ , ϕ xs₀ (head xs₀ ∶∶ tail xs₀)
          (∶∶-indistinguishable d≡ xs₀ (under (succ m))) pxs₀))

continuous-c-searcher : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                      → (cy : Y → Y → ℕ∞)
                      → (cx : X → X → ℕ∞)
                      → c-searchable cy → 𝓤ω
continuous-c-searcher {𝓤} {𝓥} {X} {Y} cy cx 𝓔Sy
 = {𝓦 : Universe}
 → (p : X → Y → 𝓦 ̇ )
 → (d : (x : X) → detachable (p x))
 → (m : ℕ) (ϕ : (x : X) → uc-mod-of cy (p x) m)
 → uc-mod-of² cx cy (λ x → 𝓔⟨ cy , 𝓔Sy ⟩ (p x) (d x) (m , ϕ x)) m m

×-c-searchable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → (cx : X → X → ℕ∞) → (cy : Y → Y → ℕ∞)
              → c-searchable cx
              → (𝓔Sy : c-searchable cy)
              → ((x : X) → Π (_⊏ cx x x))
              → continuous-c-searcher cy cx 𝓔Sy 
              → c-searchable (×-codistance cx cy)
×-c-searchable {𝓤} {𝓥} {X} {Y} cx cy 𝓔Sx 𝓔Sy f Cy p d (m , ϕ)
 = (x , x→y x) , γ
  where
   px→y = λ x y → p (x , y)
   dx→y = λ x y → d (x , y)
   ϕx→y : (x : X) → uc-mod-of cy (px→y x) m
   ϕx→y x y₁ y₂ m≼cy
    = ϕ (x , y₁) (x , y₂)
        (×-codistance-min cx cy (under m) x x y₁ y₂ (λ n _ → f x n) m≼cy)
   x→y : X → Y
   x→y x = 𝓔⟨ cy , 𝓔Sy ⟩ (px→y x) (dx→y x) (m , ϕx→y x)
   px = λ x → p (x , x→y x)
   dx = λ x → d (x , x→y x)
   ϕx : continuous cx px
   ϕx = m , λ x₁ x₂ m≼cx
          → ϕ (x₁ , x→y x₁) (x₂ , x→y x₂)
              (×-codistance-min cx cy (under m) x₁ x₂ (x→y x₁) (x→y x₂)
                m≼cx (Cy px→y dx→y m ϕx→y x₁ x₂ m≼cx))
   x : X
   x = 𝓔⟨ cx , 𝓔Sx ⟩ px dx ϕx
   γ : Σ p → p (x , x→y x)
   γ ((x₀ , y₀) , px₀y₀)
    = S⟨ cx , 𝓔Sx ⟩ px dx ϕx
        (x₀ , S⟨ cy , 𝓔Sy ⟩ (px→y x₀) (dx→y x₀) (m , ϕx→y x₀)
        (y₀ , px₀y₀))

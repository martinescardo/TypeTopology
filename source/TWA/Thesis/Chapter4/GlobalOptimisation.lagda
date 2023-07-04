\begin{code}

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
                  ⋆≤x₀ (m x)

F-ϵ-global-minimal : {X : 𝓤 ̇ } (Y : ClosenessSpace 𝓥)
                   → X → finite-discrete X
                   → (_≤_  : ⟨ Y ⟩ → ⟨ Y ⟩ → 𝓦 ̇ )
                   → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦'  ̇ )
                   → is-approx-order Y _≤_ _≤ⁿ_
                   → (ϵ : ℕ) → (f : X → ⟨ Y ⟩)
                   → (has ϵ global-minimal) _≤ⁿ_ f
F-ϵ-global-minimal Y x (n , (g , (h , η) , _)) _≤_ _≤ⁿ_ a ϵ f
 with 𝔽-ϵ-global-minimal n (h x) Y _≤_ _≤ⁿ_ a ϵ (f ∘ g)
... | (x₀ , m)
 = g x₀
 , λ x → transport (λ - → (f (g x₀) ≤ⁿ f -) ϵ) (η x) (m (h x))

-- Lemma 4.1.23

cover-continuity-lemma
 : (X : ClosenessSpace 𝓤) {X' : 𝓤' ̇ } (Y : ClosenessSpace 𝓥)
 → (_≤_  : ⟨ Y ⟩ → ⟨ Y ⟩ → 𝓦 ̇ )
 → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦'  ̇ )
 → is-approx-order Y _≤_ _≤ⁿ_
 → (ϵ : ℕ) → (f : ⟨ X ⟩ → ⟨ Y ⟩) (ϕ : f-ucontinuous X Y f)
 → let δ = pr₁ (ϕ ϵ) in (((g , _) , _) : X' is δ net-of X)
 → finite-discrete X'
 → (x : ⟨ X ⟩) → Σ x' ꞉ X' , (f (g x') ≤ⁿ f x) ϵ
cover-continuity-lemma
 X Y _≤_ _≤ⁿ_ (_ , _ , _ , c , a) ϵ f ϕ ((g , h , η) , _) e x
 = h x
 , c ϵ (f (g (h x))) (f x)
     (C-sym Y ϵ (f x) (f (g (h x)))
       (pr₂ (ϕ ϵ) x (g (h x))
         (η x)))

-- Theorem 4.1.22
global-opt : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
           → ⟨ X ⟩
           → (_≤_  : ⟨ Y ⟩ → ⟨ Y ⟩ → 𝓦 ̇ )
           → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦'  ̇ )
           → is-approx-order Y _≤_ _≤ⁿ_
           → (ϵ : ℕ) → (f : ⟨ X ⟩ → ⟨ Y ⟩) (ϕ : f-ucontinuous X Y f)
           → totally-bounded X 𝓤'
           → (has ϵ global-minimal) _≤ⁿ_ f
global-opt {𝓤} {𝓥} {𝓦} {𝓦'} {𝓤'} X Y x₁ _≤_ _≤ⁿ_ a ϵ f ϕ t
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
  η = cover-continuity-lemma X Y _≤_ _≤ⁿ_ a ϵ f ϕ X'-is-δ-net X'-is-finite
  h-min : (x : ⟨ X ⟩) → (f (g (h x)) ≤ⁿ f x) ϵ
  h-min x = pr₂ (η x)
  first  : has ϵ global-minimal _≤ⁿ_ (f ∘ g)
  first
   = F-ϵ-global-minimal Y (h x₁) X'-is-finite _≤_ _≤ⁿ_ a ϵ (f ∘ g)
  x'₀ : X'
  x'₀ = pr₁ first
  m  : is ϵ global-minimal _≤ⁿ_ (f ∘ g) x'₀
  m  = pr₂ first

{-
open import UF.Subsingletons
open import CoNaturals.GenericConvergentSequence
 renaming (ℕ-to-ℕ∞ to _↑)
open import Notation.Order
open import Naturals.Order

C-ext : (X : ClosenessSpace 𝓤)
      → (x y : ⟨ X ⟩)
      → ((ϵ : ℕ) → C X ϵ x y)
      → x ＝ y
C-ext X x y f
 = pr₁ (pr₂ (pr₂ X)) x y
     (to-subtype-＝ (being-decreasing-is-prop (fe _ _))
       (dfunext (fe _ _) (λ i → f (succ i) i (<-gives-⊏ i (succ i) (<-succ i)))))
-}
{-
CUT-CauchySequence : ClosenessSpace 𝓤 → 𝓤 ̇
CUT-CauchySequence (X , c , _)
 = Σ s ꞉ (ℕ → X) , Π ε ꞉ ℕ , Σ N ꞉ ℕ
 , ∀ m n → (N < m) × (N < n) → (ε ↑) ≺ c (s m) (s n)

has-limit : {X : 𝓤 ̇ } → (ℕ → X) → 𝓤 ̇
has-limit {X} s = Σ i ꞉ ℕ , Π n ꞉ ℕ , (i ≤ n → s n ＝ s i)

CUT-Complete : ClosenessSpace 𝓤 → 𝓤 ̇
CUT-Complete C = Π (s , _) ꞉ CUT-CauchySequence C , has-limit s

CUT-ContractionMapping : ClosenessSpace 𝓤 → 𝓤 ̇
CUT-ContractionMapping (X , c , _)
 = Σ T ꞉ (X → X) , Σ n ꞉ ℕ , (0 < n) × (∀ x y → (Succ ^ n) (c x y) ≼ c (T x) (T y))

iter : {X : 𝓤 ̇ } → X → (X → X) → (ℕ → X)
iter x₀ f n = (f ^ n) x₀

has-fixed-point : {X : 𝓤 ̇ } → (X → X) → 𝓤 ̇
has-fixed-point {𝓤} {X} f = Σ x* ꞉ X , f x* ＝ x*

limits-yield-fixed-points : {X : 𝓤 ̇ }
                          → (f : X → X)
                          → (x₀ : X)
                          → has-limit (iter x₀ f)
                          → has-fixed-point f
limits-yield-fixed-points f x₀ (n , l) = iter x₀ f n
                                       , l (succ n) (≤-succ n)

BanachFixedPointTheorem : (C : ClosenessSpace 𝓤)
                        → ⟨ C ⟩
                        → CUT-Complete C
                        → ((T , _) : CUT-ContractionMapping C)
                        → has-fixed-point T
BanachFixedPointTheorem (X , c , p) x₀ complete (T , succ k , _ , r)
 = limits-yield-fixed-points T x₀ limit
 where
  s : ℕ → X
  s = iter x₀ T
  limit : has-limit s
  limit = complete (s , λ ε → ε , γ ε)
   where
    γ : Π ε ꞉ ℕ , ((m n : ℕ) → (ε < m) × (ε < n) → (ε ↑) ≺ c (s m) (s n))
    γ ε (succ m) (succ n) (ε<sm , ε<sn)
      = ≺≼-gives-≺ (ε ↑) ((Succ ^ succ k) (c (s m) (s n))) (c (T (s m)) (T (s n)))
                   (q k ε (ε<sm , ε<sn)) (r (s m) (s n))
     where
      q : (k : ℕ) (ε : ℕ) → (ε < succ m) × (ε < succ n)
        → (ε ↑) ≺ (Succ ^ succ k) (c (s m) (s n))
      q 0 0 _ = 0 , refl , refl
      q 0 (succ ε) (ε<sm , ε<sn)
       = ≺-Succ (ε ↑) (c (s m) (s n)) (γ ε m n (ε<sm , ε<sn))
      q (succ k) ε ε<
       = ≺-Succ-r (ε ↑) ((Succ ^ succ k) (c (s m) (s n))) (q k ε ε<)
-}
{-
compute-actual-minima : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
                      → (_≤_  : ⟨ Y ⟩ → ⟨ Y ⟩ → 𝓦 ̇ )
                      → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦'  ̇ )
                      → is-approx-order Y _≤_ _≤ⁿ_
                      → (f : ⟨ X ⟩ → ⟨ Y ⟩) (ϕ : f-ucontinuous X Y f)
                      → ((ϵ : ℕ) → (has ϵ global-minimal) _≤ⁿ_ f)
                      → ((ϵ : ℕ) → is-prop (has ϵ global-minimal _≤ⁿ_ f))
                      → has-global-minimal _≤_ f
compute-actual-minima X Y _≤_ _≤ⁿ_ a f ϕ h p = {!!}

open import TypeTopology.DiscreteAndSeparated
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import TWA.Thesis.Chapter2.Sequences

compute-actual-minima-ℕ→D : {X : 𝓤 ̇ }
                          → (d : is-discrete X)
                          → (Y : ClosenessSpace 𝓥)
                          → (_≤_  : ⟨ Y ⟩ → ⟨ Y ⟩ → 𝓦 ̇ )
                          → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦'  ̇ )
                          → is-approx-order Y _≤_ _≤ⁿ_
                          → (f : (ℕ → X) → ⟨ Y ⟩)
                          → (ϕ : f-ucontinuous (ℕ→D-ClosenessSpace d) Y f)
                          → ((ϵ : ℕ) → (has ϵ global-minimal) _≤ⁿ_ f)
                          → is-prop (has-global-minimal _≤_ f)
                          → has-global-minimal _≤_ f
compute-actual-minima-ℕ→D
 {_} {_} {_} {_} {X} d Y _≤'_ _≤ⁿ_ (_ , l , _ , c , a) f ϕ h p
 = x₀ , {!!}
 where
  x₀ : ℕ → X
  x₀  ϵ = pr₁ (h (succ ϵ)) ϵ
  γ'  : (ϵ : ℕ) → (is ϵ global-minimal) _≤ⁿ_ f (pr₁ (h ϵ))
  γ'  ϵ = pr₂ (h ϵ)
  γ-  : (ϵ n : ℕ) → ϵ < n → (is ϵ global-minimal) _≤ⁿ_ f (pr₁ (h n))
  γ- ϵ n ϵ<n x
   = ≤ⁿ-trans _ _ _
       (Cases (C-decidable _ (pr₁ (ϕ ϵ)) (pr₁ (h n)) (pr₁ (h ϵ)))
         (c ϵ (f (pr₁ (h n))) (f (pr₁ (h ϵ))) ∘ pr₂ (ϕ ϵ) (pr₁ (h n)) (pr₁ (h ϵ)))
         {!!})
       (γ' ϵ x)
   where
    ≤ⁿ-trans = pr₁ (pr₂ (pr₁ (l ϵ)))
  γ'' : (ϵ : ℕ) → (is ϵ global-minimal) _≤ⁿ_ f x₀
  γ'' ϵ x = {!!}
  ζ   : (ϵ : ℕ) → (pr₁ (h ϵ) ∼ⁿ x₀) ϵ
  ζ = {!!}
  ζ'  : (n m : ℕ) → n < m → (pr₁ (h n) ∼ⁿ pr₁ (h m)) n
  ζ' n m n<m = {!p!}
--   where
  --  ≤ⁿ-trans = pr₁ (pr₂ (pr₁ (l ϵ)))
  {- Cases (C-decidable (ℕ→D-ClosenessSpace d) (pr₁ (ϕ ϵ)) x₀ x)
             (c ϵ (f x₀) (f x) ∘ (pr₂ (ϕ ϵ) x₀ x))
             {!!} -}
  γ  : is-global-minimal _≤'_ f x₀
  γ  x = {!!}
-}
\end{code}

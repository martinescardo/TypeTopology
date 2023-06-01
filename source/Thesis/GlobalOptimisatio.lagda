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
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to _↑
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)


-- Definition 4.1.4
record ordered (X : 𝓤 ̇ ) (𝓦' : Universe) : 𝓤 ⊔ 𝓦' ⁺  ̇ where
 field
  _≤_ : X → X → Ω 𝓦'
 _≤ₕ_ = λ x y → (x ≤ y) holds
 field
  reflex  : (x     : X) →    x ≤ₕ x
  trans   : (x y z : X) →    x ≤ₕ y  → y ≤ₕ z → x ≤ₕ z
  antisym : (x y   : X) → ¬ (x ≤ₕ y) → y ≤ₕ x
  
open ordered hiding (_≤_)

-- Definition 4.1.5
totally-ordered : {X : 𝓤 ̇ } → ordered X 𝓦' → 𝓤 ⊔ 𝓦' ̇
totally-ordered {𝓤} {𝓦'} {X} o
 = (x y : X) → decidable (x ≤ y)
 where _≤_ = _≤ₕ_ o

-- Definition 4.1.6
order-preserving : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → ordered X 𝓦' → ordered Y 𝓥'
                 → (f : X → Y) → 𝓤 ⊔ 𝓦' ⊔ 𝓥' ̇
order-preserving {𝓤} {𝓥} {𝓦'} {𝓥'} {X} {Y} ox oy f
 = (x₁ x₂ : X) → x₁ ≤x x₂ → f x₁ ≤y f x₂ 
 where
  _≤x_ = _≤ₕ_ ox
  _≤y_ = _≤ₕ_ oy

-- Lemma 4.1.7 [ TODO ]

-- Lemma 4.1.8 [ Should be a definition ]
is-minimal :  {X : 𝓤 ̇ } → ordered X 𝓦' → X → 𝓤 ⊔ 𝓦'  ̇
is-minimal {𝓤} {𝓦'} {X} o x₀ = (x : X) → x₀ ≤ x
 where _≤_ = _≤ₕ_ o

has-minimal : {X : 𝓤 ̇ } → ordered X 𝓦' → 𝓤 ⊔ 𝓦'  ̇
has-minimal = Σ ∘ is-minimal

-- Not in paper
is-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → ordered Y 𝓦' → (X → Y) → X → 𝓤 ⊔ 𝓦'  ̇
is-global-minimal {𝓤} {𝓥} {𝓦'} {X} o f x₀ = (x : X) → f x₀ ≤ f x
 where _≤_ = _≤ₕ_ o

has-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → ordered Y 𝓦' → (X → Y) → 𝓤 ⊔ 𝓦'  ̇
has-global-minimal f = Σ ∘ (is-global-minimal f)

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

𝔽-global-minimal : (n : ℕ) → 𝔽 n
                 → {Y : 𝓤 ̇ }
                 → (o : ordered Y 𝓦') → totally-ordered o
                 → (f : 𝔽 n → Y)
                 → has-global-minimal o f
𝔽-global-minimal 1 (inl ⋆) o t f = inl ⋆ , γ
 where
  open ordered
  γ : is-global-minimal o f (inl ⋆)
  γ (inl ⋆) = reflex o (f (inl ⋆))
𝔽-global-minimal (succ (succ n)) x o t f
 with 𝔽-global-minimal (succ n) (inl ⋆) o t (f ∘ inr)
... | (x'₀ , m) = Cases (t (f (inr x'₀)) (f (inl ⋆)))
                    γ₁ (γ₂ ∘ antisym o (f (inr x'₀)) (f (inl ⋆)))
 where
  open ordered o hiding (_≤_) renaming (_≤ₕ_ to _≤_)
  γ₁ : f (inr x'₀) ≤ f (inl ⋆  ) → has-global-minimal o f
  γ₁ x'₀≤⋆ = inr x'₀ , γ
   where
    γ : (x : 𝔽 (succ (succ n))) → f (inr x'₀) ≤ f x
    γ (inl ⋆) = x'₀≤⋆
    γ (inr x) = m x
  γ₂ : f (inl ⋆  ) ≤ f (inr x'₀) → has-global-minimal o f
  γ₂ ⋆≤x'₀ = inl ⋆ , γ
   where
    γ : (x : 𝔽 (succ (succ n))) → f (inl ⋆) ≤ f x
    γ (inl ⋆) = reflex o (f (inl ⋆))
    γ (inr x) = trans o (f (inl ⋆)) (f (inr x'₀)) (f (inr x)) ⋆≤x'₀ (m x)

finite-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥  ̇ }
                      → X → finite X
                      → (o : ordered Y 𝓦') → totally-ordered o
                      → (f : X → Y)
                      → has-global-minimal o f
finite-global-minimal x (0 , (_ , (h , _) , _)) o t f = 𝟘-elim (h x)
finite-global-minimal x (succ n , e@(g , (h , η) , _)) o t f
 = g x₀ , λ x → transport (f (g x₀) ≤_) (ap f (η x)) (γ₀ (h x))
 where
   _≤_  = _≤ₕ_ o
   _≤𝔽_ = _≤ₕ_ (→-ordered f o)
   γ = 𝔽-global-minimal (succ n) (inl ⋆) o t (f ∘ g)
   x₀ : 𝔽 (succ n)
   x₀ = pr₁ γ
   γ₀ : (x : 𝔽 (succ n)) → f (g x₀) ≤ f (g x)
   γ₀ = pr₂ γ
   
finite-minimal : {X : 𝓤 ̇ } → X → finite X
               → (o : ordered X 𝓦') → totally-ordered o
               → has-minimal o
finite-minimal x e o t = finite-global-minimal x e o t id

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
    → (x ≤ y) holds ⇔ (x ≤ⁿ y) ϵ holds
   reflex-ao : (ϵ : ℕ) (x : ⟨ X ⟩) → ((x ≤ⁿ x) ϵ) holds
   trans-ao : (ϵ : ℕ) (x y z : ⟨ X ⟩)
            → ((x ≤ⁿ y) ϵ) holds
            → ((y ≤ⁿ z) ϵ) holds
            → ((x ≤ⁿ z) ϵ) holds
   antisym-ao : (ϵ : ℕ) (x y : ⟨ X ⟩)
              → ¬ (((x ≤ⁿ y) ϵ) holds)
              → ((y ≤ⁿ x) ϵ) holds
             

-- Definition 4.1.11 [ TODO says ℝ incorrectly in paper ]
totally-approx-ordered : (X : ClosenessSpace 𝓤)
                       → approx-ordered X 𝓦' → 𝓤 ⊔ 𝓦' ̇
totally-approx-ordered X o
 = (x y : ⟨ X ⟩) (ϵ : ℕ) → decidable ((x ≤ⁿ y) ϵ holds)
 where open approx-ordered o

-- Definition 4.1.12
{-
is_minimal : ℕ → {𝓤 : Universe} {X : ClosenessSpace 𝓤}
            → approx-ordered X 𝓦' → ⟨ X ⟩ → 𝓤 ⊔ 𝓦'  ̇
(is ϵ minimal) {𝓤} {X} o x₀ = ((x : ⟨ X ⟩) → (x₀ ≤ⁿ x) ϵ holds)
 where open approx-ordered o

has_minimal : ℕ → {𝓤 : Universe} {X : ClosenessSpace 𝓤}
            → approx-ordered X 𝓦' → 𝓤 ⊔ 𝓦'  ̇
(has ϵ minimal) {𝓤} {X} o = Σ ((is ϵ minimal) {𝓤} {X} o)
-}

-- Definition 4.1.13
is_global-minimal : ℕ → {𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
                   → {Y : ClosenessSpace 𝓥} → approx-ordered Y 𝓦'
                   → (f : X → ⟨ Y ⟩) → X → (𝓦' ⊔ 𝓤) ̇ 
(is ϵ global-minimal) {𝓤} {𝓥} {X} o f x₀
 = (x : X) → (f x₀ ≤ⁿ f x) ϵ holds
 where open approx-ordered o

has_global-minimal : ℕ → {𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
                   → {Y : ClosenessSpace 𝓥} → approx-ordered Y 𝓦'
                   → (f : X → ⟨ Y ⟩) → (𝓦' ⊔ 𝓤) ̇ 
(has ϵ global-minimal) {𝓤} {𝓥} {X} o f
 = Σ ((is ϵ global-minimal) o f)

-- Lemma 4.1.14
{-
_op-cover-of_ : ℕ → (X : ClosenessSpace 𝓤) → ordered ⟨ X ⟩ 𝓦
              → (𝓥 𝓦' : Universe) → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺) ⊔ (𝓦' ⁺) ̇ 
(ϵ op-cover-of X) o 𝓥 𝓦' = Σ (X' , g , _) ꞉ ((ϵ cover-of X) 𝓥)
                          , (Σ o'  ꞉ ordered X' 𝓦'
                          , order-preserving o' o g)

lem : {X : ClosenessSpace 𝓤} → (o : approx-ordered X 𝓦)
    → (ϵ : ℕ)
    → (((X' , g , _) , o' , _)
        : (ϵ op-cover-of X) (approx-ordered.o o) 𝓥 𝓦')
    → (x'₀ : X') → is-minimal o' x'₀ → (is ϵ minimal) o (g x'₀)
lem {𝓤} {𝓦} {𝓥} {𝓦'} {X} ao ϵ ((X' , g , η) , o' , p) x'₀ m x
 = Cases (B-decidable X ϵ x₀ x)
     (close-trivial ϵ x₀ x)
     (λ f → trans-ao ϵ x₀ (g (h x)) x
       (pr₁ (far-ordereded ϵ x₀ (g (h x))
         (λ f' → f (B-trans X ϵ x₀ (g (h x)) x f'
           (B-sym X ϵ x (g (h x)) (pr₂ (η x))))))
         (p x'₀ (h x) (m (h x))))
       (close-trivial ϵ (g (h x)) x
           (B-sym X ϵ x (g (h x)) (pr₂ (η x)))))
 where
  x₀ = g x'₀
  h  = λ x → pr₁ (η x)
  open approx-ordered ao

lem'' : {X : ClosenessSpace 𝓤} → (o : approx-ordered X 𝓦)
    → (ϵ : ℕ)
    → ((X' , g , _) : (ϵ cover-of X) 𝓥)
    → (x'₀ : X') → is-global-minimal (approx-ordered.o o) g x'₀
    → (is ϵ minimal) o (g x'₀)
lem'' {𝓤} {𝓦} {𝓥} {X} ao ϵ (X' , g , η) x'₀ m x
 = Cases (B-decidable X ϵ x₀ x)
     (close-trivial ϵ x₀ x)
     (λ f → trans-ao ϵ x₀ (g (h x)) x
       (pr₁ (far-ordereded ϵ x₀ (g (h x))
         (λ f' → f (B-trans X ϵ x₀ (g (h x)) x f'
           (B-sym X ϵ x (g (h x)) (pr₂ (η x))))))
         (m (h x)))
       (close-trivial ϵ (g (h x)) x
           (B-sym X ϵ x (g (h x)) (pr₂ (η x)))))
 where
  x₀ = g x'₀
  h  = λ x → pr₁ (η x)
  open approx-ordered ao

lem' : {X : ClosenessSpace 𝓤} {Y : ClosenessSpace 𝓥}
     → (o : approx-ordered Y 𝓦)
     → (ϵ : ℕ) → (f : ⟨ X ⟩ → ⟨ Y ⟩) → (ϕ : f-ucontinuous X Y f)
     → ((X' , g , _) : (pr₁ (ϕ ϵ) cover-of X) 𝓦')
     → (x'₀ : X') → is-global-minimal (approx-ordered.o o) (f ∘ g) x'₀
     → (is ϵ global-minimal) o f (g x'₀)
lem' {𝓤} {𝓥} {𝓦} {𝓦'} {X} {Y} ao ϵ f ϕ (X' , g , η)  x'₀ m x
 = Cases (B-decidable Y ϵ (f (g x'₀)) (f x))
     (close-trivial ϵ (f (g x'₀)) (f x))
     (λ z → trans-ao ϵ (f (g x'₀)) (f (g (h x))) (f x)
       (pr₁ (far-ordereded ϵ (f (g x'₀)) (f (g (h x)))
         (λ b → z (B-trans Y ϵ (f (g x'₀)) (f (g (h x))) (f x) b
           (B-sym Y ϵ (f x) (f (g (h x)))
             (pr₂ (ϕ ϵ) x (g (h x)) (pr₂ (η x)))))))
         (m (h x)))
       (close-trivial ϵ (f (g (h x))) (f x)
         (B-sym Y ϵ (f x) (f (g (h x)))
           (pr₂ (ϕ ϵ) x (g (h x)) (pr₂ (η x))))))
 where
  h  = λ x → pr₁ (η x)
  open approx-ordered ao
-}

-- Not in paper:
--  * fin has global minimum
--  * finite δ-cover yields ϵ-global min

theorem'' : {Y : ClosenessSpace 𝓥}
          → (o : approx-ordered Y 𝓦) (t : totally-approx-ordered Y o)
          → (ϵ n : ℕ) → (f : 𝔽 n → ⟨ Y ⟩) → 𝔽 n
          → (has ϵ global-minimal) o f
theorem'' o t ϵ 1 f (inl ⋆)
 = inl ⋆ , γ
 where
  open approx-ordered o hiding (o)
  γ : is ϵ global-minimal o f (inl ⋆)
  γ (inl ⋆) = reflex-ao ϵ (f (inl ⋆))
theorem'' o t ϵ (succ (succ n)) f _
 with theorem'' o t ϵ (succ n) (f ∘ inr) (inl ⋆)
... | (x₀ , m) = Cases (t (f (inr x₀)) (f (inl ⋆)) ϵ) γ₁
                   (γ₂ ∘ antisym-ao ϵ (f (inr x₀)) (f (inl ⋆)))
 where
  open approx-ordered o hiding (o)
  IH : has ϵ global-minimal o (f ∘ inr)
  IH = theorem'' o t ϵ (succ n) (f ∘ inr) (inl ⋆)
  γ₁ : (f (inr x₀) ≤ⁿ f (inl ⋆)) ϵ holds → has ϵ global-minimal o f
  γ₁ x₀≤⋆ = inr x₀ , γ
   where
    γ : is ϵ global-minimal o f (inr x₀)
    γ (inl ⋆) = x₀≤⋆
    γ (inr x) = m x
  γ₂ : (f (inl ⋆) ≤ⁿ f (inr x₀)) ϵ holds → has ϵ global-minimal o f
  γ₂ ⋆≤x₀ = inl ⋆ , γ
   where
    γ : is ϵ global-minimal o f (inl ⋆)
    γ (inl ⋆) = reflex-ao ϵ (f (inl ⋆))
    γ (inr x) = trans-ao ϵ _ _ _ ⋆≤x₀ (m x)

theorem''' : {X : 𝓤 ̇ } {Y : ClosenessSpace 𝓥}
           → (o : approx-ordered Y 𝓦) (t : totally-approx-ordered Y o)
           → (ϵ : ℕ) → (f : X → ⟨ Y ⟩)
           → X → finite X
           → (has ϵ global-minimal) o f
theorem''' o t ϵ f x (zero , g , (h , _) , _) = 𝟘-elim (h x)
theorem''' o t ϵ f x (succ n , g , (h , η) , _)
 with theorem'' o t ϵ (succ n) (f ∘ g) (inl ⋆)
... | (x₀ , m) = g x₀ , λ x → transport (λ - → (f (g x₀) ≤ⁿ f -) ϵ holds) (η x) (m (h x))
 where open approx-ordered o

theorem'  : {X : ClosenessSpace 𝓤} {Y : ClosenessSpace 𝓥}
          → (o : approx-ordered Y 𝓦) → totally-approx-ordered Y o
          → (ϵ : ℕ) → (f : ⟨ X ⟩ → ⟨ Y ⟩) → (ϕ : f-ucontinuous X Y f)
          → ((X' , g , _) : (pr₁ (ϕ ϵ) cover-of X) 𝓦')
          → ⟨ X ⟩ → finite X'
          → (has ϵ global-minimal) o f
theorem' {𝓤} {𝓥} {𝓦} {𝓦'} {X} {Y} o t ϵ f ϕ (X' , g , η) x e
 with theorem''' o t ϵ (f ∘ g) (pr₁ (η x)) e
... | (x₀ , m) = g x₀ , λ x → trans-ao ϵ _ _ _ (m (pr₁ (η x))) (close-trivial ϵ (f (g (pr₁ (η x)))) (f x) (pr₂ (ϕ ϵ) (g (pr₁ (η x))) x (B-sym X δ x (g (pr₁ (η x))) (pr₂ (η x)))))
 where
  open approx-ordered o
  δ = pr₁ (ϕ ϵ)

theorem : {X : ClosenessSpace 𝓤} {Y : ClosenessSpace 𝓥}
        → (o : approx-ordered Y 𝓦) → totally-approx-ordered Y o
        → (f : ⟨ X ⟩ → ⟨ Y ⟩) → (ϕ : f-ucontinuous X Y f)
        → ⟨ X ⟩ → totally-bounded X 𝓤'
        → (ϵ : ℕ) → (has ϵ global-minimal) o f
theorem {𝓤} {𝓥} {𝓦} {𝓤'} {X} {Y} o t f ϕ x b ϵ
 = theorem' {𝓤} {𝓥} {𝓦} {𝓤'} {X} {Y}
     o t ϵ f ϕ (pr₁ (b (pr₁ (ϕ ϵ)))) x (pr₂ (b (pr₁ (ϕ ϵ))))

\end{code}

-- Subtype closeness stuff

subtype-closeness : (X : ClosenessSpace 𝓤)
                  → (P : ⟨ X ⟩ → 𝓥 ̇ ) → ((x : ⟨ X ⟩) → is-prop (P x))
                  → is-closeness-space (Σ P)
pr₁ (subtype-closeness (X , c , i , j , k , l) P I)
 x y = c (pr₁ x) (pr₁ y)
pr₁ (pr₂ (subtype-closeness (X , c , i , j , k , l) P I))
 x y cxy=∞ = to-subtype-＝ I (i (pr₁ x) (pr₁ y) cxy=∞)
pr₁ (pr₂ (pr₂ (subtype-closeness (X , c , i , j , k , l) P I)))
 x     = j (pr₁ x)
pr₁ (pr₂ (pr₂ (pr₂ (subtype-closeness (X , c , i , j , k , l) P I))))
 x y   = k (pr₁ x) (pr₁ y)
pr₂ (pr₂ (pr₂ (pr₂ (subtype-closeness (X , c , i , j , k , l) P I))))
 x y z = l (pr₁ x) (pr₁ y) (pr₁ z)

subtype-ordered : {X : ClosenessSpace 𝓤}
                → (P : ⟨ X ⟩ → 𝓥 ̇ )
                → ordered ⟨ X ⟩ 𝓦
                → ordered (Σ P) 𝓦
ordered._≤_ (subtype-ordered P o)
 x y   = ordered._≤_ o (pr₁ x) (pr₁ y)
reflex (subtype-ordered P o)
 x     = reflex o (pr₁ x)
trans (subtype-ordered P o)
 x y z = trans o (pr₁ x) (pr₁ y) (pr₁ z)
antisym (subtype-ordered P o)
 x y   = antisym o (pr₁ x) (pr₁ y)

subtype-approx : {X : ClosenessSpace 𝓤}
               → (P : ⟨ X ⟩ → 𝓥 ̇ ) → (I : (x : ⟨ X ⟩) → is-prop (P x))
               → approx-ordered X 𝓦
               → approx-ordered (Σ P , subtype-closeness X P I) 𝓦
approx-ordered.o (subtype-approx {𝓤} {𝓥} {𝓦} {X} P I o)
 = subtype-ordered {_} {_} {_} {X} P (approx-ordered.o o)
approx-ordered._≤ⁿ_ (subtype-approx P I o)
 x y   = approx-ordered._≤ⁿ_ o (pr₁ x) (pr₁ y)
approx-ordered.close-trivial (subtype-approx P I o)
 n x y = approx-ordered.close-trivial o n (pr₁ x) (pr₁ y)
approx-ordered.far-ordereded (subtype-approx P I o)
 n x y = approx-ordered.far-ordereded o n (pr₁ x) (pr₁ y)
approx-ordered.trans-ao (subtype-approx P I o)
 n x y z = approx-ordered.trans-ao o n (pr₁ x) (pr₁ y) (pr₁ z)


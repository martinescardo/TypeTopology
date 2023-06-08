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

module Thesis.Chapter4.GlobalOptimisation (fe : FunExt) where

open import Thesis.Chapter3.SearchableTypes fe
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to _↑
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)

record preordered (X : 𝓤 ̇ ) (𝓦' : Universe) : 𝓤 ⊔ 𝓦' ⁺  ̇ where
 field
  Order : X → X → Ω 𝓦'
 _≤_ : X → X → 𝓦' ̇ 
 x ≤ y = Order x y holds
 _<_ : X → X → 𝓤 ⊔ 𝓦'  ̇
 x < y = (x ≤ y) × ¬ (x ≡ y)
 field
  reflex  : (x     : X) →    x ≤ x
  trans   : (x y z : X) →    x ≤ y  → y ≤ z → x ≤ z
{-
 <-coarse : (x y   : X) →    x < y  →    x ≤ y
 reflex'  : (x y   : X) → ¬ (x ≤ y) → ¬ (x ≡ y)
 <-coarse x y v      = pr₁ v
 reflex'  x y u refl = u (reflex x)
-}

open preordered hiding (_≤_) -- ; reflex ; trans) -- ;_<_;<-coarse;reflex')

totally-ordered : {X : 𝓤 ̇ } → preordered X 𝓦' → 𝓤 ⊔ 𝓦' ̇
totally-ordered {𝓤} {𝓦'} {X} o = (x y : X) → (x ≤ y) + (y ≤ x)
 where open preordered o

{-
-- Definition 4.1.5
decidable-order : {X : 𝓤 ̇ } → preordered X 𝓦' → 𝓤 ⊔ 𝓦' ̇
decidable-order {𝓤} {𝓦'} {X} o
 = (x y : X) → decidable (x ≤ y)
 where open preordered o

antisym : {X : 𝓤 ̇ } → (o : preordered X 𝓦')
        → totally-ordered o
        → let _≤_ = preordered._≤_ o in
          let _<_ = preordered._<_ o in
          (x y : X) → ¬ (x ≤ y) → y < x
antisym o t x y ¬x≤y with t x y
... | inl x≤y = 𝟘-elim (¬x≤y x≤y)
... | inr y≤x = y≤x , reflex' x y ¬x≤y ∘ _⁻¹
 where open preordered o

strong-antisym : {X : 𝓤 ̇ } → (o : preordered X 𝓦')
               → totally-ordered o
               → let _≤_ = preordered._≤_ o in
                 let _<_ = preordered._<_ o in
                 (x y : X) → ¬ (x ≤ y) → y ≤ x
strong-antisym o t x y = <-coarse y x ∘ (antisym o t x y)
 where open preordered o
-}
{-
is-minimal :  {X : 𝓤 ̇ } → preordered X 𝓦' → X → 𝓤 ⊔ 𝓦'  ̇
is-minimal {𝓤} {𝓦'} {X} o x₀ = (x : X) → x₀ ≤ x
 where open preordered o

has-minimal : {X : 𝓤 ̇ } → preordered X 𝓦' → 𝓤 ⊔ 𝓦'  ̇
has-minimal = Σ ∘ is-minimal
-}

is-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → preordered Y 𝓦' → (X → Y) → X → 𝓤 ⊔ 𝓦'  ̇
is-global-minimal {𝓤} {𝓥} {𝓦'} {X} o f x₀ = (x : X) → f x₀ ≤ f x
 where open preordered o
 
has-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → preordered Y 𝓦' → (X → Y) → 𝓤 ⊔ 𝓦'  ̇
has-global-minimal f = Σ ∘ (is-global-minimal f)

{-
→-preordered : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (Y → X)
             → preordered X 𝓦' → preordered Y 𝓦'
preordered.Order (→-preordered f o) x y
                                 = Order o (f x) (f y)
reflex  (→-preordered f o) x     = reflex  o (f x)
trans   (→-preordered f o) x y z = trans   o (f x) (f y) (f z)
-}

𝔽-global-minimal : (n : ℕ) → 𝔽 n
                 → {Y : 𝓤 ̇ }
                 → (o : preordered Y 𝓦')
                 → totally-ordered o
                 → (f : 𝔽 n → Y)
                 → has-global-minimal o f
𝔽-global-minimal 1 (inl ⋆) o t f = inl ⋆ , γ
 where
  open preordered
  γ : is-global-minimal o f (inl ⋆)
  γ (inl ⋆) = reflex o (f (inl ⋆))
𝔽-global-minimal (succ (succ n)) x o t f
 with 𝔽-global-minimal (succ n) (inl ⋆) o t (f ∘ inr)
... | (x'₀ , m) = Cases (t (f (inr x'₀)) (f (inl ⋆))) γ₁ γ₂
 where
  open preordered o
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
                      → (o : preordered Y 𝓦')
                      → totally-ordered o
                      → (f : X → Y)
                      → has-global-minimal o f
finite-global-minimal x (0 , (_ , (h , _) , _)) o t f = 𝟘-elim (h x)
finite-global-minimal x (succ n , e@(g , (h , η) , _)) o t f
 with 𝔽-global-minimal (succ n) (inl ⋆) o t (f ∘ g)
... | (x₀ , γ₀) = g x₀ , λ x → transport (f (g x₀) ≤_) (ap f (η x)) (γ₀ (h x))
 where open preordered o

{-   
finite-minimal : {X : 𝓤 ̇ } → X → finite X
               → (o : preordered X 𝓦')
               → totally-ordered o
               → decidable-order o
               → has-minimal o
finite-minimal x e o t d = finite-global-minimal x e o t d id
-}

-- Definition 4.1.10
record totally-approx-ordered (X : ClosenessSpace 𝓤 ) (𝓦' : Universe)
 : 𝓤 ⊔ 𝓦' ⁺  ̇ where
  field
   preorder : preordered ⟨ X ⟩ 𝓦'
   ApproxOrder : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → Ω 𝓦'
  open preordered preorder public
    using (_≤_)
  _≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦' ̇
  (x ≤ⁿ y) ϵ = ApproxOrder x y ϵ holds
  field
   close-trivial
    : (ϵ : ℕ) (x y : ⟨ X ⟩) →    B X ϵ x y  → (x ≤ⁿ y) ϵ
   far-ordereded
    : (ϵ : ℕ) (x y : ⟨ X ⟩) → ¬ (B X ϵ x y)
    → x ≤ y ⇔ (x ≤ⁿ y) ϵ
   reflex-a : (ϵ : ℕ) (x : ⟨ X ⟩) → (x ≤ⁿ x) ϵ
   trans-a  : (ϵ : ℕ) (x y z : ⟨ X ⟩)
            → (x ≤ⁿ y) ϵ
            → (y ≤ⁿ z) ϵ
            → (x ≤ⁿ z) ϵ
   total-a  : (ϵ : ℕ) (x y : ⟨ X ⟩) → (x ≤ⁿ y) ϵ + (y ≤ⁿ x) ϵ             

{- -- Definition 4.1.11 [ TODO says ℝ incorrectly in paper ]
totally-approx-ordered : (X : ClosenessSpace 𝓤)
                       → totally-approx-ordered X 𝓦' → 𝓤 ⊔ 𝓦' ̇
totally-approx-ordered X o
 = (x y : ⟨ X ⟩) (ϵ : ℕ) → decidable ((x ≤ⁿ y) ϵ)
 where open approx-ordered o
-}

-- Definition 4.1.12
{-
is_minimal : ℕ → {𝓤 : Universe} {X : ClosenessSpace 𝓤}
            → totally-approx-ordered X 𝓦' → ⟨ X ⟩ → 𝓤 ⊔ 𝓦'  ̇
(is ϵ minimal) {𝓤} {X} o x₀ = ((x : ⟨ X ⟩) → (x₀ ≤ⁿ x) ϵ holds)
 where open approx-ordered o

has_minimal : ℕ → {𝓤 : Universe} {X : ClosenessSpace 𝓤}
            → approx-ordered X 𝓦' → 𝓤 ⊔ 𝓦'  ̇
(has ϵ minimal) {𝓤} {X} o = Σ ((is ϵ minimal) {𝓤} {X} o)
-}

-- Definition 4.1.13
is_global-minimal : ℕ → {𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
                   → {Y : ClosenessSpace 𝓥} → totally-approx-ordered Y 𝓦'
                   → (f : X → ⟨ Y ⟩) → X → (𝓦' ⊔ 𝓤) ̇ 
(is ϵ global-minimal) {𝓤} {𝓥} {X} o f x₀
 = (x : X) → (f x₀ ≤ⁿ f x) ϵ
 where open totally-approx-ordered o

has_global-minimal : ℕ → {𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
                   → {Y : ClosenessSpace 𝓥} → totally-approx-ordered Y 𝓦'
                   → (f : X → ⟨ Y ⟩) → (𝓦' ⊔ 𝓤) ̇ 
(has ϵ global-minimal) {𝓤} {𝓥} {X} o f
 = Σ ((is ϵ global-minimal) o f)

-- Lemma 4.1.23
cover-order : {X : ClosenessSpace 𝓤} {Y : ClosenessSpace 𝓥}
            → (o : totally-approx-ordered Y 𝓦)
            → (ϵ : ℕ) → (f : ⟨ X ⟩ → ⟨ Y ⟩) → (ϕ : f-ucontinuous X Y f)
            → ((X' , g , _) : (pr₁ (ϕ ϵ) cover-of X) 𝓦')
            → let _≤_ = totally-approx-ordered._≤ⁿ_ o in
              (x : ⟨ X ⟩) → Σ x' ꞉ X' , (f x ≤ f (g x')) ϵ
cover-order o ϵ f ϕ (X' , g , η) x
 = pr₁ (η x)
 , (totally-approx-ordered.close-trivial o ϵ (f x) (f (g (pr₁ (η x))))
     (pr₂ (ϕ ϵ) x (g (pr₁ (η x))) (pr₂ (η x))))

theorem'' : {Y : ClosenessSpace 𝓥}
          → (o : totally-approx-ordered Y 𝓦)
          → (ϵ n : ℕ) → (f : 𝔽 n → ⟨ Y ⟩) → 𝔽 n
          → (has ϵ global-minimal) o f
theorem'' o ϵ 1 f (inl ⋆)
 = inl ⋆ , γ
 where
  open totally-approx-ordered o
  γ : is ϵ global-minimal o f (inl ⋆)
  γ (inl ⋆) = reflex-a ϵ (f (inl ⋆)) -- reflex o ϵ (f (inl ⋆))
theorem'' o ϵ (succ (succ n)) f _
 with theorem'' o ϵ (succ n) (f ∘ inr) (inl ⋆)
... | (x₀ , m) = Cases (total-a ϵ (f (inr x₀)) (f (inl ⋆)))
                   γ₁ γ₂
 where
  open totally-approx-ordered o
  IH : has ϵ global-minimal o (f ∘ inr)
  IH = theorem'' o ϵ (succ n) (f ∘ inr) (inl ⋆)
  γ₁ : (f (inr x₀) ≤ⁿ f (inl ⋆)) ϵ → has ϵ global-minimal o f
  γ₁ x₀≤⋆ = inr x₀ , γ
   where
    γ : is ϵ global-minimal o f (inr x₀)
    γ (inl ⋆) = x₀≤⋆
    γ (inr x) = m x
  γ₂ : (f (inl ⋆) ≤ⁿ f (inr x₀)) ϵ → has ϵ global-minimal o f
  γ₂ ⋆≤x₀ = inl ⋆ , γ
   where
    γ : is ϵ global-minimal o f (inl ⋆)
    γ (inl ⋆) = reflex-a ϵ (f (inl ⋆))
    γ (inr x) = trans-a  ϵ _ _ _ ⋆≤x₀ (m x)

theorem''' : {X : 𝓤 ̇ } {Y : ClosenessSpace 𝓥}
           → (o : totally-approx-ordered Y 𝓦)
           → (ϵ : ℕ) → (f : X → ⟨ Y ⟩)
           → X → finite X
           → (has ϵ global-minimal) o f
theorem''' o ϵ f x (zero , g , (h , _) , _) = 𝟘-elim (h x)
theorem''' o ϵ f x (succ n , g , (h , η) , _)
 with theorem'' o ϵ (succ n) (f ∘ g) (inl ⋆)
... | (x₀ , m) = g x₀ , λ x → transport (λ - → (f (g x₀) ≤ⁿ f -) ϵ) (η x) (m (h x))
 where open totally-approx-ordered o

theorem'  : {X : ClosenessSpace 𝓤} {Y : ClosenessSpace 𝓥}
          → (o : totally-approx-ordered Y 𝓦)
          → (ϵ : ℕ) → (f : ⟨ X ⟩ → ⟨ Y ⟩) → (ϕ : f-ucontinuous X Y f)
          → ((X' , g , _) : (pr₁ (ϕ ϵ) cover-of X) 𝓦')
          → ⟨ X ⟩ → finite X'
          → (has ϵ global-minimal) o f
theorem' {𝓤} {𝓥} {𝓦} {𝓦'} {X} {Y} o ϵ f ϕ (X' , g , η) x e
 with theorem''' o ϵ (f ∘ g) (pr₁ (η x)) e
... | (x₀ , m) = g x₀ , λ x → trans-a ϵ _ _ _ (m (pr₁ (η x))) (close-trivial ϵ (f (g (pr₁ (η x)))) (f x) (pr₂ (ϕ ϵ) (g (pr₁ (η x))) x (B-sym X δ x (g (pr₁ (η x))) (pr₂ (η x)))))
 where
  open totally-approx-ordered o
  δ = pr₁ (ϕ ϵ)

theorem : {X : ClosenessSpace 𝓤} {Y : ClosenessSpace 𝓥}
        → (o : totally-approx-ordered Y 𝓦)
        → (f : ⟨ X ⟩ → ⟨ Y ⟩) → (ϕ : f-ucontinuous X Y f)
        → ⟨ X ⟩ → totally-bounded X 𝓤'
        → (ϵ : ℕ) → (has ϵ global-minimal) o f
theorem {𝓤} {𝓥} {𝓦} {𝓤'} {X} {Y} o f ϕ x b ϵ
 = theorem' {𝓤} {𝓥} {𝓦} {𝓤'} {X} {Y}
     o ϵ f ϕ (pr₁ (b (pr₁ (ϕ ϵ)))) x (pr₂ (b (pr₁ (ϕ ϵ))))

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


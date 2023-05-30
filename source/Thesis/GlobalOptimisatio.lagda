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
𝔽-minimal : (n : ℕ) → 𝔽 n
          → (o : ordered (𝔽 n) 𝓦') → totally-ordered o
          → has-minimal o
𝔽-minimal 1 (inl ⋆) o t = (inl ⋆) , γ
 where
  _≤_ = _≤ₕ_ o
  γ : (x : 𝔽 1) → inl ⋆ ≤ x
  γ (inl ⋆) = reflex o (inl ⋆)
𝔽-minimal (succ (succ n)) _ o t with
 𝔽-minimal (succ n) (inl ⋆)
  (→-ordered         inr o  )
  (→-totally-ordered inr o t)
... | (x'₀ , m) = Cases (t (inr x'₀) (inl ⋆)) γ₁ γ₂
 where
  _≤_ = _≤ₕ_ o
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
   _≤_  = _≤ₕ_ o
   _≤𝔽_ = _≤ₕ_ (→-ordered f o)
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
    → (x ≤ y) holds ⇔ (x ≤ⁿ y) ϵ holds
   trans-ao : (ϵ : ℕ) (x y z : ⟨ X ⟩)
            → ((x ≤ⁿ y) ϵ) holds
            → ((y ≤ⁿ z) ϵ) holds
            → ((x ≤ⁿ z) ϵ) holds

-- Definition 4.1.11 [ TODO says ℝ incorrectly in paper ]
totally-approx-ordered : (X : ClosenessSpace 𝓤)
                       → approx-ordered X 𝓦' → 𝓤 ⊔ 𝓦' ̇
totally-approx-ordered X o
 = (x y : ⟨ X ⟩) (ϵ : ℕ) → decidable ((x ≤ⁿ y) ϵ holds)
 where open approx-ordered o

-- Definition 4.1.12
is_minimal : ℕ → {𝓤 : Universe} {X : ClosenessSpace 𝓤}
            → approx-ordered X 𝓦' → ⟨ X ⟩ → 𝓤 ⊔ 𝓦'  ̇
(is ϵ minimal) {𝓤} {X} o x₀ = ((x : ⟨ X ⟩) → (x₀ ≤ⁿ x) ϵ holds)
 where open approx-ordered o

has_minimal : ℕ → {𝓤 : Universe} {X : ClosenessSpace 𝓤}
            → approx-ordered X 𝓦' → 𝓤 ⊔ 𝓦'  ̇
(has ϵ minimal) {𝓤} {X} o = Σ ((is ϵ minimal) {𝓤} {X} o)

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
         λ f' → f (B-trans X ϵ x₀ (g (h x)) x f'
           (B-sym X ϵ x (g (h x)) (pr₂ (η x)))))
         (p x'₀ (h x) (m (h x))))
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
         (λ b → z (B-trans Y ϵ (f (g x'₀)) (f (g (h x))) (f x)
           b
           (B-sym Y ϵ (f x) (f (g (h x)))
             (pr₂ (ϕ ϵ) x (g (h x)) (pr₂ (η x)))))))
         (m (h x)))
       (close-trivial ϵ (f (g (h x))) (f x)
         (B-sym Y ϵ (f x) (f (g (h x)))
           (pr₂ (ϕ ϵ) x (g (h x)) (pr₂ (η x))))))
 where
  h  = λ x → pr₁ (η x)
  open approx-ordered ao

-- fin has global minimum
-- finite δ-cover yields ϵ-global min



\end{code}
-- More sensible way of doing the below?
theorem : {X : ClosenessSpace 𝓤} {Y : ClosenessSpace 𝓥}
        → (ox : approx-ordered X 𝓦) → (oy : approx-ordered Y 𝓦)
        → (f : ⟨ X ⟩ → ⟨ Y ⟩) → (ϕ : f-ucontinuous X Y f)
        → (ϵ δ : ℕ) → δ ≡ pr₁ (ϕ ϵ)
        → ((X' , η) : (δ cover-of X) 𝓤')
        → X'
        → (has ϵ global-minimal) oy f
theorem {𝓤} {𝓥} {𝓦} {𝓤'} {X , cx , i} {Y , cy , j} ox oy f ϕ ϵ 0 e (X' , g , η) x₀
 = g x₀
 , (λ x → close-trivial oy ϵ (f (g x₀)) (f x) (pr₂ (ϕ ϵ) (g x₀) x
    (transport (λ - → B (X , cx , i) - (g x₀) x) e (zero-minimal (cx (g x₀) x)))))
 where
  open approx-ordered
theorem {𝓤} {𝓥} {𝓦} {𝓤'} {X , cx , i} {Y , cy , j} ox oy f ϕ 0 (succ δ) e (X' , g , η) x₀
 = g x₀
 , (λ x → close-trivial oy 0 (f (g x₀)) (f x) (zero-minimal (cy (f (g x₀)) (f x))))
 where
  open approx-ordered
theorem {𝓤} {𝓥} {𝓦} {𝓤'} {X , c , i} {Y} ox oy f ϕ (succ ϵ) (succ δ) e (X' , g , η) x₀
 = {!!}
 , {!!}
 where
  open approx-ordered
  IH : has ϵ global-minimal oy f
  IH = theorem {𝓤} {𝓥} {𝓦} {𝓤'} {X , c , i} {Y} ox oy f ϕ ϵ δ {!!} (X' , g , {!!}) {!!}
  
qimage : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (X → Y) → 𝓤 ⊔ 𝓥 ̇
qimage {𝓤} {𝓥} {X} {Y} f = Σ y ꞉ Y , Σ x ꞉ X , (y ≡ f x)

finiteness : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) → finite X → finite (qimage f)
finiteness f (n , p , q , r , s)
 = n , (λ x → f (p x) , p x , refl)
 , qinvs-are-equivs (λ x → f (p x) , p x , refl)
     ((λ (y , x , e) → r x) , s , (λ (y , x , e) → {!!}))

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

-- Lemma 4.1.15
open import UF.PropTrunc

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open import UF.ImageAndSurjection pt

 qimage-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) → qimage f → image f
 qimage-image f (x , y , e) = f y , ∣ y , refl ∣

 the : {X : 𝓤 ̇ } {Y : ClosenessSpace 𝓥} → (o : approx-ordered Y 𝓦)
     → (f : X → ⟨ Y ⟩) (ϵ : ℕ) (x₀ : X)
     → (is ϵ minimal)
         (subtype-approx (_∈image f)
         (λ y → being-in-the-image-is-prop y f) o)
        (corestriction f x₀)
     ⇔ ((is ϵ global-minimal) o f x₀)
 pr₁ (the {𝓤} {𝓥} {𝓦} {X} {Y , c , _} o f ϵ x₀) m x
  = m (corestriction f x)
 pr₂ (the {𝓤} {𝓥} {𝓦} {X} {Y , c , _} o f ϵ x₀)
  = image-induction f _ (λ (y , _) → holds-is-prop ((f x₀ ≤ⁿ y) ϵ))
  where open approx-ordered o

 qthe : {X : 𝓤 ̇ } {Y : ClosenessSpace 𝓥} → (o : approx-ordered Y 𝓦)
     → (f : X → ⟨ Y ⟩) (ϵ : ℕ) ((y₀ , x₀ , _) : qimage f)
     → (is-minimal (approx-ordered.o o)) y₀
     ⇔ ((is ϵ global-minimal) o f x₀)
 pr₁ (qthe {𝓤} {𝓥} {𝓦} {X} {Y , c , _} o f ϵ (y₀ , x₀ , g)) m x
  = {!m!} -- m (corestriction f x)
 pr₂ (qthe {𝓤} {𝓥} {𝓦} {X} {Y , c , _} o f ϵ x₀)
  = {!!} -- image-induction f _ (λ (y , _) → holds-is-prop ((f x₀ ≤ⁿ y) ϵ))
  where open approx-ordered o

 -- Lemma 4.1.16
 cor : {X : ClosenessSpace 𝓤} {Y : ClosenessSpace 𝓥}
     → (o : ordered ⟨ Y ⟩ 𝓦)
     → (f : ⟨ X ⟩ → ⟨ Y ⟩) → (ϕ : f-ucontinuous X Y f)
     → (ϵ : ℕ) → let δ = pr₁ (ϕ ϵ) in
       (δ cover-of X) 𝓥'
     → ((ϵ op-cover-of
                (Σ (_∈image f) , (subtype-closeness Y (_∈image f)
                   (λ y → being-in-the-image-is-prop y f))))
             (subtype-ordered {_} {_} {_} {Y} (_∈image f) o)
               (𝓥 ⊔ 𝓥') 𝓦')
 cor {𝓤} {𝓥} {𝓦} {𝓥'} {𝓦'} {X} {Y} o f ϕ ϵ (X' , g , η)
  = ((Σ y ꞉ ⟨ Y ⟩ , (Σ x' ꞉ X' , B Y ϵ (f (g x')) y))
  , (λ (y , x' , b) → y , ∣ g x' , {!!} ∣)
  , {!!})

{- (image (f ∘ g)
  , (λ (y , y∈i) → y , ∥∥-induction (λ _ → ∃-is-prop)
                     (λ (x , e) → ∣ g x , e ∣)
                     y∈i)
  , λ (y , y∈i) → (y , (∥∥-induction (λ _ → ∃-is-prop)
                     (λ (x , e) → ∣ pr₁ (η x) ,
                       ({!!} ∙ {!!}) ∣)
                     y∈i)) , {!!}) -}
  , {!!}
  , {!!}
  where δ = pr₁ (ϕ ϵ)


-- Different strategy:

\end{code}

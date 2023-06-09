\begin{code}

{-# OPTIONS --without-K --exact-split
            --no-sized-types --no-guardedness --auto-inline
            --allow-unsolved-metas #-}

open import MLTT.Spartan
open import UF.FunExt
open import NotionsOfDecidability.Complemented
open import TypeTopology.DiscreteAndSeparated
open import Notation.Order
open import Naturals.Order
open import Naturals.Properties
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

-- Definition 4.1.4
is-preorder : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇ 
is-preorder _≤_ = reflexive _≤_
                × transitive _≤_
                × is-prop-valued _≤_

-- Definition 4.1.5
is-linear-order : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇
is-linear-order {_} {_} {X} _≤_
 = is-preorder _≤_
 × ((x y : X) → (x ≤ y) + (y ≤ x))

-- Lemma 4.1.8
_≤𝔽_ : {n : ℕ} → 𝔽 n → 𝔽 n → 𝓤₀  ̇
_≤𝔽_ {succ n} (inl x) y = 𝟙
_≤𝔽_ {succ n} (inr x) (inl y) = 𝟘
_≤𝔽_ {succ n} (inr x) (inr y) = x ≤𝔽 y

≤𝔽-is-linear-order : {n : ℕ} → is-linear-order (_≤𝔽_ {n})
≤𝔽-is-linear-order {n} = (r , t , p) , l
 where
  r : {n : ℕ} → reflexive (_≤𝔽_ {n})
  r {succ n} (inl x) = ⋆
  r {succ n} (inr x) = r x
  t : {n : ℕ} → transitive (_≤𝔽_ {n})
  t {succ n} (inl x) y z _ _ = ⋆
  t {succ n} (inr x) (inr y) (inr z)
   = t x y z
  p : {n : ℕ} → is-prop-valued (_≤𝔽_ {n})
  p {succ n} (inl x) y = 𝟙-is-prop
  p {succ n} (inr x) (inl y) = 𝟘-is-prop
  p {succ n} (inr x) (inr y) = p x y
  l : {n : ℕ} → (x y : 𝔽 n) → (x ≤𝔽 y) + (y ≤𝔽 x)
  l {succ n} (inl x) y = inl ⋆
  l {succ n} (inr x) (inl y) = inr ⋆
  l {succ n} (inr x) (inr y) = l x y

-- Lemma 4.1.9
inclusion-order : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                → (f : X → Y) (_≤_ : Y → Y → 𝓦 ̇)
                → X → X → 𝓦 ̇
inclusion-order f _≤_ x₁ x₂ = f x₁ ≤ f x₂

inclusion-order-is-linear-order : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                                → (_≤_ : Y → Y → 𝓦 ̇) → is-linear-order _≤_
                                → is-linear-order (inclusion-order f _≤_)
inclusion-order-is-linear-order
 {_} {_} {_} {X} {Y} f _≤_ ((p , r , t) , l)
 = (r→ , t→ , p→) , l→
 where
  r→ : reflexive (inclusion-order f _≤_)
  r→ x = p (f x)
  t→ : transitive (inclusion-order f _≤_)
  t→ x y z = r (f x) (f y) (f z)
  p→ : is-prop-valued (inclusion-order f _≤_)
  p→ x y = t (f x) (f y)
  l→ : (x y : X) → inclusion-order f _≤_ x y + inclusion-order f _≤_ y x
  l→ x y = l (f x) (f y)

-- Corollary 4.1.10
finite-order : {F : 𝓤 ̇ } → finite-discrete F → F → F → 𝓤₀  ̇
finite-order (n , _ , (h , _) , _) = inclusion-order h _≤𝔽_ 

finite-order-is-linear-order : {F : 𝓤 ̇ } → (f : finite-discrete F)
                             → is-linear-order (finite-order f)
finite-order-is-linear-order (n , _ , (h , _) , _)
 = inclusion-order-is-linear-order h _≤𝔽_ ≤𝔽-is-linear-order

-- Definition 4.1.11
_∼ⁿ_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇
(α ∼ⁿ β) n = (i : ℕ) → i < n → α i ≡ β i

_<𝔽_ : {n : ℕ} → 𝔽 n → 𝔽 n → 𝓤₀ ̇
_<𝔽_ {succ n} (inl x) (inl y) = 𝟘
_<𝔽_ {succ n} (inl x) (inr y) = 𝟙
_<𝔽_ {succ n} (inr x) (inl y) = 𝟘
_<𝔽_ {succ n} (inr x) (inr y) = x <𝔽 y

is-strict-order : {X : 𝓤  ̇ } → (X → X → 𝓦  ̇ ) → 𝓤 ⊔ 𝓦  ̇ 
is-strict-order {_} {_} {X} _<_
 = ((x : X) → ¬ (x < x))
 × transitive _<_
 × ((x y : X) → x < y → ¬ (y < x))
 × is-prop-valued _<_

<𝔽-is-strict-order : {n : ℕ} → is-strict-order (_<𝔽_ {n})
<𝔽-is-strict-order = i , t , a , p
 where
  i : {n : ℕ} → (x : 𝔽 n) → ¬ (x <𝔽 x)
  i {succ n} (inl x) = id
  i {succ n} (inr x) = i x
  t : {n : ℕ} → transitive (_<𝔽_ {n})
  t {succ n} (inl x) (inl y) (inl z) _   = id
  t {succ n} (inl x) (inl y) (inr z) _ _ = ⋆
  t {succ n} (inl x) (inr y) (inl z) _ = id
  t {succ n} (inl x) (inr y) (inr z) _ _ = ⋆
  t {succ n} (inr x) (inl y) (inl z) _ = id
  t {succ n} (inr x) (inr y) (inl z) _ = id
  t {succ n} (inr x) (inr y) (inr z) = t x y z
  a : {n : ℕ} → (x y : 𝔽 n) → x <𝔽 y → ¬ (y <𝔽 x)
  a {succ n} (inl x) (inr y) x<y = id
  a {succ n} (inr x) (inr y) x<y = a x y x<y
  p : {n : ℕ} → is-prop-valued (_<𝔽_ {n})
  p {succ n} (inl x) (inl y) = 𝟘-is-prop
  p {succ n} (inl x) (inr y) = 𝟙-is-prop
  p {succ n} (inr x) (inl y) = 𝟘-is-prop
  p {succ n} (inr x) (inr y) = p x y

finite-strict-order : {F : 𝓤 ̇ } → finite-discrete F
                    → F → F → 𝓤₀ ̇
finite-strict-order (n , _ , (h , _) , _) = inclusion-order h _<𝔽_

inclusion-order-is-strict-order
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → (_<_ : Y → Y → 𝓦 ̇) → is-strict-order _<_
 → is-strict-order (inclusion-order f _<_)
inclusion-order-is-strict-order
 {_} {_} {_} {X} {Y} f _<_ (i , t , a , p)
 = i→ , t→ , a→ , p→
 where
  i→ : (x : X) → ¬ inclusion-order f _<_ x x
  i→ x e = i (f x) e
  t→ : transitive (inclusion-order f _<_)
  t→ x y z = t (f x) (f y) (f z)
  a→ : (x y : X) → inclusion-order f _<_ x y → ¬ inclusion-order f _<_ y x
  a→ x y = a (f x) (f y)
  p→ : is-prop-valued (inclusion-order f _<_)
  p→ x y = p (f x) (f y)
  

finite-strict-order-is-strict-order
 : {F : 𝓤 ̇ } → (f : finite-discrete F)
 → is-strict-order (finite-strict-order f)
finite-strict-order-is-strict-order (n , _ , (h , _) , _)
 = inclusion-order-is-strict-order h _<𝔽_ <𝔽-is-strict-order

finite-lexicorder : {F : 𝓤 ̇ } → finite-discrete F
                  → (ℕ → F) → (ℕ → F) → 𝓤  ̇ 
finite-lexicorder f α β
 = (α ∼ β)
 + (Σ n ꞉ ℕ , ((α ∼ⁿ β) n × finite-strict-order f (α n) (β n)))

-- Lemma 4.1.12
𝔽-is-set : {n : ℕ} → is-set (𝔽 n)
𝔽-is-set {succ n} = +-is-set 𝟙 (𝔽 n) 𝟙-is-set 𝔽-is-set

finite-is-set : {F : 𝓤 ̇ } → (f : finite-discrete F) → is-set F
finite-is-set (n , f) = equiv-to-set (≃-sym f) 𝔽-is-set

finite-lexicorder-is-preorder : {F : 𝓤 ̇ } (f : finite-discrete F)
                              → is-preorder (finite-lexicorder f)
finite-lexicorder-is-preorder f@(n , _ , (h , _) , _) = r , t , p
 where
  _≤F_ = finite-order f
  _<F_ = finite-strict-order f
  ≤F-preorder = pr₁ (finite-order-is-linear-order f)
  ≤F-trans = (pr₁ ∘ pr₂) ≤F-preorder
  <F-strict-order = finite-strict-order-is-strict-order f
  <F-irref = pr₁ <F-strict-order
  <F-trans = (pr₁ ∘ pr₂) <F-strict-order
  <F-anti  = (pr₁ ∘ pr₂ ∘ pr₂) <F-strict-order
  <F-prop-valued = (pr₂ ∘ pr₂ ∘ pr₂) <F-strict-order
  r : reflexive (finite-lexicorder f)
  r x = inl (λ _ → refl)
  t : transitive (finite-lexicorder f)
  t x y z (inl u) (inl v) = inl (λ n → u n ∙ v n)
  t x y z (inl u) (inr (n , v , w))
   = inr (n , (λ i i<n → u i ∙ v i i<n)
            , transport (_<F z n) (u n ⁻¹) w)
  t x y z (inr (n , u , v)) (inl e)
   = inr (n , (λ i i<n → u i i<n ∙ e i)
            , transport (x n <F_) (e n) v)
  t x y z (inr (n , u , v)) (inr (m , w , e)) with <-trichotomous n m
  ... | inl n<m
   = inr (n , (λ i i<n → u i i<n
                       ∙ w i (≤-trans (succ i) n m i<n
                           (<-coarser-than-≤ n m n<m)))
            , transport (x n <F_) (w n n<m) v)
  ... | inr (inl refl)
   = inr (n , (λ i i<n → u i i<n ∙ w i i<n)
            , <F-trans _ _ _ v e)
  ... | inr (inr m<n)
   = inr (m , (λ i i<m → u i (≤-trans (succ i) m n i<m
                           (<-coarser-than-≤ m n m<n))
                       ∙ w i i<m)
            , transport (_<F z m) (u m m<n ⁻¹) e)
  p : is-prop-valued (finite-lexicorder f)
  p x y = +-is-prop a b c
   where
    a : _
    a = Π-is-prop (fe _ _) (λ _ → finite-is-set f)
    b : _
    b (n , u , v) (m , w , e)
     = to-subtype-＝
        (λ _ → ×-is-prop
          (Π-is-prop (fe _ _)
            (λ _ → Π-is-prop (fe _ _)
              (λ _ → finite-is-set f)))
          (<F-prop-valued (x _) (y _)))
            (Cases (<-trichotomous n m)
              (λ n<m → 𝟘-elim (<F-irref (y n) (transport (_<F y n) (w n n<m) v)))
              (cases id
              (λ m<n → 𝟘-elim (<F-irref (x m) (transport (x m <F_) (u m m<n ⁻¹) e)))))
    c : _
    c g (n , w , v) = <F-irref (y n) (transport (_<F y n) (g n) v)

-- Lemma 4.1.13
-- TODO

-- Definition 4.1.14
is-approx-order : (X : ClosenessSpace 𝓤)
                → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
                → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
                → 𝓤 ⊔ 𝓦 ⊔ 𝓦'  ̇
is-approx-order X _≤_ _≤ⁿ_
 = is-preorder _≤_
 × ((ϵ : ℕ) → is-linear-order (λ x y → (x ≤ⁿ y) ϵ))
 × ((ϵ : ℕ) (x y : ⟨ X ⟩) →   B X ϵ x y → (x ≤ⁿ y) ϵ)
 × ((ϵ : ℕ) (x y : ⟨ X ⟩) → ¬ B X ϵ x y → (x ≤ⁿ y) ϵ ⇔ x ≤ y)

-- Make clearer in thesis:
approx-order-refl : (X : ClosenessSpace 𝓤)
                  → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
                  → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
                  → is-approx-order X _≤_ _≤ⁿ_
                  → (ϵ : ℕ) (x : ⟨ X ⟩) → (x ≤ⁿ x) ϵ
approx-order-refl X _≤_ _≤ⁿ_ (p , l , c , a) ϵ x
 = c ϵ x x (B-refl X ϵ x)

approx-order-trans : (X : ClosenessSpace 𝓤)
                   → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
                   → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
                   → is-approx-order X _≤_ _≤ⁿ_
                   → (ϵ : ℕ) (x y z : ⟨ X ⟩)
                   → (x ≤ⁿ y) ϵ → (y ≤ⁿ z) ϵ → (x ≤ⁿ z) ϵ
approx-order-trans X _≤_ _≤ⁿ_ (p , l , c , a) ϵ
 = (pr₁ ∘ pr₂ ∘ pr₁) (l ϵ)

approx-order-linear : (X : ClosenessSpace 𝓤)
                    → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
                    → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
                    → is-approx-order X _≤_ _≤ⁿ_
                    → (ϵ : ℕ) (x y : ⟨ X ⟩)
                    → (x ≤ⁿ y) ϵ + (y ≤ⁿ x) ϵ
approx-order-linear X _≤_ _≤ⁿ_ (_ , l , _ , _) ϵ
 = pr₂ (l ϵ)

-- Lemma 4.1.15
apart-total : {X : ClosenessSpace 𝓤}
            → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
            → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
            → is-approx-order X _≤_ _≤ⁿ_
            → (ϵ : ℕ) (x y : ⟨ X ⟩) 
            → ¬ B X ϵ x y → (x ≤ y) + (y ≤ x)
apart-total {_} {_} {_} {X} _≤_ _≤ⁿ_ (p , l , c , a) ϵ x y ¬Bϵxy
 = Cases (pr₂ (l ϵ) x y)
     (inl ∘ pr₁ (a ϵ x y ¬Bϵxy))
     (inr ∘ pr₁ (a ϵ y x λ Bϵxy → ¬Bϵxy (B-sym X ϵ y x Bϵxy)))

-- Definition 4.1.16
-- TODO

-- Lemma 4.1.17
-- TODO

-- Definition 4.1.18
is-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (_≤_ : Y → Y → 𝓦 ̇ ) → (X → Y) → X → 𝓤 ⊔ 𝓦  ̇
is-global-minimal {𝓤} {𝓥} {𝓦'} {X} _≤_ f x₀ = (x : X) → f x₀ ≤ f x

has-global-minimal : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (_≤_ : Y → Y → 𝓦 ̇ ) → (X → Y) → 𝓤 ⊔ 𝓦  ̇
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
    γ (inr x) = ≤𝔽-trans (f (inl ⋆)) (f (inr x'₀)) (f (inr x)) ⋆≤x'₀ (m x)

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
... | (x₀ , γ₀) = g x₀ , λ x → transport (f (g x₀) ≤_) (ap f (η x)) (γ₀ (h x))

-- Definition 4.1.20
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
  γ (inl ⋆) = approx-order-refl Y _≤_ _≤ⁿ_ a ϵ (f (inl ⋆)) 
𝔽-ϵ-global-minimal (succ (succ n)) _ Y _≤_ _≤ⁿ_ a ϵ f 
 with 𝔽-ϵ-global-minimal (succ n) (inl ⋆) Y _≤_ _≤ⁿ_ a ϵ (f ∘ inr) 
... | (x₀ , m)
 = Cases (approx-order-linear Y _≤_ _≤ⁿ_ a ϵ (f (inr x₀)) (f (inl ⋆)))
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
    γ (inl ⋆) = approx-order-refl Y _≤_ _≤ⁿ_ a ϵ (f (inl ⋆))
    γ (inr x) = approx-order-trans Y _≤_ _≤ⁿ_ a ϵ
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
 : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
 → (_≤_  : ⟨ Y ⟩ → ⟨ Y ⟩ → 𝓦 ̇ )
 → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦'  ̇ )
 → is-approx-order Y _≤_ _≤ⁿ_
 → (ϵ : ℕ) → (f : ⟨ X ⟩ → ⟨ Y ⟩) (ϕ : f-ucontinuous X Y f)
 → let δ = pr₁ (ϕ ϵ) in ((X' , g , _) : (δ cover-of X) 𝓤')
 → finite-discrete X'
 → (x : ⟨ X ⟩) → Σ x' ꞉ X' , (f (g x') ≤ⁿ f x) ϵ
cover-continuity-lemma
 X Y _≤_ _≤ⁿ_ (_ , _ , c , a) ϵ f ϕ (X' , g , η) e x
 = (pr₁ (η x))
 , c ϵ (f (g (pr₁ (η x)))) (f x)
     (B-sym Y ϵ (f x) (f (g (pr₁ (η x))))
       (pr₂ (ϕ ϵ) x (g (pr₁ (η x)))
         (pr₂ (η x))))

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
 , (λ x → approx-order-trans Y _≤_ _≤ⁿ_ a ϵ
            (f (g x'₀)) (f (g (h x))) (f x)
            (m (h x)) (h-min x))
 where
  δ : ℕ
  δ = pr₁ (ϕ ϵ)
  δ-cover : (δ cover-of X) 𝓤'
  δ-cover = pr₁ (t δ)
  X' : 𝓤'  ̇
  X' = pr₁ δ-cover
  X'-is-δ-cover : X' is δ cover-of X
  X'-is-δ-cover  = pr₂ δ-cover
  X'-is-finite : finite-discrete X'
  X'-is-finite = pr₂ (t δ)
  g : X' → ⟨ X ⟩
  g = pr₁ X'-is-δ-cover
  η : (x : ⟨ X ⟩) → Σ x' ꞉ X' , (f (g x') ≤ⁿ f x) ϵ
  η = cover-continuity-lemma X Y _≤_ _≤ⁿ_ a ϵ f ϕ δ-cover X'-is-finite
  h : ⟨ X ⟩ → X'
  h x = pr₁ (η x)
  h-min : (x : ⟨ X ⟩) → (f (g (h x)) ≤ⁿ f x) ϵ
  h-min x = pr₂ (η x)
  first  : has ϵ global-minimal _≤ⁿ_ (f ∘ g)
  first  = F-ϵ-global-minimal Y (h x₁) X'-is-finite _≤_ _≤ⁿ_ a ϵ (f ∘ g)
  x'₀ : X'
  x'₀ = pr₁ first
  m  : is ϵ global-minimal _≤ⁿ_ (f ∘ g) x'₀
  m  = pr₂ first
\end{code}

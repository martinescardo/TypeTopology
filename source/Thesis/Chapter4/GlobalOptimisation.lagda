\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

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
open import MLTT.Plus-Properties
open import UF.Equiv

module Thesis.Chapter4.GlobalOptimisation (fe : FunExt) where

open import Thesis.Chapter2.FiniteDiscrete
open import Thesis.Chapter3.ClosenessSpaces fe
open import Thesis.Chapter3.ClosenessSpaces-Examples fe
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

inclusion-order-is-linear-order
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
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
  l→ : (x y : X) → inclusion-order f _≤_ x y
                 + inclusion-order f _≤_ y x
  l→ x y = l (f x) (f y)

-- Corollary 4.1.10
finite-order : {F : 𝓤 ̇ } → finite-discrete F → F → F → 𝓤₀  ̇
finite-order (n , _ , (h , _) , _) = inclusion-order h _≤𝔽_ 

finite-order-is-linear-order : {F : 𝓤 ̇ } → (f : finite-discrete F)
                             → is-linear-order (finite-order f)
finite-order-is-linear-order (n , _ , (h , _) , _)
 = inclusion-order-is-linear-order h _≤𝔽_ ≤𝔽-is-linear-order

-- Definition 4.1.11
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
  a→ : (x y : X) →   inclusion-order f _<_ x y
                 → ¬ inclusion-order f _<_ y x
  a→ x y = a (f x) (f y)
  p→ : is-prop-valued (inclusion-order f _<_)
  p→ x y = p (f x) (f y)
  
finite-strict-order-is-strict-order
 : {F : 𝓤 ̇ } → (f : finite-discrete F)
 → is-strict-order (finite-strict-order f)
finite-strict-order-is-strict-order (n , _ , (h , _) , _)
 = inclusion-order-is-strict-order h _<𝔽_ <𝔽-is-strict-order

discrete-lexicorder : {F : 𝓤 ̇ } → is-discrete F
                    → (_<_ : F → F → 𝓥 ̇ )
                    → (ℕ → F) → (ℕ → F) → 𝓤 ⊔ 𝓥  ̇ 
discrete-lexicorder f _<_ α β
 = (α ∼ β) + (Σ n ꞉ ℕ , ((α ∼ⁿ β) n × (α n) < (β n)))

-- TODO : Put in paper
discrete-lexicorder-is-preorder
 : {D : 𝓤 ̇ } (d : is-discrete D) → is-set D
 → (_<_ : D → D → 𝓥 ̇ ) → is-strict-order _<_
 → is-preorder (discrete-lexicorder d _<_)
discrete-lexicorder-is-preorder d s _<_ (i' , t' , a' , p')
 = r , t , p
 where
  r : reflexive (discrete-lexicorder d _<_)
  r x = inl (λ _ → refl)
  t : transitive (discrete-lexicorder d _<_)
  t x y z (inl x∼y) (inl y∼z)
   = inl (λ i → x∼y i ∙ y∼z i)
  t x y z (inl x∼y) (inr (n , y∼ⁿz , yn<zn))
   = inr (n , (λ i i<n → x∼y i ∙ y∼ⁿz i i<n)
            , transport (_< z n) (x∼y n ⁻¹) yn<zn)
  t x y z (inr (n , x∼ⁿy , xn<yn)) (inl y∼z)
   = inr (n , (λ i i<n → x∼ⁿy i i<n ∙ y∼z i)
            , transport (x n <_) (y∼z n) xn<yn)
  t x y z (inr (n , x∼ⁿy , xn<yn))
          (inr (m , y∼ᵐz , ym<zm)) with <-trichotomous n m
  ... | inl n<m
   = inr (n , (λ i i<n → x∼ⁿy i i<n
                       ∙ y∼ᵐz i (<-trans i n m i<n n<m))
            , transport (x n <_) (y∼ᵐz n n<m) xn<yn)
  ... | inr (inl refl)
   = inr (n , (λ i i<n → x∼ⁿy i i<n ∙ y∼ᵐz i i<n)
            , t' (x n) (y n) (z n) xn<yn ym<zm)
  ... | inr (inr m<n )
   = inr (m , (λ i i<m → x∼ⁿy i (<-trans i m n i<m m<n)
                       ∙ y∼ᵐz i i<m)
            , transport (_< z m) (x∼ⁿy m m<n ⁻¹) ym<zm)
  p : is-prop-valued (discrete-lexicorder d _<_)
  p x y = +-is-prop a b c
   where
    a : _
    a = Π-is-prop (fe _ _) (λ _ → s)
    b : _
    b (n , u , v) (m , w , e)
     = to-subtype-＝
        (λ _ → ×-is-prop
          (Π-is-prop (fe _ _)
            (λ _ → Π-is-prop (fe _ _)
              (λ _ → s)))
          (p' (x _) (y _)))
            (Cases (<-trichotomous n m)
              (λ n<m → 𝟘-elim (i' (y n)
                         (transport (_< y n) (w n n<m) v)))
              (cases id
              (λ m<n → 𝟘-elim (i' (x m)
                         (transport (x m <_) (u m m<n ⁻¹) e)))))
    c : _
    c g (n , w , v) = i' (y n) (transport (_< y n) (g n) v)

-- Lemma 4.1.12


finite-lexicorder-is-preorder
 : {F : 𝓤 ̇ } (f : finite-discrete F)
 → is-preorder (discrete-lexicorder
                 (finite-discrete-is-discrete f)
                 (finite-strict-order f))
finite-lexicorder-is-preorder f
 = discrete-lexicorder-is-preorder
     (finite-discrete-is-discrete f)
     (finite-is-set f)
     (finite-strict-order f)
     (finite-strict-order-is-strict-order f)

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
 × ((ϵ : ℕ) (x y : ⟨ X ⟩) →   C X ϵ x y → (x ≤ⁿ y) ϵ)
 × ((ϵ : ℕ) (x y : ⟨ X ⟩) → ¬ C X ϵ x y → (x ≤ⁿ y) ϵ ⇔ x ≤ y)

-- Make clearer in thesis:
approx-order-refl : (X : ClosenessSpace 𝓤)
                  → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
                  → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇ )
                  → is-approx-order X _≤_ _≤ⁿ_
                  → (ϵ : ℕ) (x : ⟨ X ⟩) → (x ≤ⁿ x) ϵ
approx-order-refl X _≤_ _≤ⁿ_ (p , l , c , a) ϵ x
 = c ϵ x x (C-refl X ϵ x)

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
            → ¬ C X ϵ x y → (x ≤ y) + (y ≤ x)
apart-total {_} {_} {_} {X} _≤_ _≤ⁿ_ (p , l , c , a) ϵ x y ¬Bϵxy
 = Cases (pr₂ (l ϵ) x y)
     (inl ∘ pr₁ (a ϵ x y ¬Bϵxy))
     (inr ∘ pr₁ (a ϵ y x λ Bϵxy → ¬Bϵxy (C-sym X ϵ y x Bϵxy)))

-- Definition 4.1.16
-- TODO
discrete-approx-lexicorder : {F : 𝓤 ̇ } → is-discrete F
                           → (_<_ : F → F → 𝓥 ̇ )
                           → (ℕ → F) → (ℕ → F) → ℕ → 𝓤 ⊔ 𝓥  ̇
discrete-approx-lexicorder d _<'_ α β n
 = (α ∼ⁿ β) n + (Σ i ꞉ ℕ , ((i < n) × (α ∼ⁿ β) i × (α i) <' (β i)))

-- ################
-- Move to closeness functions file:



-- ################
discrete-approx-lexicorder-is-approx-order
 : {D : 𝓤 ̇ } (d : is-discrete D) (s : is-set D)
 → (_<_ : D → D → 𝓥 ̇ ) (s : is-strict-order _<_)
 → ((x y : D) → (x < y) + (x ＝ y) + (y < x))
 → is-approx-order
     (ℕ→D-ClosenessSpace d)
     (discrete-lexicorder d _<_)
     (discrete-approx-lexicorder d _<_)
discrete-approx-lexicorder-is-approx-order
 {𝓤} {𝓥} {D} d s _<'_ s'@(i' , t' , a' , p') l'
 = discrete-lexicorder-is-preorder d s _<'_ s'
 , (λ ϵ → (r ϵ , ((t ϵ) , (p ϵ))) , l ϵ)
 , c
 , a
 where
  r : (n : ℕ)
    → reflexive (λ x y → discrete-approx-lexicorder d _<'_ x y n)
  r n x = inl (λ _ _ → refl)
  t : (n : ℕ)
    → transitive (λ x y → discrete-approx-lexicorder d _<'_ x y n)
  t n x y z (inl x∼ⁿy) (inl y∼ᵐz)
   = inl (λ i i<n → x∼ⁿy i i<n ∙ y∼ᵐz i i<n)
  t n x y z (inl x∼ⁿy) (inr (i , i<n , y∼ⁱz , yi<zi))
   = inr (i , i<n , (λ j j<i → x∼ⁿy j (<-trans j i n j<i i<n)
                             ∙ y∼ⁱz j j<i)
            , transport (_<' z i) (x∼ⁿy i i<n ⁻¹) yi<zi)
  t n x y z (inr (i , i<n , x∼ⁱy , xi<yi)) (inl y∼ⁿz)
   = inr (i , i<n
            , (λ j j<i → x∼ⁱy j j<i ∙ y∼ⁿz j (<-trans j i n j<i i<n))
            , transport (x i <'_) (y∼ⁿz i i<n) xi<yi)
  t n x y z (inr (i , i<n , x∼ⁱy , xi<yi))
            (inr (k , k<n , y∼ᵏz , yk<zk)) with <-trichotomous i k
  ... | inl i<k
   = inr (i , i<n
            , (λ j j<i → x∼ⁱy j j<i
                       ∙ y∼ᵏz j (<-trans j i k j<i i<k))
            , transport (x i <'_) (y∼ᵏz i i<k) xi<yi)
  ... | inr (inl refl)
   = inr (i , i<n
            , (λ j j<i → x∼ⁱy j j<i ∙ y∼ᵏz j j<i)
            , t' (x i) (y i) (z i) xi<yi yk<zk)
  ... | inr (inr k<i )
   = inr (k , k<n
            , (λ j j<k → x∼ⁱy j (<-trans j k i j<k k<i)
                       ∙ y∼ᵏz j j<k)
            , transport (_<' z k) (x∼ⁱy k k<i ⁻¹) yk<zk)
  p : (n : ℕ)
    → is-prop-valued (λ x y → discrete-approx-lexicorder d _<'_ x y n)
  p n x y = +-is-prop (a n) b c
   where
    a : (i : ℕ) → is-prop ((x ∼ⁿ y) i)
    a _ = Π-is-prop (fe _ _) (λ _ → Π-is-prop (fe _ _) (λ _ → s))
    b : _
    b (i , i<n , x∼ⁱy , xi<yi) (j , j<n , x∼ʲy , xj<yj)
     = to-subtype-＝
         (λ k → ×₃-is-prop (<-is-prop-valued k n)
           (a k)
           (p' (x k) (y k)))
         (Cases (<-trichotomous i j)
           (λ i<j → 𝟘-elim (i' (y i)
                      (transport (_<' y i) (x∼ʲy i i<j) xi<yi)))
           (cases id
           (λ j<i → 𝟘-elim (i' (y j)
                      (transport (_<' y j) (x∼ⁱy j j<i) xj<yj)))))
    c : _
    c x∼ⁿy (i , i<n , x∼ⁱy , xi<yi)
     = i' (y i) (transport (_<' y i) (x∼ⁿy i i<n) xi<yi)
  l : (n : ℕ) → (x y : ℕ → D)
    → discrete-approx-lexicorder d _<'_ x y n
    + discrete-approx-lexicorder d _<'_ y x n
  l zero x y = inl (inl (λ _ ()))
  l (succ n) x y with l n x y | l' (x n) (y n)
  ... | inl (inr (i , i<n , x∼ⁱy , xi<yi)) | _
   = inl (inr (i , <-trans i n (succ n) i<n (<-succ n)
                 , x∼ⁱy , xi<yi))
  ... | inr (inr (i , i<n , y∼ⁱx , yi<xi)) | _
   = inr (inr (i , <-trans i n (succ n) i<n (<-succ n)
                 , y∼ⁱx , yi<xi))
  ... | inl (inl x∼ⁿy) | inl xn<yn
   = inl (inr (n , <-succ n , x∼ⁿy , xn<yn))
  ... | inl (inl x∼ⁿy) | inr (inl xn=yn)
   = inl (inl (λ i i<sn →
       Cases (<-split i n i<sn)
         (x∼ⁿy i)
         (λ i=n → transport (λ - → x - ＝ y -) (i=n ⁻¹) xn=yn)))
  ... | inl (inl x∼ⁿy) | inr (inr yn<xn)
   = inr (inr (n , <-succ n
                 , (λ i i<sn → x∼ⁿy i i<sn ⁻¹) , yn<xn))
  ... | inr (inl y∼ⁿx) | inl xn<yn
   = inl (inr (n , <-succ n
                 , (λ i i<sn → y∼ⁿx i i<sn ⁻¹) , xn<yn))
  ... | inr (inl y∼ⁿx) | inr (inl xn=yn)
   = inr (inl (λ i i<sn →
       Cases (<-split i n i<sn)
         (y∼ⁿx i)
         (λ i=n → transport (λ - → y - ＝ x -) (i=n ⁻¹) (xn=yn ⁻¹))))
  ... | inr (inl y∼ⁿx) | inr (inr yn<xn)
   = inr (inr (n , <-succ n , y∼ⁿx , yn<xn))
  c : (n : ℕ) → (x y : ℕ → D)
    → C (ℕ→D-ClosenessSpace d) n x y
    → discrete-approx-lexicorder d _<'_ x y n
  c 0 x y Bnxy
   = inl (λ _ ())
  c (succ n) x y Bnxy
   = inl (𝟚-decidable₁ (discrete-decidable-seq d x y (succ n))
      (Bnxy n (ℕ-to-ℕ∞-diagonal₁ n)))
  a : (n : ℕ) → (x y : ℕ → D)
    → ¬ C (ℕ→D-ClosenessSpace d) n x y
    → discrete-approx-lexicorder d _<'_ x y n
    ⇔ discrete-lexicorder d _<'_ x y
  pr₁ (a n x y ¬Bxy) (inl x∼ⁿy)
   = 𝟘-elim (¬Bxy (λ i i⊏n
   → decidable-𝟚₁ (discrete-decidable-seq d x y (succ i))
       (λ j j<si → x∼ⁿy j
         (≤-<-trans j i n j<si
           (⊏-gives-< i n i⊏n)))))
  pr₁ (a n x y ¬Bxy) (inr (i , i<n , x∼ⁱy , xi<yi))
   = inr (i , x∼ⁱy , xi<yi)
  pr₂ (a n x y ¬Bxy) (inl x∼y)
   = inl (λ i _ → x∼y i)
  pr₂ (a n x y ¬Bxy) (inr (i , x∼ⁱy , xi<yi))
   = Cases (<-trichotomous i n)
       (λ i<n → inr (i , i<n , x∼ⁱy , xi<yi))
       (cases
       (λ i=n → inl (λ j j<n → x∼ⁱy j (transport (j <_) (i=n ⁻¹) j<n)))
       (λ n<i → inl (λ j j<n → x∼ⁱy j (<-trans j n i j<n n<i))))

-- Lemma 4.1.17
-- TODO

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
     (C-sym Y ϵ (f x) (f (g (pr₁ (η x))))
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
  first
   = F-ϵ-global-minimal Y (h x₁) X'-is-finite _≤_ _≤ⁿ_ a ϵ (f ∘ g)
  x'₀ : X'
  x'₀ = pr₁ first
  m  : is ϵ global-minimal _≤ⁿ_ (f ∘ g) x'₀
  m  = pr₂ first
\end{code}

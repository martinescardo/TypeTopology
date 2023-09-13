\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import TypeTopology.DiscreteAndSeparated
open import Notation.Order
open import Naturals.Order
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import Quotient.Type
open import UF.Embeddings
open import UF.Equiv
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to _↑
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)

open import TWA.Thesis.Chapter2.FiniteDiscrete
open import TWA.Thesis.Chapter2.Sequences

module TWA.Thesis.Chapter4.ApproxOrder-Examples (fe : FunExt) where

open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import TWA.Thesis.Chapter3.SearchableTypes fe
open import TWA.Thesis.Chapter4.ApproxOrder fe

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

trichotomous : {X : 𝓤 ̇ } → (_<_ : X → X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
trichotomous {𝓤} {𝓥} {X} _<_
 = (x y : X) → (x < y) + (x ＝ y) + (y < x)

<𝔽-trichotomous : {n : ℕ} → trichotomous (_<𝔽_ {n})
<𝔽-trichotomous {succ n} (inl ⋆) (inl ⋆) = inr (inl refl)
<𝔽-trichotomous {succ n} (inl _) (inr _) = inl ⋆
<𝔽-trichotomous {succ n} (inr _) (inl _) = inr (inr ⋆)
<𝔽-trichotomous {succ n} (inr x) (inr y)
 = Cases (<𝔽-trichotomous x y)
     inl (cases (inr ∘ inl ∘ ap inr) (inr ∘ inr))

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

embedding-strict-order-trichotomous
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } ((f , _) : X ↪ Y)
 → (_<_ : Y → Y → 𝓦 ̇) → trichotomous _<_
 → trichotomous (inclusion-order f _<_)
embedding-strict-order-trichotomous
 {_} {_} {_} {X} {Y} (f , η) _<_ t x y
 = Cases (t (f x) (f y))
     inl (cases (inr ∘ inl ∘ λ e → ap pr₁ (f-lc x y e)) (inr ∘ inr))
 where
  f-lc : (x y : X) (e : f x ＝ f y) → x , e ＝ y , refl
  f-lc x y fx＝fy = η (f y) (x , fx＝fy) (y , refl)

finite-strict-order-is-strict-order
 : {F : 𝓤 ̇ } → (f : finite-discrete F)
 → is-strict-order (finite-strict-order f)
finite-strict-order-is-strict-order (n , _ , (h , _) , _)
 = inclusion-order-is-strict-order h _<𝔽_ <𝔽-is-strict-order

finite-strict-order-trichotomous
 : {F : 𝓤 ̇ } → (f : finite-discrete F)
 → trichotomous (finite-strict-order f)
finite-strict-order-trichotomous (n , f)
 = embedding-strict-order-trichotomous
     (≃-gives-↪ (≃-sym f))
     _<𝔽_ <𝔽-trichotomous

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
finite-lexicorder : {F : 𝓤 ̇ } (f : finite-discrete F)
                  → (ℕ → F) → (ℕ → F) → 𝓤 ⊔ 𝓤₀ ̇
finite-lexicorder f = discrete-lexicorder
                       (finite-discrete-is-discrete f)
                       (finite-strict-order f)

finite-lexicorder-is-preorder
 : {F : 𝓤 ̇ } (f : finite-discrete F)
 → is-preorder (finite-lexicorder f)
finite-lexicorder-is-preorder f
 = discrete-lexicorder-is-preorder
     (finite-discrete-is-discrete f)
     (finite-is-set f)
     (finite-strict-order f)
     (finite-strict-order-is-strict-order f)

discrete-approx-lexicorder : {F : 𝓤 ̇ } → is-discrete F
                           → (_<_ : F → F → 𝓥 ̇ )
                           → (ℕ → F) → (ℕ → F) → ℕ → 𝓤 ⊔ 𝓥  ̇
discrete-approx-lexicorder d _<'_ α β n
 = (α ∼ⁿ β) n + (Σ i ꞉ ℕ , ((i < n) × (α ∼ⁿ β) i × (α i) <' (β i)))

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

finite-approx-lexicorder : {F : 𝓤 ̇ } (f : finite-discrete F)
                         → (ℕ → F) → (ℕ → F) → ℕ → 𝓤 ⊔ 𝓤₀ ̇
finite-approx-lexicorder f
 = discrete-approx-lexicorder
     (finite-discrete-is-discrete f)
     (finite-strict-order f)

finite-approx-lexicorder-is-approx-order
 : {F : 𝓤 ̇ } (f : finite-discrete F)
 → is-approx-order
     (ℕ→D-ClosenessSpace (finite-discrete-is-discrete f))
     (finite-lexicorder f)
     (finite-approx-lexicorder f)
finite-approx-lexicorder-is-approx-order f
 = discrete-approx-lexicorder-is-approx-order
     (finite-discrete-is-discrete f)
     (finite-is-set f)
     (finite-strict-order f)
     (finite-strict-order-is-strict-order f)
     (finite-strict-order-trichotomous f)

inclusion-approx-order
 : {X : 𝓤 ̇ } {Y : ClosenessSpace 𝓥} (f : X → ⟨ Y ⟩)
 → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦  ̇)
 → X → X → ℕ → 𝓦  ̇
inclusion-approx-order f _≤ⁿ_ x y = f x ≤ⁿ f y

Σ-order : {X : 𝓤 ̇ } → (P : X → 𝓥 ̇ ) → (_≤_ : X → X → 𝓦  ̇)
        → Σ P → Σ P → 𝓦  ̇
Σ-order P _≤_ (x , _) (y , _) = x ≤ y

Σ-order-is-preorder
 : {X : 𝓤 ̇ } → (P : X → 𝓥 ̇ )
 → (_≤_ : X → X → 𝓦 ̇ ) → is-preorder _≤_
 → is-preorder (Σ-order P _≤_)
Σ-order-is-preorder P _≤_ (r' , t' , p') = r , t , p
 where
  r : reflexive (Σ-order P _≤_)
  r (x , _) = r' x
  t : transitive (Σ-order P _≤_)
  t (x , _) (y , _) (z , _) = t' x y z
  p : is-prop-valued (Σ-order P _≤_)
  p (x , _) (y , _) = p' x y

Σ-approx-order : {X : 𝓤 ̇ } → (P : X → 𝓥 ̇ ) → (_≤ⁿ_ : X → X → ℕ → 𝓦  ̇)
               → Σ P → Σ P → ℕ → 𝓦  ̇
Σ-approx-order P _≤ⁿ_ (x , _) (y , _) = x ≤ⁿ y

Σ-approx-order-is-approx-order
 : (X : ClosenessSpace 𝓤)
 → (P : ⟨ X ⟩ → 𝓥 ̇ ) → (p : (x : ⟨ X ⟩) → is-prop (P x))
 → (_≤_ : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
 → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇)
 → is-approx-order X _≤_ _≤ⁿ_
 → is-approx-order (Σ-ClosenessSpace X P p)
     (Σ-order P _≤_) (Σ-approx-order P _≤ⁿ_)
Σ-approx-order-is-approx-order
 X P p _≤_ _≤ⁿ_ (pre' , lin' , c' , a') = pre , lin , c , a
 where
  pre : is-preorder (Σ-order P _≤_)
  pre = Σ-order-is-preorder P _≤_ pre'
  lin : (ϵ : ℕ) → is-linear-order (λ x y → Σ-approx-order P _≤ⁿ_ x y ϵ)
  lin ϵ = (r' ∘ pr₁
        , (λ (x , _) (y , _) (z , _) → t' x y z)
        , λ (x , _) (y , _) → p' x y)
        , λ (x , _) (y , _) → l' x y
   where
    r' = (pr₁ ∘ pr₁)       (lin' ϵ)
    t' = (pr₁ ∘ pr₂ ∘ pr₁) (lin' ϵ)
    p' = (pr₂ ∘ pr₂ ∘ pr₁) (lin' ϵ)
    l' = pr₂               (lin' ϵ)
  c : (ϵ : ℕ) (x y : ⟨ Σ-ClosenessSpace X P p ⟩)
    →   C (Σ-ClosenessSpace X P p) ϵ x y → Σ-approx-order P _≤ⁿ_ x y ϵ
  c ϵ (x , _) (y , _) = c' ϵ x y
  a : (ϵ : ℕ) (x y : ⟨ Σ-ClosenessSpace X P p ⟩)
    → ¬ C (Σ-ClosenessSpace X P p) ϵ x y
    → Σ-approx-order P _≤ⁿ_ x y ϵ ⇔ Σ-order P _≤_ x y
  a ϵ (x , _) (y , _) = a' ϵ x y

open import MLTT.Two-Properties

ℕ→𝟚-lexicorder : (ℕ → 𝟚) → (ℕ → 𝟚) → 𝓤₀ ̇
ℕ→𝟚-lexicorder = discrete-lexicorder 𝟚-is-discrete _<₂_

ℕ∞-lexicorder : ℕ∞ → ℕ∞ → 𝓤₀ ̇
ℕ∞-lexicorder = Σ-order is-decreasing ℕ→𝟚-lexicorder

open import UF.Miscelanea

<₂-is-strict : is-strict-order _<₂_
pr₁ <₂-is-strict ₀ ()
pr₁ <₂-is-strict ₁ ()
pr₁ (pr₂ <₂-is-strict) ₀ ₀ ₀ () x₂
pr₁ (pr₂ <₂-is-strict) ₀ ₀ ₁ () x₂
pr₁ (pr₂ <₂-is-strict) ₀ ₁ ₀ ⋆ ()
pr₁ (pr₂ <₂-is-strict) ₀ ₁ ₁ ⋆ ()
pr₁ (pr₂ <₂-is-strict) ₁ ₀ ₀ () x₂
pr₁ (pr₂ <₂-is-strict) ₁ ₀ ₁ () x₂
pr₁ (pr₂ <₂-is-strict) ₁ ₁ ₀ () x₂
pr₁ (pr₂ <₂-is-strict) ₁ ₁ ₁ () x₂
pr₁ (pr₂ (pr₂ <₂-is-strict)) ₀ ₀ () x₂
pr₁ (pr₂ (pr₂ <₂-is-strict)) ₀ ₁ ⋆ ()
pr₁ (pr₂ (pr₂ <₂-is-strict)) ₁ ₀ () x₂
pr₁ (pr₂ (pr₂ <₂-is-strict)) ₁ ₁ () x₂
pr₂ (pr₂ (pr₂ <₂-is-strict)) ₀ ₀ = 𝟘-is-prop
pr₂ (pr₂ (pr₂ <₂-is-strict)) ₀ ₁ = 𝟙-is-prop
pr₂ (pr₂ (pr₂ <₂-is-strict)) ₁ ₀ = 𝟘-is-prop
pr₂ (pr₂ (pr₂ <₂-is-strict)) ₁ ₁ = 𝟘-is-prop

<₂-trichotomous : trichotomous _<₂_
<₂-trichotomous ₀ ₀ = inr (inl refl)
<₂-trichotomous ₀ ₁ = inl ⋆
<₂-trichotomous ₁ ₀ = inr (inr ⋆)
<₂-trichotomous ₁ ₁ = inr (inl refl)

ℕ→𝟚-lexicorder-is-preorder : is-preorder ℕ→𝟚-lexicorder
ℕ→𝟚-lexicorder-is-preorder
 = discrete-lexicorder-is-preorder 𝟚-is-discrete
     𝟚-is-set _<₂_ <₂-is-strict

ℕ∞-lexicorder-is-preorder : is-preorder ℕ∞-lexicorder
ℕ∞-lexicorder-is-preorder
 = Σ-order-is-preorder is-decreasing
     ℕ→𝟚-lexicorder ℕ→𝟚-lexicorder-is-preorder

ℕ→𝟚-approx-lexicorder : (ℕ → 𝟚) → (ℕ → 𝟚) → ℕ → 𝓤₀ ̇
ℕ→𝟚-approx-lexicorder = discrete-approx-lexicorder 𝟚-is-discrete _<₂_

ℕ→𝟚-approx-lexicorder-is-approx-order
 : is-approx-order ℕ→𝟚-ClosenessSpace ℕ→𝟚-lexicorder ℕ→𝟚-approx-lexicorder
ℕ→𝟚-approx-lexicorder-is-approx-order
 = discrete-approx-lexicorder-is-approx-order
     𝟚-is-discrete 𝟚-is-set _<₂_ <₂-is-strict <₂-trichotomous

ℕ∞-approx-lexicorder : ℕ∞ → ℕ∞ → ℕ → 𝓤₀ ̇
ℕ∞-approx-lexicorder
 = Σ-approx-order is-decreasing ℕ→𝟚-approx-lexicorder

ℕ∞-approx-lexicorder-is-approx-order
 : is-approx-order ℕ∞-ClosenessSpace ℕ∞-lexicorder ℕ∞-approx-lexicorder
ℕ∞-approx-lexicorder-is-approx-order
 = Σ-approx-order-is-approx-order ℕ→𝟚-ClosenessSpace
     is-decreasing (being-decreasing-is-prop (fe _ _))
     ℕ→𝟚-lexicorder ℕ→𝟚-approx-lexicorder
     ℕ→𝟚-approx-lexicorder-is-approx-order

\end{code}

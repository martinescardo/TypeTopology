[⇐ Index](../html/TWA.Thesis.index.html)

# Examples of approximate orders

```agda

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import TypeTopology.DiscreteAndSeparated
open import Notation.Order
open import Naturals.Order
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient
open import UF.Embeddings
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to _↑
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)
open import NotionsOfDecidability.Decidable
open import MLTT.Two-Properties
open import UF.Miscelanea
open import Fin.Type
open import Fin.Bishop
open import UF.PropTrunc

open import TWA.Thesis.Chapter2.Finite
open import TWA.Thesis.Chapter2.Sequences

module TWA.Thesis.Chapter4.ApproxOrder-Examples (fe : FunExt) where

open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import TWA.Thesis.Chapter3.SearchableTypes fe
open import TWA.Thesis.Chapter4.ApproxOrder fe
```

## Subtype orders

```
inclusion-order
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } → (f : X → Y) (_≤_ : Y → Y → 𝓦 ̇) → X → X → 𝓦 ̇
inclusion-order f _≤_ x₁ x₂ = f x₁ ≤ f x₂

inclusion-order-is-preorder
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → (_≤_ : Y → Y → 𝓦 ̇)
 → is-preorder _≤_
 → is-preorder (inclusion-order f _≤_)
inclusion-order-is-preorder {𝓤} {𝓥} {𝓦} {X} {Y}
 f _≤_ (r' , t' , p') = r , t , p
 where
  r : reflexive (inclusion-order f _≤_)
  r x     = r' (f x)
  t : transitive (inclusion-order f _≤_)
  t x y z = t' (f x) (f y) (f z)
  p : is-prop-valued (inclusion-order f _≤_)
  p x y   = p' (f x) (f y)

inclusion-order-is-linear-preorder
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → (_≤_ : Y → Y → 𝓦 ̇)
 → is-linear-preorder _≤_
 → is-linear-preorder (inclusion-order f _≤_)
inclusion-order-is-linear-preorder {𝓤} {𝓥} {𝓦} {X} {Y}
 f _≤_ (pre , l') = inclusion-order-is-preorder f _≤_ pre , l
 where
  l : (x y : X) → inclusion-order f _≤_ x y + inclusion-order f _≤_ y x
  l x y   = l' (f x) (f y)

inclusion-order-is-strict-order
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → (_<_ : Y → Y → 𝓦 ̇)
 → is-strict-order _<_
 → is-strict-order (inclusion-order f _<_)
inclusion-order-is-strict-order {𝓤} {𝓥} {𝓦} {X} {Y}
 f _<_ (i' , t' , a' , p') = i , t , a , p
 where
  i : (x : X) → ¬ inclusion-order f _<_ x x
  i x     = i' (f x) 
  t : transitive (inclusion-order f _<_)
  t x y z = t' (f x) (f y) (f z)
  a : (x y : X)
    → inclusion-order f _<_ x y
    → ¬ inclusion-order f _<_ y x
  a x y   = a' (f x) (f y)
  p : is-prop-valued (inclusion-order f _<_)
  p x y   = p' (f x) (f y)

embedding-strict-order-trichotomous
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } ((f , _) : X ↪ Y)
 → (_<_ : Y → Y → 𝓦 ̇) → trichotomous _<_
 → trichotomous (inclusion-order f _<_)
embedding-strict-order-trichotomous
 {𝓤} {𝓥} {𝓦} {X} {Y} (f , η) _<_ t x y
 = Cases (t (f x) (f y))
     inl (cases (inr ∘ inl ∘ λ e → ap pr₁ (f-lc x y e)) (inr ∘ inr))
 where
  f-lc : (x y : X) (e : f x ＝ f y) → x , e ＝ y , refl
  f-lc x y e = η (f y) (x , e) (y , refl)

inclusion-approx-order
 : {X : 𝓤 ̇ } {Y : ClosenessSpace 𝓥} (f : X → ⟨ Y ⟩)
 → (_≤ⁿ_ : ⟨ Y ⟩ → ⟨ Y ⟩ → ℕ → 𝓦  ̇)
 → X → X → ℕ → 𝓦  ̇ 
inclusion-approx-order f _≤ⁿ_ x y = f x ≤ⁿ f y

Σ-order : {X : 𝓤 ̇ } (P : X → 𝓥 ̇ ) (_≤_ : X → X → 𝓦  ̇)
        → Σ P → Σ P → 𝓦  ̇
Σ-order P _≤_ (x , _) (y , _) = x ≤ y

Σ-order-is-preorder
 : {X : 𝓤 ̇ } (P : X → 𝓥 ̇ ) (_≤_ : X → X → 𝓦 ̇ )
 → is-preorder _≤_
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
 → (P : ⟨ X ⟩ → 𝓥 ̇ )
 → (p : (x : ⟨ X ⟩) → is-prop (P x))
 → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇)
 → is-approx-order X _≤ⁿ_
 → is-approx-order (Σ-ClosenessSpace X P p) (Σ-approx-order P _≤ⁿ_)
Σ-approx-order-is-approx-order
 X P p' _≤ⁿ_ a = (λ ϵ → (r ϵ , t ϵ , p ϵ) , l ϵ) , d , c
 where
  r : (ϵ : ℕ) → reflexive (λ x y → Σ-approx-order P _≤ⁿ_ x y ϵ)
  r ϵ x     = ≤ⁿ-refl      X a ϵ (pr₁ x)
  t : (ϵ : ℕ) → transitive (λ x y → Σ-approx-order P _≤ⁿ_ x y ϵ)
  t ϵ x y z = ≤ⁿ-trans     X a ϵ (pr₁ x) (pr₁ y) (pr₁ z)
  p : (ϵ : ℕ) → is-prop-valued (λ x y → Σ-approx-order P _≤ⁿ_ x y ϵ)
  p ϵ x y   = ≤ⁿ-prop      X a ϵ (pr₁ x) (pr₁ y)
  l : (ϵ : ℕ) → linear (λ x y → Σ-approx-order P _≤ⁿ_ x y ϵ)
  l ϵ x y   = ≤ⁿ-linear    X a ϵ (pr₁ x) (pr₁ y)
  d : (ϵ : ℕ) (x y : Σ P) → is-decidable (Σ-approx-order P _≤ⁿ_ x y ϵ)
  d ϵ x y   = ≤ⁿ-decidable X a ϵ (pr₁ x) (pr₁ y)
  c : (ϵ : ℕ) (x y : ⟨ Σ-ClosenessSpace X P p' ⟩)
    → C (Σ-ClosenessSpace X P p') ϵ x y
    → Σ-approx-order P _≤ⁿ_ x y ϵ
  c ϵ x y   = ≤ⁿ-close X a ϵ (pr₁ x) (pr₁ y)

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 Σ-approx-order-for
  : (X : ClosenessSpace 𝓤)
  → (P : ⟨ X ⟩ → 𝓥 ̇ )
  → (p : (x : ⟨ X ⟩) → is-prop (P x))
  → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
  → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇)
  → is-approx-order-for pt X _≤_ _≤ⁿ_
  → is-approx-order-for pt
      (Σ-ClosenessSpace X P p)
      (Σ-order P _≤_)
      (Σ-approx-order P _≤ⁿ_)
 Σ-approx-order-for X P p _≤_ _≤ⁿ_ a
  = Σ-order-is-preorder P _≤_ (≤ⁿ-pre pt X a)
  , Σ-approx-order-is-approx-order X P p _≤ⁿ_ (≤ⁿ-approx pt X a)
  , f
  where
   f : is-approx-order-for' pt
         (Σ-ClosenessSpace X P p)
         (Σ-order P _≤_)
         (Σ-approx-order P _≤ⁿ_)
   f x y = ≤ⁿ-for pt X a (pr₁ x) (pr₁ y)
```

## Finite orders

```
_≤Fin_ : {n : ℕ} → Fin n → Fin n → 𝓤₀  ̇
_≤Fin_ {succ n} 𝟎 y = 𝟙
_≤Fin_ {succ n} (suc x) 𝟎 = 𝟘
_≤Fin_ {succ n} (suc x) (suc y) = x ≤Fin y

≤Fin-is-linear-preorder : {n : ℕ} → is-linear-preorder (_≤Fin_ {n})
≤Fin-is-linear-preorder {n} = (r , t , p) , l
 where
  r : {n : ℕ} → reflexive (_≤Fin_ {n})
  r {succ n} 𝟎 = ⋆
  r {succ n} (suc x) = r x
  t : {n : ℕ} → transitive (_≤Fin_ {n})
  t {succ n} 𝟎 y z _ _ = ⋆
  t {succ n} (suc x) (suc y) (suc z) = t x y z
  p : {n : ℕ} → is-prop-valued (_≤Fin_ {n})
  p {succ n} 𝟎 y = 𝟙-is-prop
  p {succ n} (suc x) 𝟎 = 𝟘-is-prop
  p {succ n} (suc x) (suc y) = p x y
  l : {n : ℕ} → (x y : Fin n) → (x ≤Fin y) + (y ≤Fin x)
  l {succ n} 𝟎 y = inl ⋆
  l {succ n} (suc x) 𝟎 = inr ⋆
  l {succ n} (suc x) (suc y) = l x y

finite-order : {F : 𝓤 ̇ } → finite-linear-order F → F → F → 𝓤₀  ̇
finite-order (n , (g , _)) = inclusion-order g _≤Fin_ 

finite-order-is-linear-preorder
 : {F : 𝓤 ̇ }
 → (f : finite-linear-order F)
 → is-linear-preorder (finite-order f)
finite-order-is-linear-preorder (n , (g , _))
 = inclusion-order-is-linear-preorder g _≤Fin_ ≤Fin-is-linear-preorder

_<Fin_ : {n : ℕ} → Fin n → Fin n → 𝓤₀ ̇
_<Fin_ {succ n} 𝟎 𝟎 = 𝟘
_<Fin_ {succ n} 𝟎 (suc x) = 𝟙
_<Fin_ {succ n} (suc x) 𝟎 = 𝟘
_<Fin_ {succ n} (suc x) (suc y) = x <Fin y

<Fin-is-strict-order : {n : ℕ} → is-strict-order (_<Fin_ {n})
<Fin-is-strict-order = i , t , a , p
 where
  i : {n : ℕ} → (x : Fin n) → ¬ (x <Fin x)
  i {succ n} 𝟎 = id
  i {succ n} (suc x) = i x
  t : {n : ℕ} → transitive (_<Fin_ {n})
  t {succ n} 𝟎 𝟎 𝟎 _                 = id
  t {succ n} 𝟎 𝟎 (suc z) _ _         = ⋆
  t {succ n} 𝟎 (suc y) 𝟎 _           = id
  t {succ n} 𝟎 (suc y) (suc z) _ _   = ⋆
  t {succ n} (suc x) 𝟎 𝟎 _           = id
  t {succ n} (suc x) (suc y) 𝟎 _     = id
  t {succ n} (suc x) (suc y) (suc z) = t x y z
  a : {n : ℕ} → (x y : Fin n) → x <Fin y → ¬ (y <Fin x)
  a {succ n} 𝟎 (suc y) x<y = id
  a {succ n} (suc x) (suc y) x<y = a x y x<y
  p : {n : ℕ} → is-prop-valued (_<Fin_ {n})
  p {succ n} 𝟎 𝟎 = 𝟘-is-prop
  p {succ n} 𝟎 (suc y) = 𝟙-is-prop
  p {succ n} (suc x) 𝟎 = 𝟘-is-prop
  p {succ n} (suc x) (suc y) = p x y

<Fin-trichotomous : {n : ℕ} → trichotomous (_<Fin_ {n})
<Fin-trichotomous {succ n} 𝟎 𝟎       = inr (inl refl)
<Fin-trichotomous {succ n} 𝟎 (suc _) = inl ⋆
<Fin-trichotomous {succ n} (suc _) 𝟎 = inr (inr ⋆)
<Fin-trichotomous {succ n} (suc x) (suc y)
 = Cases (<Fin-trichotomous x y)
     inl (cases (inr ∘ inl ∘ ap suc) (inr ∘ inr))

finite-strict-order : {F : 𝓤 ̇ } → finite-linear-order F → F → F → 𝓤₀ ̇
finite-strict-order (n , (g , _)) = inclusion-order g _<Fin_
  
finite-strict-order-is-strict-order
 : {F : 𝓤 ̇ } → (f : finite-linear-order F)
 → is-strict-order (finite-strict-order f)
finite-strict-order-is-strict-order (n , (g , _))
 = inclusion-order-is-strict-order g _<Fin_ <Fin-is-strict-order

finite-strict-order-trichotomous
 : {F : 𝓤 ̇ } → (f : finite-linear-order F)
 → trichotomous (finite-strict-order f)
finite-strict-order-trichotomous (n , f)
 = embedding-strict-order-trichotomous (≃-gives-↪ f)
     _<Fin_ <Fin-trichotomous
```

## Discrete-sequence orders

```
discrete-lexicorder : {D : 𝓤 ̇ }
                    → is-discrete D
                    → (_<_ : D → D → 𝓥 ̇ )
                    → (α β : ℕ → D)
                    → 𝓤 ⊔ 𝓥  ̇ 
discrete-lexicorder f _<_ α β
 = (α ∼ β) + (Σ n ꞉ ℕ , ((α ∼ⁿ β) n × (α n) < (β n)))

discrete-lexicorder-is-preorder
 : {D : 𝓤 ̇ } (d : is-discrete D)
 → is-set D
 → (_<_ : D → D → 𝓥 ̇ )
 → is-strict-order _<_
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
    
lexicorder-linearity-implies-LPO
 : {X : 𝓤 ̇ }
 → (f@(n , _) : finite-linear-order X)
 → n > 1
 → is-linear-preorder (discrete-lexicorder
                     (finite-is-discrete f) (finite-strict-order f))
 → LPO
lexicorder-linearity-implies-LPO
 {𝓤} {X} f@(succ (succ n) , (g , (h , η) , _)) _ s@((r , t , p) , l) α
 = Cases (l (λ _ → d₀) (ρ ∘ α))
     (cases
       (λ ₀∼α → inl (λ n → ρ-lc (₀∼α n ⁻¹)))
       (λ (i , ₀∼ⁱα , ₀<αi) → inr (i , ρ-lc (<-lemma₀ (α i) ₀<αi))))
     (cases
       (λ α∼₀ → inl (λ n → ρ-lc (α∼₀ n)))
       (λ (i , α∼ⁱ₀ , αi<₀) → 𝟘-elim (<-lemma₁ (α i) αi<₀)))
 where
  _<ₓ_ = finite-strict-order f
  γ = finite-strict-order-is-strict-order f
  d₀ d₁ : X
  d₀ = h 𝟎
  d₁ = h 𝟏
  ρ : 𝟚 → X
  ρ ₀ = d₀
  ρ ₁ = d₁
  d₀<d₁ : d₀ <ₓ d₁
  d₀<d₁ = transport (_<Fin g (h 𝟏)) (η 𝟎 ⁻¹)
            (transport (𝟎 <Fin_) (η 𝟏 ⁻¹) ⋆)
  not-zero-means-one : (a : 𝟚) → ρ a ≠ d₀ → ρ a ＝ d₁
  not-zero-means-one ₀ e = 𝟘-elim (e refl)
  not-zero-means-one ₁ _ = refl
  <-lemma₀ : (a : 𝟚) → d₀ <ₓ ρ a → ρ a ＝ d₁
  <-lemma₀ ₀   = 𝟘-elim ∘ <-irref⟨ γ ⟩ d₀
  <-lemma₀ ₁ _ = refl
  <-lemma₁ : (a : 𝟚) → ¬ (ρ a <ₓ d₀)
  <-lemma₁ ₀ = <-irref⟨ γ ⟩ d₀
  <-lemma₁ ₁ = <-anti⟨ γ ⟩ d₀ d₁ d₀<d₁
  ρ-lc : {a b : 𝟚} → ρ a ＝ ρ b → a ＝ b
  ρ-lc {₀} {₀} e = refl
  ρ-lc {₀} {₁} e
   = 𝟘-elim (<-irref⟨ γ ⟩ d₀ (transport (d₀ <ₓ_) (e ⁻¹) d₀<d₁))
  ρ-lc {₁} {₀} e
   = 𝟘-elim (<-irref⟨ γ ⟩ d₀ (transport (d₀ <ₓ_) e d₀<d₁))
  ρ-lc {₁} {₁} e = refl
 
finite-lexicorder
 : {F : 𝓤 ̇ } (f : finite-linear-order F) (d : is-discrete F)
 → (_<_ : F → F → 𝓦 ̇ )
 → (ℕ → F) → (ℕ → F) → 𝓤 ⊔ 𝓦  ̇
finite-lexicorder f d _<_ = discrete-lexicorder d _<_

discrete-approx-lexicorder : {D : 𝓤 ̇ }
                           → is-discrete D
                           → (_<_ : D → D → 𝓥 ̇ )
                           → (α β : ℕ → D)
                           → ℕ
                           → 𝓤 ⊔ 𝓥  ̇
discrete-approx-lexicorder d _<'_ α β n
 = (α ∼ⁿ β) n + (Σ i ꞉ ℕ , ((i < n) × (α ∼ⁿ β) i × (α i) <' (β i)))

discrete-approx-lexicorder-is-approx-order
 : {D : 𝓤 ̇ } (ds : is-discrete D) (s : is-set D)
 → (_<_ : D → D → 𝓥 ̇ ) (s : is-strict-linear-order _<_)
 → is-approx-order
     (ℕ→D-ClosenessSpace ds)
     (discrete-approx-lexicorder ds _<_)
discrete-approx-lexicorder-is-approx-order
 {𝓤} {𝓥} {D} ds s _<'_ s'@((i' , t' , a' , p') , l')
 = (λ ϵ → (r ϵ , ((t ϵ) , (p ϵ))) , l ϵ)
 , d
 , c
 where
  r : (n : ℕ)
    → reflexive (λ x y → discrete-approx-lexicorder ds _<'_ x y n)
  r n x = inl (λ _ _ → refl)
  t : (n : ℕ)
    → transitive (λ x y → discrete-approx-lexicorder ds _<'_ x y n)
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
    → is-prop-valued (λ x y → discrete-approx-lexicorder ds _<'_ x y n)
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
    → discrete-approx-lexicorder ds _<'_ x y n
    + discrete-approx-lexicorder ds _<'_ y x n
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
  d : (ϵ : ℕ) (x y : ℕ → D)
    → is-decidable (discrete-approx-lexicorder ds _<'_ x y ϵ)
  d ϵ x y
    = +-preserves-decidability (∼ⁿ-decidable (λ _ → ds) x y ϵ)
        (bounded-decidable-Σ
          (λ i → ×-preserves-decidability
            (∼ⁿ-decidable (λ _ → ds) x y i)
            (strict-linear-order-decidable _<'_ s' (x i) (y i)))
          ϵ)
  c : (n : ℕ) → (x y : ℕ → D)
    → C (ℕ→D-ClosenessSpace ds) n x y
    → discrete-approx-lexicorder ds _<'_ x y n
  c 0 x y Cnxy
   = inl (λ _ ())
  c (succ n) x y Cnxy
   = inl (𝟚-decidable₁ (∼ⁿ-decidable (λ _ → ds) x y (succ n))
      (Cnxy n (ℕ-to-ℕ∞-diagonal₁ n)))

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 discrete-approx-lexicorder-for'
  : {D : 𝓤 ̇ } (ds : is-discrete D) (i : is-set D)
  → (_<_ : D → D → 𝓥 ̇ )
  → is-approx-order-for' pt
      (ℕ→D-ClosenessSpace ds)
      (discrete-lexicorder ds _<_)
      (discrete-approx-lexicorder ds _<_)
 discrete-approx-lexicorder-for' ds i _<_ α β (inl α∼β)
  = ∣ (0 , λ _ _ → inl (λ n _ → α∼β n)) ∣ 
 discrete-approx-lexicorder-for' ds i _<_ α β (inr (n , α∼ⁿβ , αn<βn))
  = ∣ succ n , (λ ϵ n<ϵ → inr (n , n<ϵ , α∼ⁿβ , αn<βn)) ∣

 discrete-approx-lexicorder-for
  : {D : 𝓤 ̇ } (ds : is-discrete D) (i : is-set D)
  → (_<_ : D → D → 𝓥 ̇ ) (s : is-strict-linear-order _<_)
  → is-approx-order-for pt
      (ℕ→D-ClosenessSpace ds)
      (discrete-lexicorder ds _<_)
      (discrete-approx-lexicorder ds _<_)
 discrete-approx-lexicorder-for ds i _<_ (s , l)
  = discrete-lexicorder-is-preorder ds i _<_ s
  , discrete-approx-lexicorder-is-approx-order ds i _<_ (s , l)
  , discrete-approx-lexicorder-for' ds i _<_
```

## Specific example orders

```
ℕ→𝟚-lexicorder : (ℕ → 𝟚) → (ℕ → 𝟚) → 𝓤₀ ̇
ℕ→𝟚-lexicorder
 = discrete-lexicorder 𝟚-is-discrete _<₂_

ℕ∞-lexicorder : ℕ∞ → ℕ∞ → 𝓤₀ ̇
ℕ∞-lexicorder = Σ-order is-decreasing ℕ→𝟚-lexicorder

<₂-is-strict : is-strict-order _<₂_
<₂-is-strict
 = <₂-irref 
 , <₂-trans
 , <₂-anti
 , λ _ _ → <₂-is-prop-valued
 where
  <₂-irref : (x : 𝟚) → ¬ (x <₂ x)
  <₂-irref x x<x = zero-is-not-one (pr₁ γ ⁻¹ ∙ pr₂ γ)
   where
    γ : (x ＝ ₀) × (x ＝ ₁)
    γ = <₂-criterion-converse x<x
  <₂-anti : (x y : 𝟚) → x <₂ y → ¬ (y <₂ x)
  <₂-anti x y x<y y<x = zero-is-not-one (x₀ ⁻¹ ∙ x₁)
   where
    x₀ : x ＝ ₀
    x₀ = pr₁ (<₂-criterion-converse x<y)
    x₁ : x ＝ ₁
    x₁ = pr₂ (<₂-criterion-converse y<x)

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
 : is-approx-order 𝟚ᴺ-ClosenessSpace ℕ→𝟚-approx-lexicorder
ℕ→𝟚-approx-lexicorder-is-approx-order
 = discrete-approx-lexicorder-is-approx-order
     𝟚-is-discrete 𝟚-is-set _<₂_ (<₂-is-strict , <₂-trichotomous)

ℕ∞-approx-lexicorder : ℕ∞ → ℕ∞ → ℕ → 𝓤₀ ̇
ℕ∞-approx-lexicorder
 = Σ-approx-order is-decreasing ℕ→𝟚-approx-lexicorder

ℕ∞-approx-lexicorder-is-approx-order
 : is-approx-order ℕ∞-ClosenessSpace ℕ∞-approx-lexicorder
ℕ∞-approx-lexicorder-is-approx-order
 = Σ-approx-order-is-approx-order 𝟚ᴺ-ClosenessSpace
     is-decreasing (being-decreasing-is-prop (fe _ _))
     ℕ→𝟚-approx-lexicorder
     ℕ→𝟚-approx-lexicorder-is-approx-order
```

[⇐ Index](../html/TWA.Thesis.index.html)

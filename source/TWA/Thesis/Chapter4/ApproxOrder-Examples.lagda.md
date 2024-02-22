[⇐ Index](../html/TWA.Thesis.index.html)

# Examples of approximate orders

```agda

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.DiscreteAndSeparated
open import Notation.Order
open import Naturals.Order
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Sets
open import Quotient.Type using (is-prop-valued;is-equiv-relation)
open import UF.Embeddings
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to _↑
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)
open import NotionsOfDecidability.Decidable
open import MLTT.Two-Properties
open import Fin.Type
open import Fin.Bishop
open import UF.PropTrunc
open import Taboos.WLPO
open import Taboos.BasicDiscontinuity

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

embedding-order-is-partial-order
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → is-embedding f
 → (_≤_ : Y → Y → 𝓦 ̇)
 → is-partial-order _≤_
 → is-partial-order (inclusion-order f _≤_)
embedding-order-is-partial-order {𝓤} {𝓥} {𝓦} {X} {Y}
 f i _≤_ (pre , a') = inclusion-order-is-preorder f _≤_ pre , a
 where
  a : antisymmetric (inclusion-order f _≤_)
  a x y fx≤fy fy≤fx
   = ap pr₁ (i (f y) (x , a' (f x) (f y) fx≤fy fy≤fx) (y , refl))

inclusion-order-is-linear-preorder
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → (_≤_ : Y → Y → 𝓦 ̇)
 → is-linear-preorder _≤_
 → is-linear-preorder (inclusion-order f _≤_)
inclusion-order-is-linear-preorder {𝓤} {𝓥} {𝓦} {X} {Y}
 f _≤_ (pre , l') = inclusion-order-is-preorder f _≤_ pre , l
 where
  l : linear (inclusion-order f _≤_)
  l x y = l' (f x) (f y)

embedding-order-is-linear-order
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → is-embedding f
 → (_≤_ : Y → Y → 𝓦 ̇)
 → is-linear-order _≤_
 → is-linear-order (inclusion-order f _≤_)
embedding-order-is-linear-order {𝓤} {𝓥} {𝓦} {X} {Y}
 f i _≤_ ((pre , a') , l')
  = embedding-order-is-partial-order f i _≤_ (pre , a')
  , pr₂ (inclusion-order-is-linear-preorder f _≤_ (pre , l'))

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

module ΣOrder-Relates (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open ApproxOrder-Relates pt

 Σ-approx-order-relates
  : (X : ClosenessSpace 𝓤)
  → (P : ⟨ X ⟩ → 𝓥 ̇ )
  → (p : (x : ⟨ X ⟩) → is-prop (P x))
  → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦'  ̇)
  → (a : is-approx-order X _≤ⁿ_)
  → (_≤_  : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
  → (i : is-preorder _≤_)
  → approx-order-relates X _≤ⁿ_ a _≤_ i
  → approx-order-relates
      (Σ-ClosenessSpace X P p)
      (Σ-approx-order P _≤ⁿ_)
      (Σ-approx-order-is-approx-order X P p _≤ⁿ_ a)
      (Σ-order P _≤_)
      (Σ-order-is-preorder P _≤_ i)
 Σ-approx-order-relates X P p _≤ⁿ_ a _≤_ i (rel→ , rel←)
  = (λ (x , _) (y , _) → rel→ x y)
  , (λ (x , _) (y , _) → rel← x y)
```

## Finite orders

```
_≤Fin_ : {n : ℕ} → Fin n → Fin n → 𝓤₀  ̇
_≤Fin_ {succ n} 𝟎 y = 𝟙
_≤Fin_ {succ n} (suc x) 𝟎 = 𝟘
_≤Fin_ {succ n} (suc x) (suc y) = x ≤Fin y

≤Fin-is-preorder : {n : ℕ} → is-preorder (_≤Fin_ {n})
≤Fin-is-preorder {n} = r , t , p
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

≤Fin-is-partial-order : {n : ℕ} → is-partial-order (_≤Fin_ {n})
≤Fin-is-partial-order {n}
 = ≤Fin-is-preorder , a'
 where
  a' : {n : ℕ} → antisymmetric (_≤Fin_ {n})
  a' {succ n} 𝟎 𝟎 x≤y y≤x = refl
  a' {succ n} (suc x) (suc y) x≤y y≤x = ap suc (a' x y x≤y y≤x)

≤Fin-is-linear-preorder
 : {n : ℕ} → is-linear-preorder (_≤Fin_ {n})
≤Fin-is-linear-preorder {n} = ≤Fin-is-preorder , l
 where
  l : {n : ℕ} → linear (_≤Fin_ {n})
  l {succ n} 𝟎 y = inl ⋆
  l {succ n} (suc x) 𝟎 = inr ⋆
  l {succ n} (suc x) (suc y) = l x y

≤Fin-is-linear-order
 : {n : ℕ} → is-linear-order (_≤Fin_ {n})
≤Fin-is-linear-order {n}
 = ≤Fin-is-partial-order
 , pr₂ ≤Fin-is-linear-preorder

finite-order : {F : 𝓤 ̇ } → finite-linear-order F → F → F → 𝓤₀  ̇
finite-order (n , (g , _)) = inclusion-order g _≤Fin_ 

finite-order-is-partial-order
 : {F : 𝓤 ̇ }
 → (f : finite-linear-order F)
 → is-partial-order (finite-order f)
finite-order-is-partial-order (n , (g , i))
 = embedding-order-is-partial-order
     g (equivs-are-embeddings g i)
     _≤Fin_ ≤Fin-is-partial-order

finite-order-is-linear-preorder
 : {F : 𝓤 ̇ }
 → (f : finite-linear-order F)
 → is-linear-preorder (finite-order f)
finite-order-is-linear-preorder (n , (g , _))
 = inclusion-order-is-linear-preorder g _≤Fin_ ≤Fin-is-linear-preorder

finite-order-is-linear-order
 : {F : 𝓤 ̇ }
 → (f : finite-linear-order F)
 → is-linear-order (finite-order f)
finite-order-is-linear-order (n , (g , i))
 = embedding-order-is-linear-order
     g (equivs-are-embeddings g i)
     _≤Fin_ ≤Fin-is-linear-order
```

## Discrete-sequence orders

```
discrete-lexicorder : {D : 𝓤 ̇ }
                    → is-discrete D
                    → (_≤_ : D → D → 𝓥 ̇ )
                    → (α β : ℕ → D)
                    → 𝓤 ⊔ 𝓥  ̇ 
discrete-lexicorder f _≤_ α β
 = (n : ℕ) → (α ∼ⁿ β) n → α n ≤ β n

discrete-lexicorder-is-preorder
 : {D : 𝓤 ̇ } (d : is-discrete D)
 → (_≤_ : D → D → 𝓥 ̇ )
 → is-partial-order _≤_
 → is-preorder (discrete-lexicorder d _≤_)
discrete-lexicorder-is-preorder d _≤_ ((r' , t' , p') , a') = r , t , p
 where
 r : reflexive (discrete-lexicorder d _≤_)
 r x n _ = r' (x n) 
 t : transitive (discrete-lexicorder d _≤_)
 t x y z x≤y y≤z 0 x∼ⁿz
  = t' (x 0) (y 0) (z 0) (x≤y 0 (λ _ ())) (y≤z 0 (λ _ ()))
 t x y z x≤y y≤z (succ n) x∼ⁿz
  = t (tail x) (tail y) (tail z) γ₁ γ₂ n (x∼ⁿz ∘ succ)
    where
     e : x 0 ＝ y 0
     e = a' (x 0) (y 0) (x≤y 0 (λ _ ()))
          (transport (y 0 ≤_) (x∼ⁿz 0 ⋆ ⁻¹) (y≤z 0 (λ _ ())))
     γ₁ : discrete-lexicorder d _≤_ (tail x) (tail y)
     γ₁ i tx∼ⁿty = x≤y (succ i) ζ
      where
       ζ : (x ∼ⁿ y) (succ i)
       ζ 0 j<si = e
       ζ (succ j) j<si = tx∼ⁿty j j<si
     γ₂ : (i : ℕ) → (tail y ∼ⁿ tail z) i → y (succ i) ≤ z (succ i)
     γ₂ i ty∼ⁿtz = y≤z (succ i) ζ
      where
       ζ : (y ∼ⁿ z) (succ i)
       ζ 0 j<si = e ⁻¹ ∙ x∼ⁿz 0 ⋆
       ζ (succ j) j<si = ty∼ⁿtz j j<si
 p : is-prop-valued (discrete-lexicorder d _≤_)
 p x y = Π-is-prop (fe _ _) (λ _ → Π-is-prop (fe _ _) (λ _ → p' _ _))

finite-lexicorder
 : {F : 𝓤 ̇ } (f : finite-linear-order F) (d : is-discrete F)
 → (_<_ : F → F → 𝓦 ̇ )
 → (ℕ → F) → (ℕ → F) → 𝓤 ⊔ 𝓦  ̇
finite-lexicorder f d _<_ = discrete-lexicorder d _<_

linear-finite-lexicorder-implies-linear-ℕ∞-order
 : {F : 𝓤 ̇ } (f@(n , _) : finite-linear-order F)
 → n > 1
 → linear
    (discrete-lexicorder (finite-is-discrete f) (finite-order f))
 → linear _≼ℕ∞_
linear-finite-lexicorder-implies-linear-ℕ∞-order
 {𝓤} {F} f@(succ (succ n) , (g , (h , η) , _)) _ l u v
 = Cases (l (ρ ∘ pr₁ u) (ρ ∘ pr₁ v)) (inl ∘ γ u v) (inr ∘ γ v u)
 where
  _≤Fᴺ_ = discrete-lexicorder (finite-is-discrete f) (finite-order f)
  d₀ d₁ : F
  d₀ = h 𝟎
  d₁ = h 𝟏
  ρ : 𝟚 → F
  ρ ₀ = d₀
  ρ ₁ = d₁
  γ : (u v : ℕ∞) → (ρ ∘ pr₁ u) ≤Fᴺ (ρ ∘ pr₁ v) → u ≼ v
  γ u v u≤v n uₙ=1
   = ₁-gρ-maximal
       (pr₁ v n)
       (transport (λ - → g (ρ -) ≤Fin g (ρ (pr₁ v n)))
         uₙ=1 (u≤v n (λ i i<n → ap ρ (u∼ⁿv n uₙ=1 i i<n))))
   where
    ₁-gρ-maximal : (y : 𝟚) → g (ρ ₁) ≤Fin g (ρ y) → y ＝ ₁
    ₁-gρ-maximal ₀ gh1≤gh0
     = 𝟘-elim (transport (λ - → ¬ (- ≤Fin g (h 𝟎))) (η 𝟏 ⁻¹)
                (transport (λ - → ¬ (𝟏 ≤Fin -)) (η 𝟎 ⁻¹) id) gh1≤gh0)
    ₁-gρ-maximal ₁ _ = refl
    u∼ⁿv : (n : ℕ) → pr₁ u n ＝ ₁ → (pr₁ u ∼ⁿ pr₁ v) n
    u∼ⁿv (succ n) uₙ=₁ i i<sn
     = ⊏-trans' i (succ n) u i<sn uₙ=₁
     ∙ ⊏-trans'' v n i i<sn (γ u v u≤v n (⊏-back u n uₙ=₁)) ⁻¹
     
linear-finite-lexicorder-implies-WLPO
 : {F : 𝓤 ̇ } (f@(n , _) : finite-linear-order F)
 → n > 1
 → linear
    (discrete-lexicorder (finite-is-discrete f) (finite-order f))
 → WLPO
linear-finite-lexicorder-implies-WLPO f n>1
 = ℕ∞-linearity-taboo (fe 𝓤₀ 𝓤₀)
 ∘ linear-finite-lexicorder-implies-linear-ℕ∞-order f n>1

discrete-approx-lexicorder : {D : 𝓤 ̇ }
                           → is-discrete D
                           → (_≤_ : D → D → 𝓥 ̇ )
                           → (α β : ℕ → D)
                           → ℕ
                           → 𝓤 ⊔ 𝓥  ̇
discrete-approx-lexicorder d _≤_ α β n
 = (i : ℕ) → i < n → (α ∼ⁿ β) i → α i ≤ β i

discrete-approx-lexicorder-reduce
 : {D : 𝓤 ̇ } (ds : is-discrete D)
 → (_≤_ : D → D → 𝓥 ̇ )
 → (x y : ℕ → D) (ϵ : ℕ)
 → discrete-approx-lexicorder ds _≤_ x y (succ ϵ)
 → discrete-approx-lexicorder ds _≤_ x y ϵ
discrete-approx-lexicorder-reduce ds _≤_ x y ϵ x≤y i i<ϵ
 = x≤y i (<-trans i ϵ (succ ϵ) i<ϵ (<-succ ϵ))

discrete-approx-lexicorder-is-approx-order
 : {D : 𝓤 ̇ } (ds : is-discrete D)
 → (_≤_ : D → D → 𝓥 ̇ ) (s : is-linear-order _≤_)
 → is-approx-order
     (ℕ→D-ClosenessSpace ds)
     (discrete-approx-lexicorder ds _≤_)
discrete-approx-lexicorder-is-approx-order
 {𝓤} {𝓥} {D} ds _≤_ (((r' , t' , p') , a') , l')
 = (λ ϵ → (r ϵ , t ϵ , p ϵ) , l ϵ) , d , c
 where
  r : (n : ℕ)
    → reflexive (λ x y → discrete-approx-lexicorder ds _≤_ x y n)
  r n x i i<n _ = r' (x i)
  t : (n : ℕ)
    → transitive (λ x y → discrete-approx-lexicorder ds _≤_ x y n)
  t n x y z x≤y y≤z 0 i<n x∼ⁱz
   = t' (x 0) (y 0) (z 0) (x≤y 0 i<n (λ _ ())) (y≤z 0 i<n (λ _ ()))
  t (succ n) x y z x≤y y≤z (succ i) i<n x∼ⁱz
   = t n (tail x) (tail y) (tail z) γ₁ γ₂ i i<n (x∼ⁱz ∘ succ)
   where
    e : x 0 ＝ y 0
    e = a' (x 0) (y 0)
           (x≤y 0 ⋆ (λ _ ()))
           (transport (y 0 ≤_) (x∼ⁱz 0 ⋆ ⁻¹) (y≤z 0 ⋆ (λ _ ())))
    γ₁ : (j : ℕ)
       → j < n
       → (tail x ∼ⁿ tail y) j
       → x (succ j) ≤ y (succ j)
    γ₁ j j<n tx∼ʲty = x≤y (succ j) j<n ζ
     where
      ζ : (x ∼ⁿ y) (succ j) 
      ζ 0 k<sj = e
      ζ (succ k) k<sj = tx∼ʲty k k<sj
    γ₂ : (j : ℕ) → j < n → (tail y ∼ⁿ tail z) j → y (succ j) ≤ z (succ j)
    γ₂ j j<n ty∼ʲtz = y≤z (succ j) j<n ζ
     where
      ζ : (y ∼ⁿ z) (succ j)
      ζ 0 k<sj = e ⁻¹ ∙ x∼ⁱz 0 ⋆
      ζ (succ k) k<sj = ty∼ʲtz k k<sj
  p : (n : ℕ)
    → is-prop-valued (λ x y → discrete-approx-lexicorder ds _≤_ x y n)
  p n x y
   = Π-is-prop (fe _ _)
       (λ _ → Π-is-prop (fe _ _)
       (λ _ → Π-is-prop (fe _ _) (λ _ → p' _ _)))
  l : (ϵ : ℕ) → (x y : ℕ → D)
    → discrete-approx-lexicorder ds _≤_ x y ϵ
    + discrete-approx-lexicorder ds _≤_ y x ϵ
  l 0 x y = inl (λ _ ())
  l (succ ϵ) x y
   = γ (l ϵ (tail x) (tail y))
       (l' (head x) (head y)) (ds (head x) (head y))
   where
    γ : discrete-approx-lexicorder ds _≤_ (tail x) (tail y) ϵ
      + discrete-approx-lexicorder ds _≤_ (tail y) (tail x) ϵ
      → (head x ≤ head y) + (head y ≤ head x)
      → (head x ＝ head y) + (head x ≠ head y)
      → discrete-approx-lexicorder ds _≤_ x y (succ ϵ)
      + discrete-approx-lexicorder ds _≤_ y x (succ ϵ)
    γ (inl tx≤ᵉty) (inl hx≤hy) _ = inl ζ
     where
      ζ : discrete-approx-lexicorder ds _≤_ x y (succ ϵ)
      ζ 0 i<sϵ x∼ⁱy = hx≤hy
      ζ (succ i) i<sϵ x∼ⁱy = tx≤ᵉty i i<sϵ (x∼ⁱy ∘ succ)
    γ (inl tx≤ᵉty) (inr hy≤hx) (inl hx＝hy) = inl ζ
     where
      ζ : discrete-approx-lexicorder ds _≤_ x y (succ ϵ)
      ζ 0 i<sϵ y∼ⁱx = transport (head x ≤_) hx＝hy (r' (head x))
      ζ (succ i) i<sϵ x∼ⁱy = tx≤ᵉty i i<sϵ (x∼ⁱy ∘ succ)
    γ (inl tx≤ᵉty) (inr hy≤hx) (inr hx≠hy) = inr ζ
     where
      ζ : discrete-approx-lexicorder ds _≤_ y x (succ ϵ)
      ζ 0 i<sϵ y∼ⁱx = hy≤hx
      ζ (succ i) i<sϵ y∼ⁱx = 𝟘-elim (hx≠hy (y∼ⁱx 0 ⋆ ⁻¹))
    γ (inr ty≤ᵉtx) (inr hy≤hx) _ = inr ζ
     where
      ζ : discrete-approx-lexicorder ds _≤_ y x (succ ϵ)
      ζ 0 i<sϵ y∼ⁱx = hy≤hx
      ζ (succ i) i<sϵ y∼ⁱx = ty≤ᵉtx i i<sϵ (y∼ⁱx ∘ succ)
    γ (inr ty≤ᵉtx) (inl hx≤hy) (inl hx＝hy) = inr ζ
     where
      ζ : discrete-approx-lexicorder ds _≤_ y x (succ ϵ)
      ζ 0 i<sϵ x∼ⁱy = transport (_≤ head x) hx＝hy (r' (head x))
      ζ (succ i) i<sϵ y∼ⁱx = ty≤ᵉtx i i<sϵ (y∼ⁱx ∘ succ)
    γ (inr ty≤ᵉtx) (inl hx≤hy) (inr hx≠hy) = inl ζ
     where
      ζ : discrete-approx-lexicorder ds _≤_ x y (succ ϵ)
      ζ 0 i<sϵ x∼ⁱy = hx≤hy
      ζ (succ i) i<sϵ x∼ⁱy = 𝟘-elim (hx≠hy (x∼ⁱy 0 ⋆))
  d : (ϵ : ℕ) (x y : ℕ → D)
    → is-decidable (discrete-approx-lexicorder ds _≤_ x y ϵ)
  d 0 x y = inl (λ _ ())
  d (succ ϵ) x y
   = Cases (d ϵ x y)
       (λ x≤ᵉy → γ₁ x≤ᵉy
         (∼ⁿ-decidable (λ _ → ds) x y ϵ)
         (discrete-reflexive-antisym-linear-order-is-decidable
           ds _≤_ r' a' l' (x ϵ) (y ϵ)))
       γ₂
   where
    γ₁ : discrete-approx-lexicorder ds _≤_ x y ϵ
       → is-decidable ((x ∼ⁿ y) ϵ)
       → is-decidable (x ϵ ≤ y ϵ)
       → is-decidable (discrete-approx-lexicorder ds _≤_ x y (succ ϵ))
    γ₁ x≤ᵉy (inl  x∼ᵉy) (inl  xϵ≤yϵ) = inl ζ
     where
      ζ : discrete-approx-lexicorder ds _≤_ x y (succ ϵ)
      ζ i i<sϵ x∼ⁱy
       = Cases (<-split i ϵ i<sϵ)
           (λ i<ϵ → x≤ᵉy i i<ϵ x∼ⁱy)
           (λ i＝ϵ → transport (λ - → x - ≤ y -) (i＝ϵ ⁻¹) xϵ≤yϵ)
    γ₁ x≤ᵉy (inl  x∼ᵉy) (inr ¬xϵ≤yϵ)
     = inr (λ x≤ˢᵉy → ¬xϵ≤yϵ (x≤ˢᵉy ϵ (<-succ ϵ) x∼ᵉy))
    γ₁ x≤ᵉy (inr ¬x∼ᵉy) _
     = inl ζ
     where
      ζ : discrete-approx-lexicorder ds _≤_ x y (succ ϵ)
      ζ i i<sϵ x∼ⁱy
       = Cases (<-split i ϵ i<sϵ)
           (λ i<ϵ → x≤ᵉy i i<ϵ x∼ⁱy)
           (λ i＝ϵ → 𝟘-elim (¬x∼ᵉy (transport (x ∼ⁿ y) i＝ϵ x∼ⁱy)))
    γ₂ : ¬ discrete-approx-lexicorder ds _≤_ x y ϵ
       → is-decidable (discrete-approx-lexicorder ds _≤_ x y (succ ϵ))
    γ₂ ¬x≤ᵉy
     = inr (λ x≤ˢᵉy → ¬x≤ᵉy
             (discrete-approx-lexicorder-reduce ds _≤_ x y ϵ x≤ˢᵉy))
  c : (ϵ : ℕ) → (x y : ℕ → D)
    → C (ℕ→D-ClosenessSpace ds) ϵ x y
    → discrete-approx-lexicorder ds _≤_ x y ϵ
  c ϵ x y Cϵxy i i<ϵ x∼ⁱy
   = transport (x i ≤_) (C-to-∼ⁿ ds x y ϵ Cϵxy i i<ϵ) (r' (x i))
  
module LexicographicOrder-Relates
 (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt
 open ApproxOrder-Relates pt

 discrete-approx-lexicorder-relates→
  : {D : 𝓤 ̇ } (ds : is-discrete D) (i : is-set D)
  → (_≤_ : D → D → 𝓥 ̇ )
  → (discrete-approx-lexicorder ds _≤_)
    relates-to→
    (discrete-lexicorder ds _≤_)
 discrete-approx-lexicorder-relates→ 
  ds i _≤_ x y Πx≤ⁿy n = Πx≤ⁿy (succ n) n (<-succ n)

 discrete-approx-lexicorder-relates←
  : {D : 𝓤 ̇ } (ds : is-discrete D) (i : is-set D)
  → (_≤_ : D → D → 𝓥 ̇ )
  → discrete-approx-lexicorder ds _≤_
    relates-to←
    discrete-lexicorder ds _≤_
 discrete-approx-lexicorder-relates← ds i _≤_ α β α≤β
  = ∣ 0 , (λ _ _ i _ → α≤β i) ∣

 discrete-approx-lexicorder-relates
  : {D : 𝓤 ̇ } (ds : is-discrete D) (i : is-set D)
  → (_≤_ : D → D → 𝓥 ̇ ) (s : is-linear-order _≤_)
  → approx-order-relates
      (ℕ→D-ClosenessSpace ds)
      (discrete-approx-lexicorder ds _≤_)
      (discrete-approx-lexicorder-is-approx-order ds _≤_ s)
      (discrete-lexicorder ds _≤_)
      (discrete-lexicorder-is-preorder ds _≤_ (pr₁ s))
 discrete-approx-lexicorder-relates ds i _≤_ _
  = discrete-approx-lexicorder-relates→ ds i _≤_
  , discrete-approx-lexicorder-relates← ds i _≤_
```

## Specific example orders

```
ℕ→𝟚-lexicorder : (ℕ → 𝟚) → (ℕ → 𝟚) → 𝓤₀ ̇
ℕ→𝟚-lexicorder
 = discrete-lexicorder 𝟚-is-discrete (finite-order 𝟚-is-finite)

ℕ∞-lexicorder : ℕ∞ → ℕ∞ → 𝓤₀ ̇
ℕ∞-lexicorder = Σ-order is-decreasing ℕ→𝟚-lexicorder

ℕ→𝟚-lexicorder-is-preorder : is-preorder ℕ→𝟚-lexicorder
ℕ→𝟚-lexicorder-is-preorder
 = discrete-lexicorder-is-preorder
     𝟚-is-discrete (finite-order 𝟚-is-finite)
     (finite-order-is-partial-order 𝟚-is-finite)
     
ℕ∞-lexicorder-is-preorder : is-preorder ℕ∞-lexicorder
ℕ∞-lexicorder-is-preorder
 = Σ-order-is-preorder is-decreasing
     ℕ→𝟚-lexicorder ℕ→𝟚-lexicorder-is-preorder

ℕ→𝟚-approx-lexicorder : (ℕ → 𝟚) → (ℕ → 𝟚) → ℕ → 𝓤₀ ̇ 
ℕ→𝟚-approx-lexicorder
 = discrete-approx-lexicorder
     𝟚-is-discrete (finite-order 𝟚-is-finite)

ℕ→𝟚-approx-lexicorder-is-approx-order
 : is-approx-order 𝟚ᴺ-ClosenessSpace ℕ→𝟚-approx-lexicorder
ℕ→𝟚-approx-lexicorder-is-approx-order
 = discrete-approx-lexicorder-is-approx-order
     𝟚-is-discrete (finite-order 𝟚-is-finite)
     (finite-order-is-linear-order 𝟚-is-finite)

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

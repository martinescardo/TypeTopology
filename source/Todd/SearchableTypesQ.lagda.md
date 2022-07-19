```agda
{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}


open import SpartanMLTT
open import UF-FunExt
open import UF-Subsingletons
open import UF-PropTrunc
open import UF-Quotient

module SearchableTypesQ
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
 where

open import Two-Properties hiding (zero-is-not-one)
open import NaturalsOrder
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import IntegersB
open import IntegersOrder
open import IntegersAddition renaming (_+_ to _+ℤ_)
open import IntegersNegation renaming (-_  to  −ℤ_)
open import UF-Subsingletons
open import NaturalsOrder
open import DecidableAndDetachable
open import UF-Equiv
open import UF-Subsingletons-FunExt
open import TernaryBoehmRealsPrelude fe
open import InfiniteSearch1 (dfunext (fe _ _))
  hiding (predicate;everywhere-decidable;decidable;trivial-predicate
         ;is-set)
open import UF-ImageAndSurjection
open import UF-Embeddings
open ImageAndSurjection pt
open propositional-truncations-exist pt

```

Decidable predicates

```agda
open set-quotients-exist sq
 
decidable-predicate : {𝓤 𝓦 : Universe} → 𝓤 ̇ → 𝓤 ⊔ 𝓦 ⁺ ̇
decidable-predicate {𝓤} {𝓦} X
 = Σ p ꞉ (X → Ω 𝓦) , ((x : X) → decidable (pr₁ (p x)))

decidable-predicate-on : {𝓤 𝓥 𝓦 : Universe}
                       → (X : 𝓤 ̇ ) → EqRel {𝓤} {𝓥} X
                       → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
decidable-predicate-on {𝓤} {𝓥} {𝓦}  X   e
 = decidable-predicate {𝓤 ⊔ 𝓥} {𝓦} (X / e)

decidable-predicate⌜_,_⌝ : {X Y : 𝓤 ̇ } → X ≃ Y
                         → decidable-predicate {𝓤} {𝓥} X
                         → decidable-predicate {𝓤} {𝓥} Y
decidable-predicate⌜ e , (p , d) ⌝ = (p ∘ ⌜ e ⌝⁻¹) , (d ∘ ⌜ e ⌝⁻¹)

decidable-predicate⌜_,_⌝⁻¹ : {X Y : 𝓤 ̇ } → X ≃ Y
                           → decidable-predicate {𝓤} {𝓥} Y
                           → decidable-predicate {𝓤} {𝓥} X
decidable-predicate⌜ e , (p , d) ⌝⁻¹ = (p ∘ ⌜ e ⌝) , (d ∘ ⌜ e ⌝)

Trivial : {X : 𝓤 ̇ } → EqRel {𝓤} {𝓥} X
Trivial = (λ x y → 𝟙)
        , (λ _ _ → 𝟙-is-prop)
        , (λ _         → ⋆)
        , (λ _ _ _     → ⋆)
        , (λ _ _ _ _ _ → ⋆)

_/𝟙 : {𝓤 : Universe} → 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ̇ 
_/𝟙 {𝓤} X 𝓥 = X / Trivial {𝓤} {𝓥}

_/𝟙-is-set : {𝓤 𝓥 : Universe} → (X : 𝓤 ̇ ) → is-set ((X /𝟙) 𝓥) 
(X /𝟙-is-set) = /-is-set Trivial

_/𝟙-is-prop : {𝓤 𝓥 : Universe} → (X : 𝓤 ̇ ) → is-prop ((X /𝟙) 𝓥) 
_/𝟙-is-prop {𝓤} {𝓥} X x
 = /-induction Trivial (λ _ → X /𝟙-is-set)
   (λ x₂ → /-induction Trivial (λ _ → X /𝟙-is-set)
   (λ x₁ → η/-identifies-related-points {𝓤} {𝓥} {X} Trivial {x₁} {x₂} ⋆) x)

_/𝟙-pointed-is-singleton : {𝓤 𝓥 : Universe} → (X : 𝓤 ̇ ) → (x : X)
                         → is-singleton ((X /𝟙) 𝓥) 
(X /𝟙-pointed-is-singleton) x
 = pointed-props-are-singletons (η/ Trivial x) (X /𝟙-is-prop)

singletons-equiv-to-𝟙 : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ } → is-singleton X → 𝟙 {𝓥} ≃ X
singletons-equiv-to-𝟙 {𝓤} {𝓥} {X} (x , h) = f , (g , h) , (g , h⁻¹)
 where
   f : 𝟙 → X
   f ⋆ = x
   g : X → 𝟙
   g _ = ⋆
   h⁻¹ : g ∘ f ∼ id
   h⁻¹ ⋆ = refl

quotient-by-𝟙-equiv : {X : 𝓤 ̇ } → X → 𝟙 {𝓥} ≃ (X /𝟙) 𝓥
quotient-by-𝟙-equiv = singletons-equiv-to-𝟙 ∘ (_ /𝟙-pointed-is-singleton)

Identity : {X : 𝓤 ̇ } → is-set X → EqRel {𝓤} {𝓤} X
Identity s = _≡_
           , (λ _ _ → s)
           , (λ _     → refl)
           , (λ _ _   → _⁻¹)
           , (λ _ _ _ → _∙_)

_/≡ : {𝓤 : Universe} → (X : 𝓤 ̇ ) → is-set X → 𝓤 ̇
(X /≡) s = X / (Identity s)

ispropfiber : {X : 𝓤 ̇ } → (s : is-set X) → (x : X)
            → is-prop (fiber (η/ (Identity s)) (η/ (Identity s) x))
ispropfiber s x (_ , a) (_ , b)
 = {!!} {- to-subtype-≡ (λ _ → quotient-is-set (Identity s))
     (η/-relates-identified-points (Identity s) (a ∙ b ⁻¹)) 0 -}

embedη/ : {X : 𝓤 ̇ } → (s : is-set X) → is-embedding (η/ (Identity s))
embedη/ s = embedding-criterion (η/ (Identity s)) (ispropfiber s)

equivη/ : {X : 𝓤 ̇ } → (s : is-set X) → is-equiv (η/ (Identity s))
equivη/ s = surjective-embeddings-are-equivs (η/ (Identity s))
              (embedη/ s) {!!} -- (η/-is-surjection (Identity s))

quotient-by-≡-equiv : {X : 𝓤 ̇ } → (s : is-set X) → X ≃ (X /≡) s
quotient-by-≡-equiv {𝓤} {X} s = η/ (Identity s) , equivη/ s

Product : {X : 𝓤 ̇ } {Y : 𝓤' ̇ } → is-set X → is-set Y
        → EqRel {𝓤}  {𝓥}  X
        → EqRel {𝓤'} {𝓥'} Y
        → EqRel {𝓤 ⊔ 𝓤'} {𝓥 ⊔ 𝓥'} (X × Y)
Product s t (_≈x_ , ≈ix , ≈rx , ≈sx , ≈tx)
            (_≈y_ , ≈iy , ≈ry , ≈sy , ≈ty)
 = (λ (x₁ , y₁) (x₂ , y₂) → (x₁ ≈x x₂) × (y₁ ≈y y₂))
 , (λ (x₁ , y₁) (x₂ , y₂) → ×-is-prop (≈ix x₁ x₂) (≈iy y₁ y₂))
 , (λ (x₁ , y₁) → (≈rx x₁) , (≈ry y₁))
 , (λ (x₁ , y₁) (x₂ , y₂) (x≈ , y≈)
    → ≈sx x₁ x₂ x≈ , ≈sy y₁ y₂ y≈)
 , λ (x₁ , y₁) (x₂ , y₂) (x₃ , y₃) (x≈ , y≈) (x'≈ , y'≈)
    → ≈tx x₁ x₂ x₃ x≈ x'≈ , ≈ty y₁ y₂ y₃ y≈ y'≈

_≈_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇
(α ≈ β) n = (i : ℕ) → i <ℕ n → α i ≡ β i

Prefix : {X : 𝓤 ̇ } → is-set X → ℕ → EqRel {𝓤} {𝓤} (ℕ → X)
Prefix s n = (λ α β → (α ≈ β) n)
           , (λ _ _ → Π-is-prop (fe _ _) (λ _ → Π-is-prop (fe _ _) (λ _ → s)))
           , (λ _ _ _ → refl)
           , (λ _ _   f   i i<n → f i i<n ⁻¹)
           , (λ _ _ _ f g i i<n → f i i<n ∙ g i i<n)

ℕ→_/≈_ : (X : 𝓤 ̇ ) → ℕ → is-set X → 𝓤 ̇
(ℕ→ X /≈ n) s = (ℕ → X) / Prefix s n

≈-0-is-singleton : {X : 𝓤 ̇ } → X → (s : is-set X)
                 → is-singleton ((ℕ→ X /≈ 0) s)
≈-0-is-singleton x s
 = {!!} {- ((λ _ → ⊤Ω) , ∣ {!!} ∣)
 , (λ (h , i) → to-subtype-≡ {!!} {!!}) -}
```
quotient-by-≈-equiv : {X : 𝓤 ̇ } → X → (s : is-set X)
                    → 𝟙 {𝓤 ⁺} ≃ (ℕ→ X /≈ 0) s
quotient-by-≈-equiv {𝓤} {X} x s = f , (g , fg) , (g , gf)
 where
   f : 𝟙 → (ℕ→ X /≈ 0) s
   f ⋆ = (λ _ → ⊤Ω) , ∣ (λ _ → x) , dfunext (fe _ _) (λ _ → to-subtype-≡ {!!} {!!}) ∣
   g : (ℕ→ X /≈ 0) s → 𝟙
   g _ = ⋆
   fg : f ∘ g ∼ id
   fg = {!!}
   gf : g ∘ f ∼ id
   gf = {!!}

Head : {X : 𝓤 ̇ } → (s : is-set X) (n : ℕ)
     → (ℕ→ X /≈ succ n) s → X
Head {𝓤} {X} s n
 = mediating-map/ (Prefix s (succ n)) s head (λ f → f 0 ⋆)

Tail : {X : 𝓤 ̇ } → (s : is-set X) (n : ℕ)
     → (ℕ→ X /≈ succ n) s → (ℕ→ X /≈ n) s
Tail s n
 = mediating-map/ (Prefix s (succ n)) ? -- (quotient-is-set (Prefix s n))
     (η/ (Prefix s n))
     (λ f → η/-identifies-related-points (Prefix s n)
       (λ i i<n → f i (<-trans i n (succ n) i<n (<-succ n))))

Cons : {X : 𝓤 ̇ } → (s : is-set X) (n : ℕ)
     → (X × (ℕ → X)) / (Product s (Π-is-set (fe _ _) (λ _ → s))
                         (Identity s) (Prefix s n))
     → (ℕ→ X /≈ succ n) s
Cons {𝓤} {X} s n
 = mediating-map/
     (Product s (Π-is-set (fe _ _) (λ _ → s)) (Identity s) (Prefix s n))
     ? -- (quotient-is-set (Prefix s (succ n)))
     (λ (x , xs) → η/ (Prefix s (succ n)) (x :: xs))
     (λ f → η/-identifies-related-points (Prefix s (succ n))
       (γ f))
 where
   γ : {(x , xs) (x' , xs') : X × (ℕ → X)}
     → ((x ≡ x') × ((i : ℕ) → i <ℕ n → xs i ≡ xs' i))
     → (i : ℕ) → i <ℕ succ n
     → (x :: xs) i ≡ (x' :: xs') i
   γ (x≡ , xs≈) zero i<sn = x≡
   γ (x≡ , xs≈) (succ i) i<sn = xs≈ i i<sn

quotient-by-≈-s-equiv : {X : 𝓤 ̇ } → X → (s : is-set X) (n : ℕ)
                      → X × ((ℕ→ X /≈ n) s) ≃ (ℕ→ X /≈ succ n) s
quotient-by-≈-s-equiv {𝓤} {X} x s n = f , (g , fg) , (g , gf)
 where
   f : X × (ℕ→ X /≈ n) s → (ℕ→ X /≈ succ n) s
   f (x , xs) = {!!}
   g : (ℕ→ X /≈ succ n) s → X × ((ℕ→ X /≈ n) s)
   g xs = {!!} , {!!}
   fg : f ∘ g ∼ id
   fg = {!!}
   gf : g ∘ f ∼ id
   gf = {!!}

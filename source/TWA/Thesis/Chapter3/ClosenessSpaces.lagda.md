[⇐ Index](../html/TWA.Thesis.index.html)

# Closeness spaces

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import Notation.Order
open import Naturals.Order
open import UF.DiscreteAndSeparated
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import Quotient.Type
  using (is-prop-valued;is-equiv-relation;EqRel)
open import MLTT.Two-Properties
open import Fin.Bishop
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to _↑
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)
open import NotionsOfDecidability.Complemented

open import TWA.Thesis.Chapter2.Finite

module TWA.Thesis.Chapter3.ClosenessSpaces (fe : FunExt) where

open import TWA.Closeness fe hiding (is-ultra; is-closeness)

is-decreasing'
 : (v : ℕ∞) (n : ℕ) → (i : ℕ) → i ≤ n → pr₁ v n ＝ ₁ → pr₁ v i ＝ ₁
is-decreasing' v
 = regress (λ z → pr₁ v z ＝ ₁) (λ n → ≤₂-criterion-converse (pr₂ v n))

positive-below-n : (i n : ℕ) → pr₁ (Succ (n ↑)) i ＝ ₁ → i ≤ n 
positive-below-n zero n snᵢ=1 = ⋆
positive-below-n (succ i) (succ n) snᵢ=1 = positive-below-n i n snᵢ=1

≼-left-decidable : (n : ℕ) (v : ℕ∞) → is-decidable ((n ↑) ≼ v)
≼-left-decidable zero v = inl (zero-minimal v)
≼-left-decidable (succ n) v
 = Cases (𝟚-is-discrete (pr₁ v n) ₁)
     (λ  vₙ=1 → inl (λ i snᵢ=1 → is-decreasing' v n i
                                   (positive-below-n i n snᵢ=1) vₙ=1))
     (λ ¬vₙ=1 → inr (λ sn≼v → ¬vₙ=1 (sn≼v n (ℕ-to-ℕ∞-diagonal₁ n))))
```

## (Pseudo)closeness spaces

```
is-ultra is-closeness : {X : 𝓤 ̇ } → (X → X → ℕ∞) → 𝓤 ̇
is-ultra {𝓤} {X} c = (x y z : X) → min (c x y) (c y z) ≼ c x z
is-closeness c
 = indistinguishable-are-equal c
 × self-indistinguishable c
 × is-symmetric c
 × is-ultra c

is-pseudocloseness : {X : 𝓤 ̇ } → (X → X → ℕ∞) → 𝓤 ̇ 
is-pseudocloseness c
 = self-indistinguishable c
 × is-symmetric c
 × is-ultra c

is-pseudocloseness-space : (X : 𝓤 ̇ ) → 𝓤 ̇
is-pseudocloseness-space X = Σ c ꞉ (X → X → ℕ∞) , is-pseudocloseness c

PseudoClosenessSpace : (𝓤 : Universe) → 𝓤 ⁺  ̇ 
PseudoClosenessSpace 𝓤
 = Σ X ꞉ 𝓤 ̇ , is-pseudocloseness-space X

⟪_⟫ : PseudoClosenessSpace 𝓤 → 𝓤 ̇ 
⟪ X , _ ⟫ = X

is-closeness-space : (X : 𝓤 ̇ ) → 𝓤 ̇
is-closeness-space X
 = Σ c ꞉ (X → X → ℕ∞)
 , (indistinguishable-are-equal c
 × is-pseudocloseness c)

ClosenessSpace : (𝓤 : Universe) → 𝓤 ⁺  ̇ 
ClosenessSpace 𝓤
 = Σ X ꞉ 𝓤 ̇ , is-closeness-space X

ι : ClosenessSpace 𝓤 → PseudoClosenessSpace 𝓤
ι (X , c , i , p) = X , c , p

⟨_⟩ : ClosenessSpace 𝓤 → 𝓤 ̇
⟨ X , _ ⟩ = X

c⟨_⟩ : (X : ClosenessSpace 𝓤) → ⟨ X ⟩ → ⟨ X ⟩ → ℕ∞
c⟨ (X , c , e , i , s , u) ⟩ = c

e⟨_⟩ : (X : ClosenessSpace 𝓤)
     → indistinguishable-are-equal c⟨ X ⟩
e⟨ (X , c , e , i , s , u) ⟩ = e

i⟨_⟩ : (X : ClosenessSpace 𝓤)
     → self-indistinguishable c⟨ X ⟩
i⟨ (X , c , e , i , s , u) ⟩ = i

s⟨_⟩ : (X : ClosenessSpace 𝓤)
     → is-symmetric c⟨ X ⟩
s⟨ (X , c , e , i , s , u) ⟩ = s

u⟨_⟩ : (X : ClosenessSpace 𝓤)
     → is-ultra c⟨ X ⟩
u⟨ (X , c , e , i , s , u) ⟩ = u
```

## Closeness relations

```
c'⟨_⟩ : (X : PseudoClosenessSpace 𝓤) → ⟪ X ⟫ → ⟪ X ⟫ → ℕ∞
c'⟨ (X , c , _) ⟩ = c

C' : (X : PseudoClosenessSpace 𝓤) → ℕ → ⟪ X ⟫ → ⟪ X ⟫ → 𝓤₀ ̇   
C' (X , c , _) n x y = (n ↑) ≼ c x y

C'-prop
 : (X : PseudoClosenessSpace 𝓤) (n : ℕ) → is-prop-valued (C' X n)
C'-prop X n _ _
 = Π-is-prop (fe _ _) (λ _ → Π-is-prop (fe _ _) (λ _ → 𝟚-is-set))

C'-refl : (X : PseudoClosenessSpace 𝓤) (n : ℕ) → reflexive (C' X n)
C'-refl (X , c , e , s , u) n x
 = transport ((n ↑) ≼_) (e x ⁻¹) (∞-maximal (n ↑))

C'-sym : (X : PseudoClosenessSpace 𝓤) (n : ℕ) → symmetric (C' X n) 
C'-sym (X , c , e , s , u) n x y Cxy
 = transport ((n ↑) ≼_) (s x y) Cxy

C'-trans : (X : PseudoClosenessSpace 𝓤) (n : ℕ) → transitive (C' X n)
C'-trans (X , c , e , s , u) n x y z Cxy Cyz m π
 = u x y z m (Lemma[a＝₁→b＝₁→min𝟚ab＝₁] (Cxy m π) (Cyz m π))

C'-decidable : (X : PseudoClosenessSpace 𝓤) (n : ℕ)
             → (x y : ⟪ X ⟫) → is-decidable (C' X n x y)
C'-decidable (X , c , _) n x y = ≼-left-decidable n (c x y)

C : (X : ClosenessSpace 𝓤) → ℕ → ⟨ X ⟩ → ⟨ X ⟩ → 𝓤₀ ̇   
C = C' ∘ ι

C-prop : (X : ClosenessSpace 𝓤) (n : ℕ) → is-prop-valued (C X n)
C-prop = C'-prop ∘ ι

C-refl : (X : ClosenessSpace 𝓤) (n : ℕ) → reflexive (C X n)
C-refl = C'-refl ∘ ι

C-sym : (X : ClosenessSpace 𝓤) (n : ℕ) → symmetric (C X n) 
C-sym = C'-sym ∘ ι

C-trans : (X : ClosenessSpace 𝓤) (n : ℕ) → transitive (C X n)
C-trans = C'-trans ∘ ι

C-decidable : (X : ClosenessSpace 𝓤)
            → (n : ℕ)
            → (x y : ⟨ X ⟩ )
            → is-decidable (C X n x y)
C-decidable = C'-decidable ∘ ι

C-is-eq : (X : ClosenessSpace 𝓤) (n : ℕ) → is-equiv-relation (C X n)
C-is-eq X n = C-prop X n , C-refl X n , C-sym X n , C-trans X n

C'Ω : (X : PseudoClosenessSpace 𝓤) → ℕ → ⟪ X ⟫ → ⟪ X ⟫ → Ω 𝓤₀   
C'Ω X n x y = C' X n x y , C'-prop X n x y

CΩ : (X : ClosenessSpace 𝓤) → ℕ → ⟨ X ⟩ → ⟨ X ⟩ → Ω 𝓤₀   
CΩ X n x y = C X n x y , C-prop X n x y

C⁼ : (X : ClosenessSpace 𝓤) (n : ℕ) → EqRel ⟨ X ⟩
C⁼ X n = C X n , C-is-eq X n

C'-pred : (X : PseudoClosenessSpace 𝓤)
        → (ϵ : ℕ)
        → (x y : ⟪ X ⟫)
        → C' X (succ ϵ) x y
        → C' X ϵ x y
C'-pred X ϵ x y Csϵxy n n⊏ϵ
 = Csϵxy n (⊏-trans n ϵ (Succ (ϵ ↑)) n⊏ϵ (ℕ-to-ℕ∞-diagonal₁ ϵ))

C-pred : (X : ClosenessSpace 𝓤)
       → (ϵ : ℕ)
       → (x y : ⟨ X ⟩)
       → C X (succ ϵ) x y
       → C X ϵ x y
C-pred X = C'-pred (ι X)

C-mono : (X : ClosenessSpace 𝓤)
       → (n i : ℕ)
       → i ≤ n
       → (x y : ⟨ X ⟩)
       → C X n x y
       → C X i x y
C-mono X n i i≤n x y Cnxy k k⊏i
 = Cnxy k (<-gives-⊏ k n (<-≤-trans k i n (⊏-gives-< k i k⊏i) i≤n))

identical-implies-closeness-∞ : (X : ClosenessSpace 𝓤)
                              → (x y : ⟨ X ⟩)
                              → x ＝ y
                              → c⟨ X ⟩ x y ＝ ∞
identical-implies-closeness-∞ X x x refl = i⟨ X ⟩ x

closeness-∞-implies-ϵ-close : (X : ClosenessSpace 𝓤)
                            → (x y : ⟨ X ⟩)
                            → c⟨ X ⟩ x y ＝ ∞
                            → (ϵ : ℕ) → C X ϵ x y
closeness-∞-implies-ϵ-close X x y cxy＝∞ ϵ n _
 = ap (λ - → pr₁ - n) cxy＝∞

C-id : (X : ClosenessSpace 𝓤)
     → (n : ℕ)
     → (x y : ⟨ X ⟩)
     → x ＝ y
     → C X n x y
C-id X n x x refl = C-refl X n x
```

## Continuity definitions

```
f-continuous'
 : (X : PseudoClosenessSpace 𝓤) (Y : PseudoClosenessSpace 𝓥)
 → (f : ⟪ X ⟫ → ⟪ Y ⟫)
 → 𝓤 ̇  
f-continuous' X Y f
 = (ϵ : ℕ) → (x₁ : ⟪ X ⟫) → Σ δ ꞉ ℕ , ((x₂ : ⟪ X ⟫)
 → C' X δ x₁ x₂ → C' Y ϵ (f x₁) (f x₂))

f-continuous : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
             → (f : ⟨ X ⟩ → ⟨ Y ⟩)
             → 𝓤 ̇  
f-continuous X Y = f-continuous' (ι X) (ι Y)

f-ucontinuous'
 : (X : PseudoClosenessSpace 𝓤) (Y : PseudoClosenessSpace 𝓥)
 → (f : ⟪ X ⟫ → ⟪ Y ⟫)
 → 𝓤 ̇  
f-ucontinuous' X Y f
 = (ϵ : ℕ) → Σ δ ꞉ ℕ , ((x₁ x₂ : ⟪ X ⟫)
 → C' X δ x₁ x₂ → C' Y ϵ (f x₁) (f x₂))

f-ucontinuous
 : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
 → (f : ⟨ X ⟩ → ⟨ Y ⟩)
 → 𝓤 ̇  
f-ucontinuous X Y = f-ucontinuous' (ι X) (ι Y)

ucontinuous-continuous : (X : ClosenessSpace 𝓤)
                       → (Y : ClosenessSpace 𝓥)
                       → (f : ⟨ X ⟩ → ⟨ Y ⟩)
                       → f-ucontinuous X Y f
                       → f-continuous  X Y f
ucontinuous-continuous X Y f ϕ ϵ x₁ = pr₁ (ϕ ϵ)  , pr₂ (ϕ ϵ) x₁

p-ucontinuous'-with-mod
 : (X : PseudoClosenessSpace 𝓤) → (p : ⟪ X ⟫ → Ω 𝓦) → ℕ → 𝓤 ⊔ 𝓦  ̇
p-ucontinuous'-with-mod X p δ
 = (x₁ x₂ : ⟪ X ⟫) → C' X δ x₁ x₂ → (p x₁ holds → p x₂ holds)

p-ucontinuous'
 : (X : PseudoClosenessSpace 𝓤) → (p : ⟪ X ⟫ → Ω 𝓦) → 𝓤 ⊔ 𝓦  ̇  
p-ucontinuous' X p
 = Σ δ ꞉ ℕ , p-ucontinuous'-with-mod X p δ

p-ucontinuous-with-mod
 : (X : ClosenessSpace 𝓤) → (p : ⟨ X ⟩ → Ω 𝓦) → ℕ → 𝓤 ⊔ 𝓦  ̇
p-ucontinuous-with-mod X p δ = p-ucontinuous'-with-mod (ι X) p δ

p-ucontinuous : (X : ClosenessSpace 𝓤) → (p : ⟨ X ⟩ → Ω 𝓦) → 𝓤 ⊔ 𝓦  ̇ 
p-ucontinuous X p 
 = Σ δ ꞉ ℕ , p-ucontinuous-with-mod X p δ
```

## Continuity lemmas

```
id-ucontinuous : (X : ClosenessSpace 𝓤) → f-ucontinuous X X id
id-ucontinuous X ϵ = ϵ , λ _ _ → id

p-ucontinuous-comp : (X : ClosenessSpace 𝓤)
                   → (Y : ClosenessSpace 𝓥)
                   → (f : ⟨ X ⟩ → ⟨ Y ⟩)
                   → f-ucontinuous X Y f
                   → (p : ⟨ Y ⟩ → Ω 𝓦)
                   → p-ucontinuous Y p
                   → p-ucontinuous X (p ∘ f)
p-ucontinuous-comp X Y f ϕᶠ p (δ , ϕᵖ)
 = pr₁ (ϕᶠ δ)
 , λ x₁ x₂ Cx₁x₂ → ϕᵖ (f x₁) (f x₂)
                     (pr₂ (ϕᶠ δ) x₁ x₂ Cx₁x₂)

f-ucontinuous-comp' : (X : PseudoClosenessSpace 𝓤)
                    → (Y : PseudoClosenessSpace 𝓥)
                    → (Z : PseudoClosenessSpace 𝓦)
                    → (f : ⟪ X ⟫ → ⟪ Y ⟫)
                    → (g : ⟪ Y ⟫ → ⟪ Z ⟫)
                    → f-ucontinuous' X Y f
                    → f-ucontinuous' Y Z g
                    → f-ucontinuous' X Z (g ∘ f)
f-ucontinuous-comp' X Y Z f g ϕᶠ ϕᵍ ε
 = pr₁ (ϕᶠ (pr₁ (ϕᵍ ε)))
 , λ x₁ x₂ Cx₁x₂ → pr₂ (ϕᵍ ε) (f x₁) (f x₂)
                    (pr₂ (ϕᶠ (pr₁ (ϕᵍ ε))) x₁ x₂ Cx₁x₂)

f-ucontinuous-comp : (X : ClosenessSpace 𝓤)
                   → (Y : ClosenessSpace 𝓥)
                   → (Z : ClosenessSpace 𝓦)
                   → (f : ⟨ X ⟩ → ⟨ Y ⟩)
                   → (g : ⟨ Y ⟩ → ⟨ Z ⟩)
                   → f-ucontinuous X Y f
                   → f-ucontinuous Y Z g
                   → f-ucontinuous X Z (g ∘ f)
f-ucontinuous-comp X Y Z f g ϕᶠ ϕᵍ ε
 = pr₁ (ϕᶠ (pr₁ (ϕᵍ ε)))
 , λ x₁ x₂ Cx₁x₂ → pr₂ (ϕᵍ ε) (f x₁) (f x₂)
                    (pr₂ (ϕᶠ (pr₁ (ϕᵍ ε))) x₁ x₂ Cx₁x₂)

C-ucontinuous-l : (X : ClosenessSpace 𝓤)
                → (ϵ : ℕ) (y : ⟨ X ⟩)
                → p-ucontinuous X (λ x → CΩ X ϵ x y)
C-ucontinuous-l X ϵ y = ϵ , γ
 where
  γ : (x₁ x₂ : ⟨ X ⟩) → C X ϵ x₁ x₂ → C X ϵ x₁ y → C X ϵ x₂ y
  γ x₁ x₂ Cx₁x₂ Cx₁y
   = C-trans X ϵ x₂ x₁ y (C-sym X ϵ x₁ x₂ Cx₁x₂) Cx₁y

C-ucontinuous-r : (X : ClosenessSpace 𝓤)
                → (ϵ : ℕ) (y : ⟨ X ⟩)
                → p-ucontinuous X (λ x → CΩ X ϵ y x)
C-ucontinuous-r X ϵ y = ϵ , γ
 where
  γ : (x₁ x₂ : ⟨ X ⟩) → C X ϵ x₁ x₂ → C X ϵ y x₁ → C X ϵ y x₂
  γ x₁ x₂ Cx₁x₂ Cyx₁ = C-trans X ϵ y x₁ x₂ Cyx₁ Cx₁x₂
```

## Predicates from closeness relations

```
decidable-predicate : (𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓦 ⁺  ̇
decidable-predicate 𝓦 X
 = Σ p ꞉ (X → Ω 𝓦) , is-complemented (λ x → (p x) holds)

decidable-uc-predicate
 : (𝓦 : Universe) → ClosenessSpace 𝓤 → 𝓤 ⊔ 𝓦 ⁺  ̇
decidable-uc-predicate 𝓦 X
 = Σ (p , d) ꞉ decidable-predicate 𝓦 ⟨ X ⟩ , p-ucontinuous X p

-- LINK
C-decidable-uc-predicate-l : (X : ClosenessSpace 𝓤)
                           → (ϵ : ℕ) (y : ⟨ X ⟩)
                           → decidable-uc-predicate 𝓤₀ X
C-decidable-uc-predicate-l X ϵ y
 = ((λ x → CΩ X ϵ x y)
  , (λ x → C-decidable X ϵ x y))
 , C-ucontinuous-l X ϵ y

C-decidable-uc-predicate-r : (X : ClosenessSpace 𝓤)
                           → (ϵ : ℕ) (y : ⟨ X ⟩)
                           → decidable-uc-predicate 𝓤₀ X
C-decidable-uc-predicate-r X ϵ y
 = ((λ x → CΩ X ϵ y x)
  , (λ x → C-decidable X ϵ y x))
 , C-ucontinuous-r X ϵ y

C-f-decidable-uc-predicate-l : (X : ClosenessSpace 𝓤)
                             → (Y : ClosenessSpace 𝓥)
                             → (f : ⟨ X ⟩ → ⟨ Y ⟩)
                             → f-ucontinuous X Y f
                             → (ϵ : ℕ) (y : ⟨ Y ⟩)
                             → decidable-uc-predicate 𝓤₀ X
C-f-decidable-uc-predicate-l X Y f ϕ ϵ y
 = ((λ x → CΩ Y ϵ (f x) y)
  , (λ x → C-decidable Y ϵ (f x) y))
 , p-ucontinuous-comp X Y f ϕ
     (λ x → CΩ Y ϵ x y)
     (C-ucontinuous-l Y ϵ y)

C-f-decidable-uc-predicate-r : (X : ClosenessSpace 𝓤)
                             → (Y : ClosenessSpace 𝓥)
                             → (f : ⟨ X ⟩ → ⟨ Y ⟩)
                             → f-ucontinuous X Y f
                             → (ϵ : ℕ) (y : ⟨ Y ⟩)
                             → decidable-uc-predicate 𝓤₀ X
C-f-decidable-uc-predicate-r X Y f ϕ ϵ y
 = ((λ x → CΩ Y ϵ y (f x))
  , (λ x → C-decidable Y ϵ y (f x)))
 , p-ucontinuous-comp X Y f ϕ
     (λ x → CΩ Y ϵ y x)
     (C-ucontinuous-r Y ϵ y)
```

## Totally bounded

```
_is_net-of_ : (X' : 𝓤'  ̇ ) → ℕ → ClosenessSpace 𝓤 → 𝓤 ⊔ 𝓤'  ̇
X' is ϵ net-of X
 = (Σ g ꞉ (  X'  → ⟨ X ⟩)
 , Σ h ꞉ (⟨ X ⟩ →   X' )
 , ((x : ⟨ X ⟩) → C X ϵ x (g (h x))))
 × finite-linear-order X'

pointed-has-a-0-net : (X : ClosenessSpace 𝓤)
                    → pointed ⟨ X ⟩
                    → Σ X' ꞉ 𝓦 ̇ , (X' is 0 net-of X)
pointed-has-a-0-net X x
 = 𝟙 , ((λ _ → x) , (λ _ → ⋆) , λ _ _ ()) , 𝟙-is-finite

totally-bounded : ClosenessSpace 𝓤 → (𝓤' : Universe) → 𝓤 ⊔ (𝓤' ⁺)  ̇ 
totally-bounded X 𝓤' = (ϵ : ℕ) → Σ X' ꞉ 𝓤' ̇ , X' is ϵ net-of X
```

[⇐ Index](../html/TWA.Thesis.index.html)

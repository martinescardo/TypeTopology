[⇐ Index](../html/TWA.Thesis.index.html)

# Uniformly continuously searchable closeness spaces

```agda
{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import NotionsOfDecidability.Complemented
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Equiv
open import UF.DiscreteAndSeparated
open import MLTT.Two-Properties
open import Fin.Type
open import Fin.Bishop

module TWA.Thesis.Chapter3.SearchableTypes (fe : FunExt) where

open import TWA.Thesis.Chapter3.ClosenessSpaces fe
 hiding (decidable-predicate;decidable-uc-predicate)
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
 using (decidable-𝟚; decidable-𝟚₁; 𝟚-decidable₁)
```

## Searchable types

```
decidable-predicate : (𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓦 ⁺  ̇
decidable-predicate 𝓦 X
 = Σ p ꞉ (X → Ω 𝓦) , is-complemented (λ x → (p x) holds)

searchable𝓔 : (𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ (𝓦 ⁺)  ̇
searchable𝓔 𝓦 X = Σ 𝓔 ꞉ (decidable-predicate 𝓦 X → X)
                , (((p , d) : decidable-predicate 𝓦 X)
                → (Σ x ꞉ X , (p x holds)) → p (𝓔 (p , d)) holds)

searchable : (𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ (𝓦 ⁺)  ̇
searchable 𝓦 X
 = ((p , d) : decidable-predicate 𝓦 X)
 → Σ x₀ ꞉ X , ((Σ x ꞉ X , (p x holds)) → p x₀ holds)

searchable-pointed
 : (𝓦 : Universe) → (X : 𝓤 ̇ ) → searchable 𝓦 X → X
searchable-pointed 𝓦 X Sx = pr₁ (Sx ((λ _ → ⊤) , (λ _ → inl ⋆)))

𝟙-searchable : searchable 𝓦 (𝟙 {𝓤})
𝟙-searchable {𝓦} {𝓤} (p , d) = ⋆ , S
 where
  S : (Σ x ꞉ 𝟙 , p x holds) → p ⋆ holds
  S  (⋆ , p⋆) = p⋆

𝟘+-searchable
 : {X : 𝓤 ̇ } → searchable 𝓦 X → searchable 𝓦 (𝟘 {𝓥} + X)
𝟘+-searchable {𝓤} {𝓦} {𝓥} {X} Sx (p , d)
 = inr x₀ , γ
 where
  px : decidable-predicate 𝓦 X
  px = p ∘ inr , d ∘ inr
  x₀ : X
  x₀ = pr₁ (Sx px)
  γx : (Σ x ꞉ X , (pr₁ px x holds)) → pr₁ px x₀ holds
  γx = pr₂ (Sx px)
  γ : (Σ x ꞉ 𝟘 + X , (p x holds)) → pr₁ px x₀ holds
  γ (inr x , pix) = γx (x , pix)

+-searchable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → searchable 𝓦 X
             → searchable 𝓦 Y
             → searchable 𝓦 (X + Y)
+-searchable {𝓤} {𝓥} {𝓦} {X} {Y} Sx Sy (p , d)
 = Cases (d (inl x₀))
     (λ  px₀ → inl x₀ , λ _ → px₀)
     (λ ¬px₀ → inr y₀ , γ ¬px₀)
 where
  px : decidable-predicate 𝓦 X
  px = p ∘ inl , d ∘ inl
  py : decidable-predicate 𝓦 Y
  py = p ∘ inr , d ∘ inr
  x₀ : X
  x₀ = pr₁ (Sx px)
  γx : Σ x ꞉ X , (pr₁ px x holds) → pr₁ px x₀ holds
  γx = pr₂ (Sx px)
  y₀ : Y
  y₀ = pr₁ (Sy py)
  γy : Σ y ꞉ Y , (pr₁ py y holds) → pr₁ py y₀ holds
  γy = pr₂ (Sy py)
  γ : ¬ (p (inl x₀) holds)
    → (Σ xy ꞉ (X + Y) , p xy holds)
    → p (inr y₀) holds
  γ ¬px₀ (inl x , pix) = 𝟘-elim (¬px₀ (γx (x , pix)))
  γ ¬px₀ (inr y , piy) = γy (y , piy)

Fin-searchable : (n : ℕ) → Fin n → searchable 𝓦 (Fin n)
Fin-searchable 1 _ = 𝟘+-searchable 𝟙-searchable
Fin-searchable (succ (succ n)) _
 = +-searchable (Fin-searchable (succ n) 𝟎) 𝟙-searchable

equivs-preserve-searchability
 : {X : 𝓤  ̇ } {Y : 𝓥  ̇}
 → (f : X → Y)
 → is-equiv f
 → searchable 𝓦 X
 → searchable 𝓦 Y
equivs-preserve-searchability {𝓤} {𝓥} {𝓦} {X} {Y}
 f ((g , η) , _) Sx (p , d) = y₀ , γ
 where
  px : decidable-predicate 𝓦 X
  px = p ∘ f , d ∘ f
  x₀ : X
  x₀ = pr₁ (Sx px)
  γx : Σ x ꞉ X , p (f x) holds → p (f x₀) holds
  γx = pr₂ (Sx px)
  y₀ : Y
  y₀ = f x₀
  γ : Σ y ꞉ Y , p y holds → p y₀ holds
  γ (y , py) = γx (g y , transport (λ - → p - holds) (η y ⁻¹) py)

≃-searchable
 : {X : 𝓤  ̇ } {Y : 𝓥 ̇ } → X ≃ Y → searchable 𝓦 X → searchable 𝓦 Y
≃-searchable (f , e) = equivs-preserve-searchability f e
             
finite-searchable : {X : 𝓤 ̇ }
                  → finite-linear-order X
                  → X
                  → searchable 𝓦 X
finite-searchable (0 , (g , _)) x = 𝟘-elim (g x)
finite-searchable (succ n , e) x
 = ≃-searchable (≃-sym e) (Fin-searchable (succ n) 𝟎) 

×-searchable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → searchable 𝓦 X
             → searchable 𝓦 Y
             → searchable 𝓦 (X × Y)
×-searchable {𝓤} {𝓥} {𝓦} {X} {Y} Sx Sy (p , d)
 = xy₀ , γ
 where
  py→ : X → decidable-predicate 𝓦 Y
  py→ x = p ∘ (x ,_) , d ∘ (x ,_)
  y₀ : X → Y
  y₀ x = pr₁ (Sy (py→ x))
  γy : (x : X) → Σ y ꞉ Y , p (x , y) holds → p (x , y₀ x) holds
  γy x = pr₂ (Sy (py→ x))
  px : decidable-predicate 𝓦 X
  px = (λ x → p (x , y₀ x)) , (λ x → d (x , y₀ x))
  x₀ : X
  x₀ = pr₁ (Sx px)
  γx : Σ x ꞉ X , p (x , y₀ x) holds → p (x₀ , y₀ x₀) holds
  γx = pr₂ (Sx px)
  xy₀ : X × Y
  xy₀ = x₀ , y₀ x₀
  γ : Σ (x , y) ꞉ X × Y , p (x , y) holds → p (x₀ , y₀ x₀) holds
  γ ((x , y) , pxy) = γx (x , (γy x (y , pxy)))
```

## Cantor searchability is LPO

```
LPO : 𝓤₀  ̇
LPO = (α : ℕ → 𝟚) → ((n : ℕ) → α n ＝ ₀) + (Σ n ꞉ ℕ , α n ＝ ₁)

no-ones-means-all-zero
 : (α : ℕ → 𝟚) → ¬ (Σ n ꞉ ℕ , α n ＝ ₁)  → (n : ℕ) → α n ＝ ₀
no-ones-means-all-zero α f n
 = Cases (𝟚-possibilities (α n)) id
     (λ αn＝₁ → 𝟘-elim (f (n , αn＝₁)))

ℕ-searchability-is-taboo : searchable 𝓤₀ ℕ → LPO
ℕ-searchability-is-taboo S α
 = Cases (𝟚-possibilities (α n))
     (λ αn＝₀ → inl (no-ones-means-all-zero α
                      (λ (i , αi＝₁) → zero-is-not-one
                                         (αn＝₀ ⁻¹ ∙ γ (i , αi＝₁)))))
     (λ αn＝₁ → inr (n , αn＝₁))
 where
  p : decidable-predicate 𝓤₀ ℕ
  pr₁ p n = (α n ＝ ₁) , 𝟚-is-set
  pr₂ p n = 𝟚-is-discrete (α n) ₁
  n : ℕ
  n = pr₁ (S p)
  γ : Σ i ꞉ ℕ , pr₁ p i holds → pr₁ p n holds
  γ = pr₂ (S p)

decidable-to-𝟚 : {X : 𝓤 ̇ } → is-decidable X
               → Σ b ꞉ 𝟚 , ((b ＝ ₁ ↔ X) × (b ＝ ₀ ↔ ¬ X))
decidable-to-𝟚 (inl  x)
 = ₁ , (((λ _ → x) , (λ _ → refl))
     , (𝟘-elim ∘ zero-is-not-one ∘ _⁻¹) , (λ ¬x → 𝟘-elim (¬x x)))
decidable-to-𝟚 (inr ¬x)
 = ₀ , ((𝟘-elim ∘ zero-is-not-one) , (λ x → 𝟘-elim (¬x x)))
     , (λ _ → ¬x) , (λ _ → refl)
     
LPO-implies-ℕ-searchability : LPO → searchable 𝓦 ℕ
LPO-implies-ℕ-searchability {𝓦} f (p , d)
 = Cases (f (λ i → decidable-𝟚 (d i)))
     (λ α∼₀ → 0 , λ (n , pn) → (𝟘-elim ∘ zero-is-not-one)
                                 (α∼₀ n ⁻¹ ∙ decidable-𝟚₁ (d n) pn))
     λ (i , αᵢ=₀) → i , λ _ → 𝟚-decidable₁ (d i) αᵢ=₀
```

## Uniformly continuously searchable closeness spaces

```
decidable-uc-predicate-with-mod
 : (𝓦 : Universe) → ClosenessSpace 𝓤 → ℕ → 𝓤 ⊔ 𝓦 ⁺  ̇
decidable-uc-predicate-with-mod 𝓦 X δ
 = Σ (p , d) ꞉ decidable-predicate 𝓦 ⟨ X ⟩
 , p-ucontinuous-with-mod X p δ

decidable-uc-predicate
 : (𝓦 : Universe) → ClosenessSpace 𝓤 → 𝓤 ⊔ 𝓦 ⁺  ̇
decidable-uc-predicate 𝓦 X
 = Σ (p , d) ꞉ decidable-predicate 𝓦 ⟨ X ⟩ , p-ucontinuous X p

to-uc-pred : (𝓦 : Universe)
           → (X : ClosenessSpace 𝓤)
           → (δ : ℕ)
           → decidable-uc-predicate-with-mod 𝓦 X δ
           → decidable-uc-predicate 𝓦 X
to-uc-pred 𝓦 X δ ((p , d) , ϕ) = (p , d) , δ , ϕ

get-uc-mod : (X : ClosenessSpace 𝓤) → decidable-uc-predicate 𝓦 X → ℕ
get-uc-mod 𝓦 (_ , δ , _) = δ

csearchable𝓔 : (𝓦 : Universe) → ClosenessSpace 𝓤 → 𝓤 ⊔ (𝓦 ⁺)  ̇
csearchable𝓔 𝓦 X
 = Σ 𝓔 ꞉ (decidable-uc-predicate 𝓦 X → ⟨ X ⟩)
 , ((((p , d) , ϕ) : decidable-uc-predicate 𝓦 X)
 → (Σ x ꞉ ⟨ X ⟩ , (p x holds))
 → p (𝓔 ((p , d) , ϕ)) holds)

csearchable : (𝓦 : Universe) → ClosenessSpace 𝓤 → 𝓤 ⊔ (𝓦 ⁺)  ̇
csearchable 𝓦 X
 = (((p , d) , ϕ) : decidable-uc-predicate 𝓦 X)
 → Σ x₀ ꞉ ⟨ X ⟩ , ((Σ x ꞉ ⟨ X ⟩ , (p x holds)) → p x₀ holds)

csearchable→csearchable𝓔
 : (X : ClosenessSpace 𝓤) → csearchable 𝓦 X → csearchable𝓔 𝓦 X
csearchable→csearchable𝓔 X S = (λ p → pr₁ (S p)) , (λ p → pr₂ (S p))

csearchable𝓔→csearchable
 : (X : ClosenessSpace 𝓤) → csearchable𝓔 𝓦 X → csearchable 𝓦 X
csearchable𝓔→csearchable X (𝓔 , S) p = 𝓔 p , S p

searchable→csearchable : {𝓦 : Universe} (X : ClosenessSpace 𝓤)
                       →  searchable 𝓦 ⟨ X ⟩
                       → csearchable 𝓦   X
searchable→csearchable X S ((p , d) , _) = S (p , d)

csearchable-pointed
 : (𝓦 : Universe)
 → (X : ClosenessSpace 𝓤)
 → csearchable 𝓦 X
 → ⟨ X ⟩ 
csearchable-pointed 𝓦 X Sx
 = pr₁ (Sx (((λ _ → ⊤) , (λ _ → inl ⋆)) , 0 , λ _ _ _ → id))

totally-bounded-csearchable : (X : ClosenessSpace 𝓤)
                            → ⟨ X ⟩
                            → (t : totally-bounded X 𝓤')
                            → csearchable 𝓦 X
totally-bounded-csearchable {𝓤} {𝓤'} {𝓦} X x t ((p , d) , δ , ϕ)
 = x₀ , γ
 where
  X' : 𝓤'  ̇
  X' = pr₁ (t δ)
  g  :   X'  → ⟨ X ⟩
  g  = pr₁ (pr₁ (pr₂ (t δ)))
  h  : ⟨ X ⟩ →   X'
  h  = pr₁ (pr₂ (pr₁ (pr₂ (t δ))))
  η  : (x : ⟨ X ⟩) → C X δ x (g (h x))
  η  = pr₂ (pr₂ (pr₁ (pr₂ (t δ))))
  f  : finite-linear-order X'
  f  = pr₂ (pr₂ (t δ))
  p' : decidable-predicate 𝓦 X'
  p' = p ∘ g , d ∘ g
  Sx : searchable 𝓦 X'
  Sx = finite-searchable f (h x)
  x'₀ : X'
  x'₀ = pr₁ (Sx p')
  γ' : (Σ x' ꞉ X' , p (g x') holds) → p (g x'₀) holds
  γ' = pr₂ (Sx p')
  x₀  : ⟨ X ⟩
  x₀  = g x'₀
  γ : (Σ x ꞉ ⟨ X ⟩ , p x holds) → p x₀ holds
  γ (x , px) = γ' (h x , (ϕ x (g (h x)) (η x) px))
```

[⇐ Index](../html/TWA.Thesis.index.html)

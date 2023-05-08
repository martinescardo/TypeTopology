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
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient
open import UF.Miscelanea
open import MLTT.Two-Properties
open import UF.Equiv

module Thesis.SearchableTypes (fe : FunExt) where

_≡_ = Id

-- Definition 3.1.1
decidable-predicate : (𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓦 ⁺  ̇
decidable-predicate 𝓦 X
 = Σ p ꞉ (X → Ω 𝓦) , complemented (λ x → (p x) holds)

-- Definition 3.1.2/3
searchable : (𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ (𝓦 ⁺)  ̇
searchable 𝓦 X = Σ 𝓔 ꞉ (decidable-predicate 𝓦 X → X)
                , (((p , d) : decidable-predicate 𝓦 X)
                → (Σ x ꞉ X , (p x holds)) → p (𝓔 (p , d)) holds)

-- Lemma 3.1.4
searchable-inhabited : (𝓦 : Universe) → (X : 𝓤 ̇ )
                     → searchable 𝓦 X → X
searchable-inhabited 𝓦 X (𝓔 , S) = 𝓔 ((λ _ → ⊤Ω) , (λ _ → inl ⋆))

-- Definition 3.1.5
𝔽 : ℕ → 𝓤₀  ̇
𝔽 0 = 𝟘
𝔽 (succ n) = 𝟙 + 𝔽 n

-- Definition 3.1.6
finite : 𝓤 ̇ → 𝓤  ̇
finite X = Σ n ꞉ ℕ , 𝔽 n ≃ X

-- Lemma 3.1.7
𝔽-discrete : (n : ℕ) → is-discrete (𝔽 n)
𝔽-discrete 0 = 𝟘-is-discrete
𝔽-discrete (succ n) = +-is-discrete 𝟙-is-discrete (𝔽-discrete n)

finite-discrete : {X : 𝓤 ̇ } → finite X → is-discrete X
finite-discrete (n , e) = equiv-to-discrete e (𝔽-discrete n)

-- Lemma 3.1.8
𝟙-searchable : searchable 𝓦 (𝟙 {𝓤})
𝟙-searchable {𝓦} {𝓤} = (λ _ → ⋆) , S
 where
  S : ((p , d) : decidable-predicate 𝓦 𝟙)
    → (Σ x ꞉ 𝟙 , p x holds) → p ⋆ holds
  S (p , d) (⋆ , p⋆) = p⋆

+𝟘-searchable : {X : 𝓤 ̇ } → searchable 𝓦 X
              → searchable 𝓦 (X + 𝟘 {𝓥})
+𝟘-searchable {𝓤} {𝓦} {𝓥} {X} (𝓔x , Sx) = 𝓔 , S
 where
  px→ : decidable-predicate 𝓦 (X + 𝟘 {𝓥})
      → decidable-predicate 𝓦  X
  px→ (p , d) = p ∘ inl , d ∘ inl
  𝓔 : decidable-predicate 𝓦 (X + 𝟘) → X + 𝟘
  𝓔 = inl ∘ 𝓔x ∘ px→
  S : ((p , d) : decidable-predicate 𝓦 (X + 𝟘))
    → (Σ x ꞉ (X + 𝟘) , p x holds) → p (𝓔 (p , d)) holds
  S (p , d) (inl x , px) = Sx (px→ (p , d)) (x , px)

-- Lemma 3.1.9
+-searchable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
             → searchable 𝓦 X → searchable 𝓦 Y
             → searchable 𝓦 (X + Y)
+-searchable {𝓤} {𝓥} {𝓦} {X} {Y} (𝓔x , Sx) (𝓔y , Sy) = 𝓔 , S
 where
  px→ : decidable-predicate 𝓦 (X + Y) → decidable-predicate 𝓦 X
  px→ (p , d) = p ∘ inl , d ∘ inl
  py→ : decidable-predicate 𝓦 (X + Y) → decidable-predicate 𝓦 Y
  py→ (p , d) = p ∘ inr , d ∘ inr
  𝓔x→ = 𝓔x ∘ px→ 
  𝓔y→ = 𝓔y ∘ py→
  Sx→ = Sx ∘ px→
  Sy→ = Sy ∘ py→
  𝓔 : decidable-predicate 𝓦 (X + Y) → X + Y
  𝓔 (p , d) with d (inl (𝓔x→ (p , d)))
  ... | inl _ = inl (𝓔x→ (p , d))
  ... | inr _ = inr (𝓔y→ (p , d))
  S : ((p , d) : decidable-predicate 𝓦 (X + Y))
    → (Σ xy ꞉ X + Y , (p xy holds)) → p (𝓔 (p , d)) holds
  S (p , d) pxy with d (inl (𝓔x→ (p , d))) | pxy
  ... | inl  px₀ | _ = px₀
  ... | inr ¬px₀ |(inl x , px)
   = 𝟘-elim (¬px₀ (Sx→ (p , d) (x , px)))
  ... | inr ¬px₀ |(inr y , py) = Sy→ (p , d) (y , py)

-- Lemma 3.1.10
𝔽-searchable : (n : ℕ) → 𝔽 n → searchable 𝓦 (𝔽 n)
𝔽-searchable 1 _ = +𝟘-searchable 𝟙-searchable
𝔽-searchable (succ (succ n)) _
 = +-searchable 𝟙-searchable (𝔽-searchable (succ n) (inl ⋆))

-- Lemma 3.3.11
equivs-preserve-searchability : {X : 𝓤  ̇ } {Y : 𝓥  ̇}
                              → (f : X → Y) → is-equiv f
                              → searchable 𝓦 X
                              → searchable 𝓦 Y
equivs-preserve-searchability {𝓤} {𝓥} {𝓦} {X} {Y}
 f ((g , η) , _) (𝓔x , Sx) = 𝓔 , S
 where
  px→ : decidable-predicate 𝓦 Y → decidable-predicate 𝓦 X
  px→ (p , d) = p ∘ f , d ∘ f
  𝓔x→ = 𝓔x ∘ px→
  Sx→ = Sx ∘ px→
  𝓔 : decidable-predicate 𝓦 Y → Y
  𝓔 (p , d) = f (𝓔x→ (p , d))
  S : ((p , d) : decidable-predicate 𝓦 Y)
    → (Σ y ꞉ Y , p y holds) → p (𝓔 (p , d)) holds
  S (p , d) (y , py)
   = Sx→ (p , d) (g y , transport (λ - → p - holds) (η y ⁻¹) py)

≃-searchable : {X : 𝓤  ̇ } {Y : 𝓥 ̇ }
             → X ≃ Y → searchable 𝓦 X → searchable 𝓦 Y
≃-searchable (f , e) = equivs-preserve-searchability f e
             
-- Lemma 3.1.12
finite-searchable : {X : 𝓤 ̇ } → X → finite X → searchable 𝓦 X
finite-searchable x (0 , _ , (g , _) , _) = 𝟘-elim (g x)
finite-searchable x (succ n , e)
 = ≃-searchable e (𝔽-searchable (succ n) (inl ⋆))

-- Lemma 3.1.13
-- TODO !!

-- Definition 3.2.13-16, 21
open import CoNaturals.GenericConvergentSequence
  renaming (ℕ-to-ℕ∞ to _↑
         ; Zero-smallest to zero-minimal
         ; ∞-largest to ∞-maximal)

-- Lemma 3.2.17
≤-≼-relationship : (n m : ℕ) → n ≤ m ⇔ (n ↑) ≼ (m ↑)
pr₁ (≤-≼-relationship 0 m) n≤m = zero-minimal (m ↑)
pr₁ (≤-≼-relationship (succ n) (succ m)) n≤m
 = Succ-monotone (n ↑) (m ↑) (pr₁ (≤-≼-relationship n m) n≤m)
pr₂ (≤-≼-relationship 0 m) n≼m = ⋆
pr₂ (≤-≼-relationship (succ n) 0) n≼m
 = Succ-not-≼-Zero (n ↑) n≼m
pr₂ (≤-≼-relationship (succ n) (succ m)) n≼m
 = pr₂ (≤-≼-relationship n m) (Succ-loc (n ↑) (m ↑) n≼m)

-- Lemma 3.2.18
≼-right-decidable : (u : ℕ∞) (m : ℕ) → decidable (u ≼ (m ↑))
≼-right-decidable u m
 = Cases (𝟚-is-discrete (pr₁ u m) ₀) (inl ∘ γ₁) (inr ∘ γ₂)
 where
   γ₁ : {!!}
   γ₁ um=0 n un=1 = {!!}
   γ₂ : {!!}
   γ₂ um≠0 u≼m = {!!}

-- Lemma 3.2.19
≼-left-decidable : (n : ℕ) (v : ℕ∞) → decidable ((n ↑) ≼ v)
≼-left-decidable = {!!}

-- Definition 3.2.22
open import TWA.Closeness fe hiding (is-ultra; is-closeness)

is-ultra is-closeness : {X : 𝓤 ̇ } → (X → X → ℕ∞) → 𝓤 ̇
is-ultra {𝓤} {X} c
 = (x y z : X) → (n : ℕ) → min (c x y) (c y z) ≼ c x z

is-closeness c
 = indistinguishable-are-equal c
 × self-indistinguishable c
 × is-symmetric c
 × is-ultra c

is-closeness-space : (X : 𝓤 ̇ ) → 𝓤 ̇
is-closeness-space X = Σ c ꞉ (X → X → ℕ∞) , is-closeness c

ClosenessSpace : (𝓤 : Universe) → 𝓤 ⁺  ̇ 
ClosenessSpace 𝓤
 = Σ X ꞉ 𝓤 ̇ , Σ c ꞉ (X → X → ℕ∞) , is-closeness c

-- Definition 3.2.23 [ Doesn't say in paper that this is an equiv rel ? TODO ]

B : ((X , _) : ClosenessSpace 𝓤) → ℕ → X → X → 𝓤₀  ̇   
B (X , c , _) n x y = (n ↑) ≼ c x y

⟨_⟩ : ClosenessSpace 𝓤 → 𝓤 ̇
⟨ X , _ ⟩ = X

B-is-eq : (C : ClosenessSpace 𝓤)
        → (n : ℕ) → is-equiv-relation (B C n)
pr₁ (B-is-eq (X , c , i , j , k , l) n) x y
 = Π-is-prop (fe _ _) (λ _ → Π-is-prop (fe _ _) (λ _ → 𝟚-is-set))
pr₁ (pr₂ (B-is-eq (X , c , i , j , k , l) n)) x m η
 = transport (λ - → ℕ∞-to-ℕ→𝟚 - m ≡ ₁) (j x ⁻¹) refl
pr₁ (pr₂ (pr₂ (B-is-eq (X , c , i , j , k , l) n))) x y η m ρ
 = transport (λ - → ℕ∞-to-ℕ→𝟚 - m ≡ ₁) (k x y) (η m ρ)
pr₂ (pr₂ (pr₂ (B-is-eq (X , c , i , j , k , l) n))) x y z η ρ m π
 = l x y z n m ((Lemma[a＝₁→b＝₁→min𝟚ab＝₁] (η m π) (ρ m π)))

B⁼ : ((X , ci) : ClosenessSpace 𝓤) → (n : ℕ) → EqRel X
B⁼ C n = B C n , B-is-eq C n

-- Definition 3.2.24 [ not needed ? ]

-- Definition 3.2.25

f-continuous : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
             → (f : ⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇  
f-continuous X Y f
 = (ϵ : ℕ) → (x₁ : ⟨ X ⟩) → Σ δ ꞉ ℕ , ((x₂ : ⟨ X ⟩)
 → B X δ x₁ x₂ → B Y ϵ (f x₁) (f x₂))

-- Definition 3.2.26
f-ucontinuous : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
              → (f : ⟨ X ⟩ → ⟨ Y ⟩) → 𝓤 ̇  
f-ucontinuous X Y f
 = (ϵ : ℕ) → Σ δ ꞉ ℕ , ((x₁ x₂ : ⟨ X ⟩)
 → B X δ x₁ x₂ → B Y ϵ (f x₁) (f x₂))

-- Lemma 3.2.27
ucontinuous-continuous : (X : ClosenessSpace 𝓤)
                       → (Y : ClosenessSpace 𝓥)
                       → (f : ⟨ X ⟩ → ⟨ Y ⟩)
                       → f-ucontinuous X Y f → f-continuous X Y f
ucontinuous-continuous X Y f ϕ ϵ x₁ = pr₁ (ϕ ϵ)  , pr₂ (ϕ ϵ) x₁

-- Definition 3.2.28
p-ucontinuous : (X : ClosenessSpace 𝓤)
              → (p : ⟨ X ⟩ → Ω 𝓦) → 𝓤 ⊔ 𝓦  ̇  
p-ucontinuous X p
 = Σ δ ꞉ ℕ , ((x₁ x₂ : ⟨ X ⟩)
 → B X δ x₁ x₂ → (p x₁ holds → p x₂ holds))
           

-- Examples 3.2.3 [ TODO link to blog post ]

-- Definition 3.3.2 [ TODO in paper needs to be a closeness space, not a general type ]
{- First, some things TODO put in Section 2 -}
_-sect : {X : 𝓤 ̇ } → EqRel {𝓤} {𝓤'} X
      → (𝓥 : Universe) → 𝓤 ⊔ 𝓤' ⊔ (𝓥 ⁺)  ̇
((_≣_ , _) -sect) 𝓥
 = Σ X' ꞉ 𝓥 ̇ , Σ g ꞉ (X' → _) , ((x : _) → Σ x' ꞉ X' , (x ≣ g x'))

_cover-of_ : ℕ → ClosenessSpace 𝓤 → (𝓥 : Universe) → 𝓤 ⊔ (𝓥 ⁺) ̇
(ϵ cover-of X) 𝓥 = (B⁼ X ϵ -sect) 𝓥

-- Definition 3.3.3
totally-bounded : ClosenessSpace 𝓤 → (𝓥 : Universe) → 𝓤 ⊔ (𝓥 ⁺) ̇ 
totally-bounded X 𝓥
 = (ϵ : ℕ) → Σ (X' , _) ꞉ (ϵ cover-of X) 𝓥 , finite X'

-- Definition 3.3.4
decidable-uc-predicate : (𝓦 : Universe) → ClosenessSpace 𝓤
                       → 𝓤 ⊔ 𝓦 ⁺  ̇
decidable-uc-predicate 𝓦 X
 = Σ (p , d) ꞉ decidable-predicate 𝓦 ⟨ X ⟩ , p-ucontinuous X p

get-uc-mod : (X : ClosenessSpace 𝓤)
           → decidable-uc-predicate 𝓦 X → ℕ
get-uc-mod 𝓦 (_ , δ , _) = δ

-- Definition 3.3.5/6
csearchable : (𝓦 : Universe) → ClosenessSpace 𝓤 → 𝓤 ⊔ (𝓦 ⁺)  ̇
csearchable 𝓦 X
 = Σ 𝓔 ꞉ (decidable-uc-predicate 𝓦 X → ⟨ X ⟩)
 , ((((p , d) , ϕ) : decidable-uc-predicate 𝓦 X)
 → (Σ x ꞉ ⟨ X ⟩ , (p x holds)) → p (𝓔 ((p , d) , ϕ)) holds)

-- Need to decide which to use in the paper TODO
csearchable' : (𝓦 : Universe) → ClosenessSpace 𝓤 → 𝓤 ⊔ (𝓦 ⁺)  ̇
csearchable' 𝓦 X
 = (((p , d) , ϕ) : decidable-uc-predicate 𝓦 X)
 → Σ x₀ ꞉ ⟨ X ⟩ , ((Σ x ꞉ ⟨ X ⟩ , (p x holds)) → p x₀ holds)

-- Theorem 3.3.7
-- Should be in paper TODO
semi-searchable : ClosenessSpace 𝓤 → (𝓥 𝓦 : Universe)
                → 𝓤 ⊔ (𝓥 ⁺) ⊔ (𝓦 ⁺)  ̇ 
semi-searchable X 𝓥 𝓦
 = (ϵ : ℕ) → Σ (X' , _) ꞉ (ϵ cover-of X) 𝓥 , searchable 𝓦 X'

searchable-covers-csearchable : (X : ClosenessSpace 𝓤)
                              → semi-searchable X 𝓥 𝓦
                              → csearchable' 𝓦 X
searchable-covers-csearchable {𝓤} {𝓥} {𝓦} X C ((p , d) , δ , ϕ)
 = x₀ , γ
 where
  X' : 𝓥 ̇
  g  : X' → ⟨ X ⟩
  η  : (x : ⟨ X ⟩) → Σ x' ꞉ X' , B X δ x (g x')
  𝓔' : decidable-predicate 𝓦 X' → X'
  S' : ((p' , d') : decidable-predicate 𝓦 X')
     → (Σ x' ꞉ X' , p' x' holds) → p' (𝓔' (p' , d')) holds
  p' : decidable-predicate 𝓦 X'
  p' = p ∘ g , d ∘ g
  x₀  : ⟨ X ⟩
  x₀  = g (𝓔' p')
  γ : (Σ x ꞉ ⟨ X ⟩ , p x holds) → p x₀ holds
  γ (x , px) = S' p' (x' , (ϕ x (g x') η' px))
   where
     x' : X'
     x' = pr₁ (η x)
     η' : B X δ x (g x')
     η' = pr₂ (η x)
  X' = pr₁ (pr₁ (C δ))
  g  = pr₁ (pr₂ (pr₁ (C δ)))
  η  = pr₂ (pr₂ (pr₁ (C δ)))
  𝓔' = pr₁ (pr₂ (C δ))
  S' = pr₂ (pr₂ (C δ))
  
-- Corollary 3.3.8
-- Add inhabited assumption
totally-bounded-csearchable : (X : ClosenessSpace 𝓤)
                            → (t : totally-bounded X 𝓥)
                            → ((ϵ : ℕ) → pr₁ (pr₁ (t ϵ)))
                            → csearchable' 𝓦 X
totally-bounded-csearchable X t i
 = searchable-covers-csearchable X
     (λ ϵ → (pr₁ (t ϵ)) , finite-searchable (i ϵ) (pr₂ (t ϵ)))

-- Theorem 3.3.9 [ TODO link to blog post ]

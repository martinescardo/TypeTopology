\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import NotionsOfDecidability.Complemented
open import UF.Subsingletons
open import UF.Equiv

module TWA.Thesis.Chapter3.SearchableTypes (fe : FunExt) where

-- Definition 3.1.1
decidable-predicate : (𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ 𝓦 ⁺  ̇
decidable-predicate 𝓦 X
 = Σ p ꞉ (X → Ω 𝓦) , is-complemented (λ x → (p x) holds)

-- Definition 3.1.2/3
searchable : (𝓦 : Universe) → 𝓤 ̇ → 𝓤 ⊔ (𝓦 ⁺)  ̇
searchable 𝓦 X = Σ 𝓔 ꞉ (decidable-predicate 𝓦 X → X)
                , (((p , d) : decidable-predicate 𝓦 X)
                → (Σ x ꞉ X , (p x holds)) → p (𝓔 (p , d)) holds)

-- Lemma 3.1.4
searchable-inhabited : (𝓦 : Universe) → (X : 𝓤 ̇ )
                     → searchable 𝓦 X → X
searchable-inhabited 𝓦 X (𝓔 , S) = 𝓔 ((λ _ → ⊤Ω) , (λ _ → inl ⋆))

-- Definition 3.1.5-7
open import TWA.Thesis.Chapter2.FiniteDiscrete

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
finite-discrete-searchable : {X : 𝓤 ̇ } → X → finite-discrete X
                           → searchable 𝓦 X
finite-discrete-searchable x (0 , _ , (g , _) , _) = 𝟘-elim (g x)
finite-discrete-searchable x (succ n , e)
 = ≃-searchable e (𝔽-searchable (succ n) (inl ⋆))

-- Lemma 3.1.13
-- TODO !!

open import TWA.Thesis.Chapter3.ClosenessSpaces fe

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
searchable-covers-csearchable {𝓤} {𝓥} {𝓦} X S ((p , d) , δ , ϕ)
 = x₀ , γ
 where
  X' : 𝓥 ̇
  g  : X' → ⟨ X ⟩
  η  : (x : ⟨ X ⟩) → Σ x' ꞉ X' , C X δ x (g x')
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
     η' : C X δ x (g x')
     η' = pr₂ (η x)
  X' = pr₁ (pr₁ (S δ))
  g  = pr₁ (pr₂ (pr₁ (S δ)))
  η  = pr₂ (pr₂ (pr₁ (S δ)))
  𝓔' = pr₁ (pr₂ (S δ))
  S' = pr₂ (pr₂ (S δ))
  
-- Corollary 3.3.8
-- Add inhabited assumption
totally-bounded-csearchable : (X : ClosenessSpace 𝓤)
                            → (t : totally-bounded X 𝓥)
                            → ((ϵ : ℕ) → pr₁ (pr₁ (t ϵ)))
                            → csearchable' 𝓦 X
totally-bounded-csearchable X t i
 = searchable-covers-csearchable X
     (λ ϵ → (pr₁ (t ϵ)) , finite-discrete-searchable (i ϵ) (pr₂ (t ϵ)))

-- Theorem 3.3.9 [ TODO link to blog post ]
-- in Tychonoff

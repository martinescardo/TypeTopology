```agda

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import NotionsOfDecidability.Complemented
open import UF.Subsingletons
open import UF.Equiv
open import TypeTopology.DiscreteAndSeparated
open import TWA.Thesis.Chapter2.FiniteDiscrete
open import TWA.Thesis.Chapter2.Sequences

module TWA.Thesis.Chapter3.SearchableTypes-Examples
  (fe : FunExt) (pe : PropExt) where

open import TWA.Thesis.Chapter3.SearchableTypes fe
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import TWA.Thesis.Chapter3.PredicateEquality fe pe

-- Finite continuously searchable spaces.

finite-discrete-csearchable
 : (X : ClosenessSpace 𝓤)
 → (f : finite-discrete ⟨ X ⟩)
 → pointed ⟨ X ⟩
 → csearchable 𝓦 X
finite-discrete-csearchable X f x
 = searchable→csearchable X
     (finite-discrete-searchable f x)

-- Disjoint union of continuously searchable spaces.

+-csearchable : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
              → csearchable 𝓦 X
              → csearchable 𝓦 Y
              → csearchable 𝓦 (+-ClosenessSpace X Y)
+-csearchable {𝓤} {𝓥} {𝓦} X Y Sx Sy ((p , d) , δ , ϕ)
 = xy₀ , γ
 where
  px : decidable-uc-predicate 𝓦 X
  px = (p ∘ inl , d ∘ inl) , δ , λ x₁ x₂ → ϕ (inl x₁) (inl x₂)
  py : decidable-uc-predicate 𝓦 Y
  py = (p ∘ inr , d ∘ inr) , δ , λ x₁ x₂ → ϕ (inr x₁) (inr x₂)
  x₀ : ⟨ X ⟩
  x₀ = pr₁ (Sx px)
  γx : (Σ x ꞉ ⟨ X ⟩ , (p (inl x) holds))    → p (inl x₀) holds
  γx = pr₂ (Sx px)
  y₀ : ⟨ Y ⟩
  y₀ = pr₁ (Sy py)
  γy : (Σ y ꞉ ⟨ Y ⟩ , (p (inr y) holds))    → p (inr y₀) holds
  γy = pr₂ (Sy py)
  xy₀ : ⟨ X ⟩ + ⟨ Y ⟩
  xy₀ with d (inl x₀)
  ... | inl _ = inl x₀
  ... | inr _ = inr y₀
  γ : (Σ xy ꞉ ⟨ X ⟩ + ⟨ Y ⟩ , (p xy holds)) → p xy₀ holds
  γ (inl x , px) with d (inl x₀)
  ... | inl  px₀ = px₀
  ... | inr ¬px₀ = (𝟘-elim ∘ ¬px₀) (γx (x , px))
  γ (inr y , py) with d (inl x₀)
  ... | inl  px₀ = px₀
  ... | inr ¬px₀ = γy (y , py)

-- Binary product closeness spaces

×-pred-left : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
            → decidable-uc-predicate 𝓦 (×-ClosenessSpace X Y)
            → ⟨ Y ⟩ → decidable-uc-predicate 𝓦 X
×-pred-left X Y ((p , d) , δ , ϕ) y
 = ((p ∘ (_, y)) , (d ∘ (_, y))) , δ
 , λ x₁ x₂ Cδx₁x₂
 → ϕ (x₁ , y) (x₂ , y)
     (×-C-combine X Y x₁ x₂ y y δ Cδx₁x₂ (C-refl Y δ y))

×-pred-right : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
             → decidable-uc-predicate 𝓦 (×-ClosenessSpace X Y)
             → ⟨ X ⟩ → decidable-uc-predicate 𝓦 Y
×-pred-right X Y ((p , d) , δ , ϕ) x
 = ((p ∘ (x ,_)) , (d ∘ (x ,_))) , δ
 , λ y₁ y₂ Cδy₁y₂
 → ϕ (x , y₁) (x , y₂)
     (×-C-combine X Y x x y₁ y₂ δ (C-refl X δ x) Cδy₁y₂)

×-csearchable : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
              → csearchable 𝓦 X
              → csearchable 𝓦 Y
              → csearchable 𝓦 (×-ClosenessSpace X Y)
×-csearchable {𝓤} {𝓥} {𝓦} X Y Sx Sy ((p , d) , δ , ϕ)
 = xy₀ , γ
 where
  py→ : ⟨ X ⟩ → decidable-uc-predicate 𝓦 Y
  py→ x = (p ∘ (x ,_) , d ∘ (x ,_))
        , δ , λ y₁ y₂ Cδy₁y₂ → ϕ (x , y₁) (x , y₂)
                (×-C-combine X Y x x y₁ y₂ δ (C-refl X δ x) Cδy₁y₂)
  y₀ : ⟨ X ⟩ → ⟨ Y ⟩
  y₀ x = pr₁ (Sy (py→ x))
  γy : (x : ⟨ X ⟩)
     → (Σ y ꞉ ⟨ Y ⟩ , (p (x , y) holds))
     → p (x , y₀ x) holds
  γy x = pr₂ (Sy (py→ x))
  pyϕ : (x₁ x₂ : ⟨ X ⟩)
      → C X δ x₁ x₂
      → (y : ⟨ Y ⟩)
      → p (x₁ , y) holds ⇔ p (x₂ , y) holds
  pyϕ x₁ x₂ Cδx₁x₂ y
   = ϕ (x₁ , y) (x₂ , y)
         (×-C-combine X Y x₁ x₂ y y δ Cδx₁x₂ (C-refl Y δ y))
   , ϕ (x₂ , y) (x₁ , y)
         (×-C-combine X Y x₂ x₁ y y δ (C-sym X δ x₁ x₂ Cδx₁x₂)
         (C-refl Y δ y))
  px : decidable-uc-predicate 𝓦 X
  px = ((λ x → p (x , y₀ x)) , λ x → d (x , y₀ x))
     , δ , λ x₁ x₂ Cδx₁x₂ → ϕ (x₁ , y₀ x₁) (x₂ , y₀ x₂)
             (×-C-combine X Y x₁ x₂ (y₀ x₁) (y₀ x₂) δ Cδx₁x₂
               (transport (λ - → C Y δ (y₀ x₁) (pr₁ (Sy -)))
                 (decidable-uc-predicate-＝ Y (py→ x₁) (py→ x₂)
                   refl (pyϕ x₁ x₂ Cδx₁x₂))
                 (C-refl Y δ (y₀ x₁))))
  x₀ : ⟨ X ⟩
  x₀ = pr₁ (Sx px)
  γx : (Σ x ꞉ ⟨ X ⟩ , (p (x , y₀ x) holds)) → p (x₀ , y₀ x₀) holds
  γx = pr₂ (Sx px)
  xy₀ : ⟨ X ⟩ × ⟨ Y ⟩
  xy₀ = x₀ , y₀ x₀
  γ : (Σ xy ꞉ ⟨ X ⟩ × ⟨ Y ⟩ , (p xy holds)) → p xy₀ holds
  γ ((x , y) , pxy) = γx (x , γy x (y , pxy))

-- Equivalence continuously searchable spaces.

≃-csearchable : {X : 𝓤 ̇} (Y : ClosenessSpace 𝓥)
              → (e : X ≃ ⟨ Y ⟩)
              → csearchable 𝓦 Y
              → csearchable 𝓦 (≃-ClosenessSpace Y e)
≃-csearchable {𝓤} {𝓥} {𝓦} {X}
 Y e@(f , (g , η) , (h , μ)) S ((p' , d') , δ , ϕ')
 = x₀ , γ
 where
  p : ⟨ Y ⟩ → Ω 𝓦
  p y = p' (g y)
  d : is-complemented (λ x → p x holds)
  d y = d' (g y)
  ϕ : p-ucontinuous-with-mod Y p δ
  ϕ y₁ y₂ Cδy₁y₂
   = ϕ' (g y₁) (g y₂)
       (C-trans Y δ (f (g y₁)) y₁ (f (g y₂))
         (C-id Y δ (f (g y₁)) y₁ (η y₁))
         (C-trans Y δ y₁ y₂ (f (g y₂)) Cδy₁y₂
           (C-id Y δ y₂ (f (g y₂)) (η y₂ ⁻¹))))
  x₀ : X
  x₀ = g (pr₁ (S ((p , d) , δ , ϕ)))
  γ : Sigma ⟨ ≃-ClosenessSpace Y e ⟩ (λ x → p' x holds)
    → p' x₀ holds
  γ (x , phx)
   = pr₂ (S ((p , d) , δ , ϕ))
       (f x , transport (λ - → p' - holds)
         (μ x ⁻¹ ∙ (ap h (η (f x) ⁻¹) ∙ μ (g (f x)))) phx)

-- Discrete-sequence continuously searchable spaces.

tail-predicate
 : {X : 𝓤 ̇ }
 → (f : finite-discrete X)
 → (i : is-discrete X)
 → (δ : ℕ)
 → (x : X)
 → decidable-uc-predicate-with-mod 𝓦
     (ℕ→D-ClosenessSpace i)
     (succ δ)
 → decidable-uc-predicate-with-mod 𝓦
     (ℕ→D-ClosenessSpace i)
     δ
tail-predicate {𝓤} {𝓦} {X} f i' δ x ((p' , d') , ϕ') = (p , d) , ϕ
 where
  p : (ℕ → X) → Ω _
  p xs = p' (x ∶∶ xs)
  d : is-complemented (λ x₁ → p x₁ holds)
  d xs = d' (x ∶∶ xs)
  ϕ : p-ucontinuous-with-mod (ℕ→D-ClosenessSpace _) p δ
  ϕ x₁ x₂ Cδx₁x₂
   = ϕ' (x ∶∶ x₁) (x ∶∶ x₂)
       (∼ⁿ-to-C i' _ _ (succ δ) γ)
   where
    γ : ((x ∶∶ x₁) ∼ⁿ (x ∶∶ x₂)) (succ δ)
    γ zero i<sδ = refl
    γ (succ i) i<sδ
     = C-to-∼ⁿ i' _ _ δ Cδx₁x₂ i i<sδ

discrete-finite-seq-csearchable'
 : {X : 𝓤 ̇ }
 → X 
 → (f : finite-discrete X)
 → (i : is-discrete X)
 → (δ : ℕ)
 → (((p , _) , _) : decidable-uc-predicate-with-mod 𝓦
                      (ℕ→D-ClosenessSpace i) δ)
 → Σ xs₀ ꞉ (ℕ → X)
 , ((Σ xs ꞉ (ℕ → X) , p xs holds) → p xs₀ holds)

head-predicate
 : {X : 𝓤 ̇ }
 → X
 → (f : finite-discrete X)
 → (i : is-discrete X)
 → (δ : ℕ)
 → decidable-uc-predicate-with-mod 𝓦 (ℕ→D-ClosenessSpace i) (succ δ)
 → decidable-predicate 𝓦 X
head-predicate {𝓤} {𝓦} {X} x₀ f i δ ((p , d) , ϕ)
 = p ∘ xs→ , d ∘ xs→
 where
  xs→ : X → (ℕ → X)
  xs→ x = x ∶∶ pr₁ (discrete-finite-seq-csearchable' x₀ f i δ
                     (tail-predicate f i δ x ((p , d) , ϕ)))
     
discrete-finite-seq-csearchable' x₀ f i zero ((p , d) , ϕ)
 = (λ _ → x₀)
 , λ (y , py) → ϕ y (λ _ → x₀) (λ n ()) py
discrete-finite-seq-csearchable'
 {𝓤} {𝓦} {X} x' f i (succ δ) ((p , d) , ϕ)
 = xs₀ , γ
 where
   pₕ  = head-predicate x' f i δ ((p , d) , ϕ)
   x₀ : X
   x₀ = pr₁ (finite-discrete-searchable f x' pₕ)
   γₕ : Σ x ꞉ X , pr₁ pₕ x holds → pr₁ pₕ x₀ holds
   γₕ = pr₂ (finite-discrete-searchable f x' pₕ)
   pₜ→ = λ x → tail-predicate f i δ x ((p , d) , ϕ)
   xs→ : (x : X) → Σ xs₀ ꞉ (ℕ → X)
       , ((Σ xs ꞉ (ℕ → X) , (pr₁ ∘ pr₁) (pₜ→ x) xs holds)
       → (pr₁ ∘ pr₁) (pₜ→ x) xs₀ holds) 
   xs→ x = discrete-finite-seq-csearchable' x' f i δ (pₜ→ x)
   xs₀ : ℕ → X
   xs₀ = x₀ ∶∶ pr₁ (xs→ x₀)
   γ : Σ xs ꞉ (ℕ → X) , (p xs holds) → p xs₀ holds
   γ (y , py)
    = γₕ (y 0 , pr₂ (xs→ (y 0))
        (y ∘ succ , ϕ y (y 0 ∶∶ (y ∘ succ))
          (λ n _ → decidable-𝟚₁ (discrete-decidable-seq _ _ _ _)
            λ i _ → ζ i) py))
    where
     ζ : y ∼ (y 0 ∶∶ (λ x₁ → y (succ x₁)))
     ζ zero = refl
     ζ (succ i) = refl

discrete-finite-seq-csearchable
 : {X : 𝓤 ̇ }
 → X 
 → (f : finite-discrete X)
 → (i : is-discrete X)
 → csearchable 𝓦 (ℕ→D-ClosenessSpace i)
discrete-finite-seq-csearchable x₀ f i ((p , d) , (δ , ϕ))
 = discrete-finite-seq-csearchable' x₀ f i δ ((p , d) , ϕ)

-- Tychonoff

tail-predicate-tych
 : (T : ℕ → ClosenessSpace 𝓤)
 → (δ : ℕ)
 → (x : ⟨ T 0 ⟩)
 → decidable-uc-predicate-with-mod 𝓦
     (Π-ClosenessSpace T) (succ δ)
 → decidable-uc-predicate-with-mod 𝓦
     (Π-ClosenessSpace (tail T)) δ
tail-predicate-tych {𝓤} {𝓦} T δ x₀ ((p' , d') , ϕ') = (p , d) , ϕ
 where
  p : Π (⟨_⟩ ∘ T ∘ succ) → Ω 𝓦
  p xs = p' (x₀ :: xs)
  d : is-complemented (λ x → p x holds)
  d xs = d' (x₀ :: xs)
  ϕ : p-ucontinuous-with-mod (Π-ClosenessSpace (T ∘ succ)) p δ
  ϕ xs ys Cδxsys
   = ϕ' (x₀ :: xs) (x₀ :: ys)
       (Π-C-combine T x₀ x₀ xs ys δ
         (C-refl (T 0) (succ δ) x₀)
           Cδxsys)

tychonoff'
 : (T : ℕ → ClosenessSpace 𝓤)
 → ((n : ℕ) → csearchable 𝓦 (T n))
 → (δ : ℕ)
 → (((p , _) , _) : decidable-uc-predicate-with-mod 𝓦
     (Π-ClosenessSpace T) δ)
 → Σ xs₀ ꞉ Π (⟨_⟩ ∘ T)
 , ((Σ xs ꞉ Π (⟨_⟩ ∘ T) , p xs holds) → p xs₀ holds)

head-predicate-tych
 : (T : ℕ → ClosenessSpace 𝓤)
 → ((n : ℕ) → csearchable 𝓦 (T n))
 → (δ : ℕ)
 → decidable-uc-predicate-with-mod 𝓦
     (Π-ClosenessSpace T) (succ δ)
 → decidable-uc-predicate 𝓦 (T 0)
head-predicate-tych {𝓤} {𝓦} T S δ ((p , d) , ϕ)
 = ((p ∘ xs→) , d ∘ xs→)
 , succ δ , γ
 where
  xs→ : ⟨ T 0 ⟩ → Π (⟨_⟩ ∘ T)
  xs→ x = x :: pr₁ (tychonoff' (T ∘ succ) (S ∘ succ) δ
                 (tail-predicate-tych T δ x ((p , d) , ϕ)))
  γ : p-ucontinuous-with-mod (T 0) (λ x → p (xs→ x)) (succ δ)
  γ x₁ x₂ Csδx₁x₂
   = ϕ (xs→ x₁) (xs→ x₂)
       (Π-C-combine T x₁ x₂ (xs→ x₁ ∘ succ) (xs→ x₂ ∘ succ)
         δ Csδx₁x₂ ζₛ)
    where
     χ : (xs : Π (⟨_⟩ ∘ T ∘ succ))
       → (pr₁ (pr₁ (tail-predicate-tych T δ x₁ ((p , d) , ϕ))) xs
           holds)
       ⇔ (pr₁ (pr₁ (tail-predicate-tych T δ x₂ ((p , d) , ϕ))) xs
           holds)
     χ xs = ϕ (x₁ :: xs) (x₂ :: xs)
              (Π-C-combine T x₁ x₂ xs xs δ
                Csδx₁x₂
                (C-refl (Π-ClosenessSpace (T ∘ succ)) δ xs))
          , ϕ (x₂ :: xs) (x₁ :: xs)
              (Π-C-combine T x₂ x₁ xs xs δ
                (C-sym (T 0) (succ δ) x₁ x₂ Csδx₁x₂)
                (C-refl (Π-ClosenessSpace (T ∘ succ)) δ xs))
     ζₛ : C (Π-ClosenessSpace (T ∘ succ)) δ
           (xs→ x₁ ∘ succ) (xs→ x₂ ∘ succ)
     ζₛ
      = transport (λ - → C (Π-ClosenessSpace (T ∘ succ)) δ
                    (xs→ x₁ ∘ succ)
                    (pr₁ (tychonoff' (T ∘ succ) (S ∘ succ) δ -)))
          (decidable-uc-predicate-with-mod-＝
            (Π-ClosenessSpace (T ∘ succ)) δ
            (tail-predicate-tych T δ x₁ ((p , d) , ϕ))
            (tail-predicate-tych T δ x₂ ((p , d) , ϕ))
            χ)
          (C-refl (Π-ClosenessSpace (T ∘ succ)) δ
            (xs→ x₁ ∘ succ))

tychonoff' T S 0 ((p , d) , ϕ)
 = (λ n → pr₁ (S n (((λ _ → ⊤Ω) , (λ _ → inl ⋆))
 , (0 , (λ x₁ x₂ _ _ → ⋆)))) )
 , (λ (α , pα) → ϕ α _ (λ _ ()) pα)
tychonoff' T S (succ δ) ((p , d) , ϕ) 
 = (x :: pr₁ (xs→ x)) , γ
 where
   pₜ→ = λ x → tail-predicate-tych T δ x ((p , d) , ϕ)
   pₕ  = head-predicate-tych T S δ ((p , d) , ϕ)
   xs→ : (x : ⟨ T 0 ⟩) →  Σ xs₀ ꞉ Π (⟨_⟩ ∘ T ∘ succ)
       , ((Σ xs ꞉ Π (⟨_⟩ ∘ T ∘ succ)
                , (pr₁ ∘ pr₁) (pₜ→ x) xs holds)
       → (pr₁ ∘ pr₁) (pₜ→ x) xs₀ holds) 
   xs→ x = tychonoff' (T ∘ succ) (S ∘ succ) δ (pₜ→ x)
   x : ⟨ T 0 ⟩
   x = pr₁ (S 0 pₕ)
   γₕ : _
   γₕ = pr₂ (S 0 pₕ)
   γ : _
   γ (y , py)
    = γₕ (y 0 , pr₂ (xs→ (y 0))
           (y ∘ succ
           , ϕ y (y 0 :: (y ∘ succ)) (Π-C-eta T y (succ δ)) py))

tychonoff : (T : ℕ → ClosenessSpace 𝓤)
          → ((n : ℕ) → csearchable 𝓦 (T n))
          → csearchable 𝓦 (Π-ClosenessSpace T)
tychonoff T S ((p , d) , δ , ϕ) = tychonoff' T S δ ((p , d) , ϕ)
```

{-
-}

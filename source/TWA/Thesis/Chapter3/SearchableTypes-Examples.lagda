\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import NotionsOfDecidability.Complemented
open import UF.Subsingletons
open import UF.Equiv
open import UF.Embeddings

module TWA.Thesis.Chapter3.SearchableTypes-Examples
  (fe : FunExt) (pe : PropExt) where

open import TWA.Thesis.Chapter2.FiniteDiscrete
open import TWA.Thesis.Chapter3.SearchableTypes fe
open import TWA.Thesis.Chapter2.Sequences
open import TypeTopology.DiscreteAndSeparated
open import TWA.Thesis.Chapter6.SequenceContinuity fe
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import UF.Subsingletons-FunExt

predicate-＝ : {X : 𝓤 ̇ }
             → (p₁ p₂ : X → Ω 𝓦)
             → ((x : X) → p₁ x holds ⇔ p₂ x holds)
             → p₁ ＝ p₂
predicate-＝ p₁ p₂ f
 = dfunext (fe _ _)
     (λ x → to-subtype-＝ (λ _ → being-prop-is-prop (fe _ _))
       (pe _ (pr₂ (p₁ x)) (pr₂ (p₂ x)) (pr₁ (f x)) (pr₂ (f x))))

complemented-is-prop : {X : 𝓤 ̇ }
                     → (p : X → Ω 𝓦)
                     → is-prop (is-complemented (λ x → p x holds))
complemented-is-prop p
 = Π-is-prop (fe _ _) (λ x → +-is-prop (pr₂ (p x))
     (Π-is-prop (fe _ _) (λ _ → 𝟘-is-prop))
     (λ px ¬px → ¬px px))

uc-continuous-is-prop : (X : ClosenessSpace 𝓤)
                      → (p : ⟨ X ⟩ → Ω 𝓦)
                      → (δ : ℕ)
                      → is-prop (p-ucontinuous-with-mod X p δ)
uc-continuous-is-prop X p δ
 = Π-is-prop (fe _ _) (λ _ → Π-is-prop (fe _ _)
     (λ _ → Π-is-prop (fe _ _) (λ _ → Π-is-prop (fe _ _)
       (λ _ → pr₂ (p _)))))

decidable-uc-predicate-＝''
 : (X : ClosenessSpace 𝓤)
 → (δ : ℕ)
 → (p₁ p₂ : ⟨ X ⟩ → Ω 𝓦)
 → (d₁ : is-complemented (λ x → p₁ x holds))
 → (d₂ : is-complemented (λ x → p₂ x holds))
 → (ϕ₁ : p-ucontinuous-with-mod X p₁ δ)
 → (ϕ₂ : p-ucontinuous-with-mod X p₂ δ)
 → p₁ ＝ p₂
 → _＝_ {_} {decidable-uc-predicate 𝓦 X}
     ((p₁ , d₁) , δ , ϕ₁) ((p₂ , d₂) , δ , ϕ₂)
decidable-uc-predicate-＝'' X δ p p d₁ d₂ ϕ₁ ϕ₂ refl
 = ap (λ - → (p , -) , δ , ϕ₁) (complemented-is-prop p d₁ d₂)
 ∙ ap (λ - → (p , d₂) , δ , -) (uc-continuous-is-prop X p δ ϕ₁ ϕ₂)

decidable-uc-predicate-＝'
 : (X : ClosenessSpace 𝓤)
 → (δ : ℕ)
 → (p₁ p₂ : ⟨ X ⟩ → Ω 𝓦)
 → (d₁ : is-complemented (λ x → p₁ x holds))
 → (d₂ : is-complemented (λ x → p₂ x holds))
 → (ϕ₁ : p-ucontinuous-with-mod X p₁ δ)
 → (ϕ₂ : p-ucontinuous-with-mod X p₂ δ)
 → ((x : ⟨ X ⟩) → p₁ x holds ⇔ p₂ x holds)
 → _＝_ {_} {decidable-uc-predicate 𝓦 X}
     ((p₁ , d₁) , δ , ϕ₁) ((p₂ , d₂) , δ , ϕ₂)
decidable-uc-predicate-＝' X δ p₁ p₂ d₁ d₂ ϕ₁ ϕ₂ f
 = decidable-uc-predicate-＝'' X δ p₁ p₂ d₁ d₂ ϕ₁ ϕ₂
     (predicate-＝ p₁ p₂ f)

decidable-uc-predicate-＝
 : (X : ClosenessSpace 𝓤)
 → (p@((p₁ , d₁) , δ₁ , ϕ₁) q@((p₂ , d₂) , δ₂ , ϕ₂)
    : decidable-uc-predicate 𝓦 X)
 → δ₁ ＝ δ₂
 → ((x : ⟨ X ⟩) → p₁ x holds ⇔ p₂ x holds)
 → p ＝ q
decidable-uc-predicate-＝
 X ((p₁ , d₁) , δ , ϕ₁) ((p₂ , d₂) , δ , ϕ₂) refl f
 = decidable-uc-predicate-＝' X δ p₁ p₂ d₁ d₂ ϕ₁ ϕ₂ f

decidable-uc-predicate-with-mod-＝
 : (X : ClosenessSpace 𝓤)
 → (δ : ℕ)
 → (p@((p₁ , d₁) , ϕ₁) q@((p₂ , d₂) , ϕ₂)
    : decidable-uc-predicate-with-mod 𝓦 X δ)
 → ((x : ⟨ X ⟩) → p₁ x holds ⇔ p₂ x holds)
 → p ＝ q
decidable-uc-predicate-with-mod-＝
 X δ ((p₁ , d₁) , ϕ₁) ((p₂ , d₂) , ϕ₂) f
 = to-subtype-＝ (λ p → uc-continuous-is-prop X (pr₁ p) δ)
     (to-subtype-＝ (λ p → complemented-is-prop p)
       (predicate-＝ p₁ p₂ f))

-- Finite continuously searchable spaces.

finite-discrete-csearchable
 : {X : 𝓤 ̇ }
 → (f : finite-discrete X)
 → pointed X
 → let d = finite-discrete-is-discrete f in
   csearchable 𝓦 (D-ClosenessSpace d)
finite-discrete-csearchable f x
 = searchable→csearchable (D-ClosenessSpace d)
     (finite-discrete-searchable f x)
 where d = finite-discrete-is-discrete f

-- Disjoint union of continuously searchable spaces.

+-csearchable : (X : ClosenessSpace 𝓤) (Y : ClosenessSpace 𝓥)
              → csearchable' 𝓦 X
              → csearchable' 𝓦 Y
              → csearchable' 𝓦 (+-ClosenessSpace X Y)
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
              → csearchable' 𝓦 X
              → csearchable' 𝓦 Y
              → csearchable' 𝓦 (×-ClosenessSpace X Y)
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
              → csearchable' 𝓦 Y
              → csearchable' 𝓦 (≃-ClosenessSpace Y e)
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
 → (δ : ℕ)
 → (x : X)
 → decidable-uc-predicate-with-mod 𝓦
     (ℕ→D-ClosenessSpace (finite-discrete-is-discrete f))
     (succ δ)
 → decidable-uc-predicate-with-mod 𝓦
     (ℕ→D-ClosenessSpace (finite-discrete-is-discrete f))
     δ
tail-predicate {𝓤} {𝓦} {X} f δ x ((p' , d') , ϕ') = (p , d) , ϕ
 where
  p : (ℕ → X) → Ω _
  p xs = p' (x ∶∶ xs)
  d : is-complemented (λ x₁ → p x₁ holds)
  d xs = d' (x ∶∶ xs)
  ϕ : p-ucontinuous-with-mod (ℕ→D-ClosenessSpace _) p δ
  ϕ x₁ x₂ Cδx₁x₂
   = ϕ' (x ∶∶ x₁) (x ∶∶ x₂)
       (∼ⁿ-to-C (finite-discrete-is-discrete f) _ _ (succ δ) γ)
   where
    γ : ((x ∶∶ x₁) ∼ⁿ (x ∶∶ x₂)) (succ δ)
    γ zero i<sδ = refl
    γ (succ i) i<sδ
     = C-to-∼ⁿ (finite-discrete-is-discrete f) _ _ δ Cδx₁x₂ i i<sδ

discrete-finite-seq-csearchable'
 : {X : 𝓤 ̇ }
 → X 
 → (f : finite-discrete X)
 → (δ : ℕ)
 → (((p , _) , _) : decidable-uc-predicate-with-mod 𝓦
     (ℕ→D-ClosenessSpace (finite-discrete-is-discrete f)) δ)
 → Σ xs₀ ꞉ (ℕ → X)
 , ((Σ xs ꞉ (ℕ → X) , p xs holds) → p xs₀ holds)

head-predicate
 : {X : 𝓤 ̇ }
 → X
 → (f : finite-discrete X)
 → (δ : ℕ)
 → decidable-uc-predicate-with-mod 𝓦
     (ℕ→D-ClosenessSpace (finite-discrete-is-discrete f)) (succ δ)
 → decidable-predicate 𝓦 X
head-predicate {𝓤} {𝓦} {X} x₀ f δ ((p , d) , ϕ)
 = p ∘ xs→ , d ∘ xs→
 where
  xs→ : X → (ℕ → X)
  xs→ x = x ∶∶ pr₁ (discrete-finite-seq-csearchable' x₀ f δ
                     (tail-predicate f δ x ((p , d) , ϕ)))
     
discrete-finite-seq-csearchable' x₀ f zero ((p , d) , ϕ)
 = (λ _ → x₀)
 , λ (y , py) → ϕ y (λ _ → x₀) (λ n ()) py
discrete-finite-seq-csearchable'
 {𝓤} {𝓦} {X} x₀ f (succ δ) ((p , d) , ϕ)
 = (x ∶∶ pr₁ (xs→ x)) , γ
 where
   pₜ→ = λ x → tail-predicate f δ x ((p , d) , ϕ)
   pₕ  = head-predicate x₀ f δ ((p , d) , ϕ)
   xs→ : (x : X) →  Σ xs₀ ꞉ (ℕ → X)
       , ((Σ xs ꞉ (ℕ → X) , (pr₁ ∘ pr₁) (pₜ→ x) xs holds)
       → (pr₁ ∘ pr₁) (pₜ→ x) xs₀ holds) 
   xs→ x = discrete-finite-seq-csearchable' x₀ f δ (pₜ→ x)
   x : X
   x = pr₁ (finite-discrete-searchable f x₀) pₕ
   γₕ : _
   γₕ = pr₂ (finite-discrete-searchable f x₀) pₕ
   γ : _
   γ (y , py)
    = γₕ (head y , pr₂ (xs→ (head y)) (tail y , transport (pr₁ ∘ p)
        (dfunext (fe _ _) ζ) py))
    where
     ζ : y ∼ (y 0 ∶∶ (λ x₁ → y (succ x₁)))
     ζ zero = refl
     ζ (succ i) = refl

discrete-finite-seq-csearchable
 : {X : 𝓤 ̇ }
 → X 
 → (f : finite-discrete X)
 → csearchable' 𝓦
     (ℕ→D-ClosenessSpace (finite-discrete-is-discrete f))
discrete-finite-seq-csearchable x₀ f ((p , d) , (δ , ϕ))
 = discrete-finite-seq-csearchable' x₀ f δ ((p , d) , ϕ)

-- Tychonoff

tail-predicate-tych
 : (T : ℕ → ClosenessSpace 𝓤)
 → (δ : ℕ)
 → (x : ⟨ T 0 ⟩)
 → decidable-uc-predicate-with-mod 𝓦
     (Π-ClosenessSpace T) (succ δ)
 → decidable-uc-predicate-with-mod 𝓦
     (Π-ClosenessSpace (T ∘ succ)) δ
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
 → ((n : ℕ) → csearchable' 𝓦 (T n))
 → (δ : ℕ)
 → (((p , _) , _) : decidable-uc-predicate-with-mod 𝓦
     (Π-ClosenessSpace T) δ)
 → Σ xs₀ ꞉ Π (⟨_⟩ ∘ T)
 , ((Σ xs ꞉ Π (⟨_⟩ ∘ T) , p xs holds) → p xs₀ holds)

head-predicate-tych
 : (T : ℕ → ClosenessSpace 𝓤)
 → ((n : ℕ) → csearchable' 𝓦 (T n))
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
    = γₕ (y 0 , pr₂ (xs→ (y 0)) (y ∘ succ , transport (pr₁ ∘ p)
        (dfunext (fe _ _) ζ) py))
    where
     ζ : y ∼ (y 0 :: (y ∘ succ))
     ζ zero = refl
     ζ (succ i) = refl

tychonoff : (T : ℕ → ClosenessSpace 𝓤)
          → ((n : ℕ) → csearchable' 𝓦 (T n))
          → csearchable' 𝓦 (Π-ClosenessSpace T)
tychonoff T S ((p , d) , δ , ϕ) = tychonoff' T S δ ((p , d) , ϕ)

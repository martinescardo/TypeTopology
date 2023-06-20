\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import CoNaturals.GenericConvergentSequence
 renaming (ℕ-to-ℕ∞ to _↑) hiding (max)
open import Notation.Order
open import Naturals.Order
open import TypeTopology.DiscreteAndSeparated
open import NotionsOfDecidability.Complemented
open import UF.Subsingletons
open import UF.FunExt
open import UF.Miscelanea
open import UF.Equiv

module TWA.Thesis.Chapter6.SignedDigitSearch (fe : FunExt) where

open import TWA.Thesis.Chapter2.FiniteDiscrete
open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter2.Vectors
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import TWA.Thesis.Chapter3.SearchableTypes fe
open import TWA.Thesis.Chapter4.ApproxOrder fe
open import TWA.Thesis.Chapter4.ApproxOrder-Examples fe
open import TWA.Thesis.Chapter4.GlobalOptimisation fe
open import TWA.Thesis.Chapter4.ConvergenceTheorems fe
open import TWA.Thesis.Chapter5.SignedDigit
open import TWA.Thesis.Chapter6.SequenceContinuity fe
open import TWA.Thesis.Chapter6.SignedDigitContinuity fe

𝟛ᴺ-lexicorder : 𝟛ᴺ → 𝟛ᴺ → 𝓤₀ ̇
𝟛ᴺ-lexicorder
 = discrete-lexicorder 𝟛-is-discrete (finite-strict-order 𝟛-finite)

𝟛-is-set : is-set 𝟛
𝟛-is-set = finite-is-set 𝟛-finite

_<₃_ : 𝟛 → 𝟛 → 𝓤₀ ̇
_<₃_ = finite-strict-order 𝟛-finite

<₃-is-strict : is-strict-order _<₃_
<₃-is-strict = finite-strict-order-is-strict-order 𝟛-finite

<₃-trichotomous : trichotomous _<₃_
<₃-trichotomous = finite-strict-order-trichotomous 𝟛-finite

𝟛ᴺ-lexicorder-is-preorder : is-preorder 𝟛ᴺ-lexicorder
𝟛ᴺ-lexicorder-is-preorder
 = discrete-lexicorder-is-preorder 𝟛-is-discrete
     𝟛-is-set _<₃_ <₃-is-strict

𝟛ᴺ-approx-lexicorder : 𝟛ᴺ → 𝟛ᴺ → ℕ → 𝓤₀ ̇ 
𝟛ᴺ-approx-lexicorder = discrete-approx-lexicorder 𝟛-is-discrete _<₃_

𝟛ᴺ-approx-lexicorder-is-approx-order
 : is-approx-order 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-lexicorder 𝟛ᴺ-approx-lexicorder
𝟛ᴺ-approx-lexicorder-is-approx-order
 = discrete-approx-lexicorder-is-approx-order
     𝟛-is-discrete 𝟛-is-set _<₃_ <₃-is-strict <₃-trichotomous

𝟛ᴺ-approx-lexicorder' : 𝟛ᴺ → 𝟛ᴺ → ℕ → Ω 𝓤₀
𝟛ᴺ-approx-lexicorder' α β n
 = 𝟛ᴺ-approx-lexicorder α β n
 , γ n α β
 where
  γ : (ϵ : ℕ) → (x y : 𝟛ᴺ) → is-prop (𝟛ᴺ-approx-lexicorder x y ϵ)
  γ ϵ = pr₂ (pr₂ (pr₁ (pr₁ (pr₂ 𝟛ᴺ-approx-lexicorder-is-approx-order) ϵ)))

𝟛ᴺ-totally-bounded : totally-bounded 𝟛ᴺ-ClosenessSpace 𝓤₀
𝟛ᴺ-totally-bounded = ℕ→F-is-totally-bounded 𝟛-finite O

𝟛ᴺ-global-opt¹ : (f : 𝟛ᴺ → 𝟛ᴺ)
               → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace f
               → (ϵ : ℕ)
               → (has ϵ global-minimal) 𝟛ᴺ-approx-lexicorder f
𝟛ᴺ-global-opt¹ f ϕ ϵ
 = global-opt 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     (repeat O) 𝟛ᴺ-lexicorder 𝟛ᴺ-approx-lexicorder
     𝟛ᴺ-approx-lexicorder-is-approx-order ϵ f ϕ
     𝟛ᴺ-totally-bounded

test : ℕ → 𝟛ᴺ
test ε = pr₁ (𝟛ᴺ-global-opt¹ neg neg-ucontinuous ε)

test2 : ℕ → 𝟛ᴺ
test2 ε = pr₁ (𝟛ᴺ-global-opt¹ (λ x → mul x x)
            mul-b-ucontinuous ε)

{-
test-eq : test 5 4 ＝ +1
test-eq = refl

test-eq-vec : test 5 ＝ Vec-to-Seq O (+1 ∷ (+1 ∷ (+1 ∷ (+1 ∷ [ +1 ]))))
test-eq-vec = refl
-}

𝟛ᴺ-csearchable : {𝓦 : Universe} → csearchable 𝓦 𝟛ᴺ-ClosenessSpace
𝟛ᴺ-csearchable
 = csearchable'→csearchable 𝟛ᴺ-ClosenessSpace
   (totally-bounded-csearchable 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-totally-bounded γ)
 where
  γ : (ϵ : ℕ) → pr₁ (pr₁ (𝟛ᴺ-totally-bounded ϵ)) -- TODO separate
  γ zero = []
  γ (succ ε) = O ∷ γ ε

𝟛ᴺ-csearchable₂ : {𝓦 : Universe} → csearchable 𝓦 𝟛ᴺ-ClosenessSpace
𝟛ᴺ-csearchable₂
 = csearchable'→csearchable 𝟛ᴺ-ClosenessSpace
   (discrete-finite-seq-csearchable O 𝟛-finite)

-- Move to ApproxOrder?
{-

approx-order-not-succ
 : (X : ClosenessSpace 𝓤)
 → (_≤_ : ⟨ X ⟩ → ⟨ X ⟩ → 𝓦 ̇ )
 → (_≤ⁿ_ : ⟨ X ⟩ → ⟨ X ⟩ → ℕ → 𝓦' ̇ )
 → is-approx-order X _≤_ _≤ⁿ_
 → (ε : ℕ) (x y : ⟨ X ⟩)
 → ¬ (x ≤ⁿ y) ε
 → ¬ (x ≤ⁿ y) (succ ε)
approx-order-not-succ X _≤_ _≤ⁿ_ (_ , _ , _ , c , a) ε x y ¬x≤ᵉy x≤ˢᵉy
 with C-decidable X (succ ε) x y 
... | inl  Csεxy = ¬x≤ᵉy (c ε x y (C-pred X ε x y Csεxy))
... | inr ¬Csεxy = ¬x≤ᵉy (pr₂ (a ε x y ¬Cεxy) x≤y)
 where
  x≤y : x ≤ y
  x≤y = pr₁ (a (succ ε) x y ¬Csεxy) x≤ˢᵉy
  ¬Cεxy : ¬ C X ε x y
  ¬Cεxy = ¬x≤ᵉy ∘ c ε x y
-}

discrete-approx-lexicorder-l-decidable
 : {F : 𝓤 ̇ } (f : finite-discrete F)
 → (ε : ℕ) (y : ℕ → F)
 → is-complemented (λ x → finite-approx-lexicorder f x y ε)
discrete-approx-lexicorder-l-decidable f ε y x
 = pr₁ (pr₂ (pr₂ (finite-approx-lexicorder-is-approx-order f))) ε x y

𝟛ᴺ-approx-lexicorder-l-decidable
 : (ε : ℕ) (y : 𝟛ᴺ)
 → is-complemented (λ x → 𝟛ᴺ-approx-lexicorder x y ε)
𝟛ᴺ-approx-lexicorder-l-decidable
 = discrete-approx-lexicorder-l-decidable 𝟛-finite

𝟛ᴺ-approx-lexicorder-l-ucontinuous
 : (ε : ℕ) (y : 𝟛ᴺ)
 → p-ucontinuous
     𝟛ᴺ-ClosenessSpace (λ x → 𝟛ᴺ-approx-lexicorder' x y ε)
𝟛ᴺ-approx-lexicorder-l-ucontinuous ε y = ε , γ
 where
  γ : (x₁ x₂ : 𝟛ᴺ) → C 𝟛ᴺ-ClosenessSpace ε x₁ x₂
    → 𝟛ᴺ-approx-lexicorder' x₁ y ε holds
    → 𝟛ᴺ-approx-lexicorder' x₂ y ε holds
  γ x₁ x₂ Cx₁x₂ (inl x₁∼ᵉy)
   = inl (λ i i<ε → C-to-∼ⁿ 𝟛-is-discrete x₁ x₂ ε Cx₁x₂ i i<ε ⁻¹
                  ∙ x₁∼ᵉy i i<ε)
  γ x₁ x₂ Cx₁x₂ (inr (i , i<ε , x₁∼ⁱy , x₁i<yi))
   = inr (i , i<ε
       , (λ j j<i → C-to-∼ⁿ 𝟛-is-discrete x₁ x₂ ε Cx₁x₂ j
                      (<-trans j i ε j<i i<ε) ⁻¹
                  ∙ x₁∼ⁱy j j<i)
       , transport (_<₃ y i)
           (C-to-∼ⁿ 𝟛-is-discrete x₁ x₂ ε Cx₁x₂ i i<ε) x₁i<yi)
  
-- TODO: Move to Chapter3.ClosenessSpaces
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

𝟛ᴺ-approx-lexicorder-l-f-ucontinuous
 : (ε : ℕ) (y : 𝟛ᴺ)
 → (f : 𝟛ᴺ → 𝟛ᴺ)
 → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace f
 → p-ucontinuous
     𝟛ᴺ-ClosenessSpace (λ x → 𝟛ᴺ-approx-lexicorder' (f x) y ε)
𝟛ᴺ-approx-lexicorder-l-f-ucontinuous ε ζ f ϕ
 = p-ucontinuous-comp 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
     f ϕ
     (λ α → 𝟛ᴺ-approx-lexicorder' α ζ ε)
     (𝟛ᴺ-approx-lexicorder-l-ucontinuous ε ζ)

open import TWA.Thesis.Chapter2.Sequences

1/4 : 𝟛ᴺ
1/4 = O ∶∶ (O ∶∶ (repeat +1))

question : 𝟛ᴺ → ℕ → Ω 𝓤₀
question x
 = 𝟛ᴺ-approx-lexicorder'
     (mid (neg x) (repeat O)) 1/4

question-decidable : (ε : ℕ)
                   → is-complemented (λ x → question x ε holds)
question-decidable ε x
 = 𝟛ᴺ-approx-lexicorder-l-decidable ε
     1/4 (mid (neg x) (repeat O))

question-ucontinuous : (ε : ℕ)
                     → p-ucontinuous 𝟛ᴺ-ClosenessSpace
                         (λ x → question x ε)
question-ucontinuous ε
 = 𝟛ᴺ-approx-lexicorder-l-f-ucontinuous ε 1/4
     (λ x → mid (neg x) (repeat O))
     (f-ucontinuous-comp
        𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
        neg (λ x → mid x (repeat O))
        neg-ucontinuous (mid-l-ucontinuous (repeat O)))

question* : ℕ → decidable-uc-predicate 𝓤₀ 𝟛ᴺ-ClosenessSpace
question* ε = ((λ x → question x ε)
            , (question-decidable ε))
            , question-ucontinuous ε

-- find x such that (-x/2) ≼ᵉ (1/4)
search-test : ℕ → 𝟛ᴺ
search-test ε = pr₁ 𝟛ᴺ-csearchable (question* ε)

search-test₂ : ℕ → 𝟛ᴺ
search-test₂ ε = pr₁ 𝟛ᴺ-csearchable₂ (question* ε) 

1/3 : 𝟛ᴺ
1/3 0 =  O
1/3 1 = +1
1/3 (succ (succ n)) = 1/3 n

ℕ∞-vec-min : (n : ℕ) → Vec ℕ∞ n → ℕ∞
ℕ∞-vec-min 0 [] = ∞
ℕ∞-vec-min (succ n) (x ∷ v) = min x (ℕ∞-vec-min n v)

Vec-≃ : {X : 𝓤 ̇ } → (n : ℕ) → Vec X (succ n) ≃ X × Vec X n
Vec-≃ {𝓤} {X} n = qinveq g (h , η , μ)
 where
  g : Vec X (succ n) → X × Vec X n
  g (x ∷ v) = x , v
  h : X × Vec X n → Vec X (succ n)
  h (x , v) = x ∷ v
  η : (λ x → h (g x)) ∼ (λ x → x)
  η (x ∷ v) = refl
  μ : (λ x → g (h x)) ∼ (λ x → x)
  μ (x , v) = refl

open import TWA.Closeness fe hiding (is-ultra;is-closeness)

Vec-ClosenessSpace : (X : ClosenessSpace 𝓤)
                   → (n : ℕ)
                   → ClosenessSpace 𝓤

Vec-clospace : (X : ClosenessSpace 𝓤)
             → (n : ℕ)
             → is-closeness-space (Vec ⟨ X ⟩ n)

Vec-ClosenessSpace X n = (Vec ⟨ X ⟩ n) , Vec-clospace X n

Vec-clospace X 0
 = (λ _ _ → ∞) , e , i , s , u
 where
  e : indistinguishable-are-equal (λ _ _ → ∞)
  e [] [] _ = refl
  i : self-indistinguishable (λ _ _ → ∞)
  i [] = refl
  s : is-symmetric (λ _ _ → ∞)
  s [] [] = refl
  u : is-ultra (λ _ _ → ∞)
  u [] [] [] _ _ = refl
Vec-clospace X (succ n)
 = pr₂ (≃-ClosenessSpace (Vec ⟨ X ⟩ (succ n))
     (×-ClosenessSpace X (Vec-ClosenessSpace X n))
     (Vec-≃ n))

FunPoints-clofun : (X : 𝓤 ̇ ) (Y : ClosenessSpace 𝓥)
                 → {n : ℕ}
                 → Vec X n
                 → ((X → ⟨ Y ⟩) → (X → ⟨ Y ⟩) → ℕ∞)
FunPoints-clofun X Y {n} v f g
 = pr₁ (Vec-clospace Y n) (vec-map f v) (vec-map g v)

FunPoints-clofun-is-psclofun
 : (X : 𝓤 ̇ ) (Y : ClosenessSpace 𝓥)
 → {n : ℕ}
 → (v : Vec X n)
 → is-pseudocloseness (FunPoints-clofun X Y v)
FunPoints-clofun-is-psclofun X Y {n} v
 = (λ f → pr₁ (pr₂ γ) (vec-map f v))
 , (λ f g → pr₁ (pr₂ (pr₂ γ)) (vec-map f v) (vec-map g v))
 , (λ f g h → pr₂ (pr₂ (pr₂ γ)) (vec-map f v) (vec-map g v) (vec-map h v))
 where
  γ : is-closeness (pr₁ (Vec-clospace Y n))
  γ = pr₂ (Vec-clospace Y n)

FunPoints-PseudoClosenessSpace : (X : 𝓤 ̇ ) (Y : ClosenessSpace 𝓥)
                               → (f : X → ⟨ Y ⟩)
                               → {n : ℕ}
                               → Vec X n
                               → PseudoClosenessSpace (𝓤 ⊔ 𝓥)
FunPoints-PseudoClosenessSpace X Y f v
 = (X → ⟨ Y ⟩)
 , FunPoints-clofun X Y v
 , FunPoints-clofun-is-psclofun X Y v

open import MLTT.Two-Properties

close-to-close' : (X : ClosenessSpace 𝓤)
                → (Y : ClosenessSpace 𝓥)
                → (Z : ClosenessSpace 𝓦)
                → (f : ⟨ X ⟩ → ⟨ Y ⟩ → ⟨ Z ⟩)
                → (Ω' : ⟨ Y ⟩ → ⟨ Z ⟩)
                → {n : ℕ} (v : Vec ⟨ Y ⟩ n)
                → f-ucontinuous (×-ClosenessSpace X Y) Z (uncurry f)
                → f-ucontinuous' (ι X)
                    (FunPoints-PseudoClosenessSpace ⟨ Y ⟩ Z Ω' v) f
close-to-close' X Y Z f Ω' [] ϕ ε = 0 , λ _ _ _ _ _ → refl
close-to-close' X Y Z f Ω' v@(y ∷ ys) ϕ ε = δ , γ
 where
  IH = close-to-close' X Y Z f Ω' ys ϕ ε
  δ δ₁ δ₂ : ℕ
  δ₁ = pr₁ (ϕ ε)
  δ₂ = pr₁ IH
  δ  = max δ₁ δ₂
  γ : (x₁ x₂ : ⟨ X ⟩) → C X δ x₁ x₂
    → C' (FunPoints-PseudoClosenessSpace ⟨ Y ⟩ Z Ω' v) ε (f x₁) (f x₂)
  γ x₁ x₂ Cδx₁x₂ n z
   = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
       (pr₂ (ϕ ε) (x₁ , y) (x₂ , y)
         (C-prev (×-ClosenessSpace X Y) δ δ₁ (max-≤-upper-bound δ₁ δ₂)
           (x₁ , y) (x₂ , y)
           (×-C-combine X Y x₁ x₂ y y δ Cδx₁x₂ (C-refl Y δ y))) n z)
       (pr₂ IH x₁ x₂
         (C-prev X δ δ₂ (max-≤-upper-bound' δ₂ δ₁) x₁ x₂ Cδx₁x₂) n z)
  

-- check if below needed, or if above is enough
close-to-close : (X : ClosenessSpace 𝓤)
               → (Y : ClosenessSpace 𝓥)
               → (Z : ClosenessSpace 𝓦)
               → (f : ⟨ X ⟩ → ⟨ Y ⟩ → ⟨ Z ⟩)
               → {n : ℕ} (v : Vec ⟨ Y ⟩ n)
               → ((x : ⟨ X ⟩) → f-ucontinuous Y Z (f x))
               → ((y : ⟨ Y ⟩) → f-ucontinuous X Z (λ x → f x y))
               → (x : ⟨ X ⟩) → f-ucontinuous' (ι X)
                   (FunPoints-PseudoClosenessSpace ⟨ Y ⟩ Z (f x) v)
                   f
close-to-close X Y Z f [] _ _ k ε = 0 , λ _ _ _ _ _ → refl
close-to-close X Y Z f v@(y ∷ ys) ϕˣ ϕʸ k ε = δ , γ
 where
  IH = close-to-close X Y Z f ys ϕˣ ϕʸ k ε
  δ δ₁ δ₂ : ℕ
  δ₁ = pr₁ (ϕʸ y ε)
  δ₂ = pr₁ IH
  δ = max δ₁ δ₂
  γ : (x₁ x₂ : ⟨ X ⟩) → C X δ x₁ x₂
    → C' (FunPoints-PseudoClosenessSpace ⟨ Y ⟩ Z (f k) v) ε (f x₁) (f x₂)
  γ x₁ x₂ Cx₁x₂ n z
   = Lemma[a＝₁→b＝₁→min𝟚ab＝₁]
       (pr₂ (ϕʸ y ε) x₁ x₂
         (C-prev X δ δ₁ (max-≤-upper-bound δ₁ δ₂) x₁ x₂ Cx₁x₂) n z)
       (pr₂ IH x₁ x₂
         (C-prev X δ δ₂ (max-≤-upper-bound' δ₂ δ₁) x₁ x₂ Cx₁x₂) n z)
    
perfect-regression-test : {n : ℕ} → ℕ → Vec 𝟛ᴺ n → (𝟛ᴺ → 𝟛ᴺ)
perfect-regression-test {n} ε v
 = ω
 where
  M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
  M y = λ x → mid y (mul x x)
  k : 𝟛ᴺ
  k = 1/3
  Ω' = M k -- Ω(x) ≔ (1/3 + x²) / 2
  𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
   = FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v
  ϕᴹ' : (y : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                     (λ x → mid y (mul x x))
  ϕᴹ' y = f-ucontinuous-comp
            𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
            (λ x → mul x x) (mid y)
            mul-b-ucontinuous (mid-r-ucontinuous y)
  ϕᴹ'' : (x : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                     (λ y → mid y (mul x x))
  ϕᴹ'' x = mid-l-ucontinuous (mul x x)
  ϕᴹ : f-ucontinuous' (ι 𝟛ᴺ-ClosenessSpace)
         (FunPoints-PseudoClosenessSpace ⟨ 𝟛ᴺ-ClosenessSpace ⟩
           𝟛ᴺ-ClosenessSpace Ω' v) M 
  ϕᴹ = close-to-close
         𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         M v ϕᴹ' ϕᴹ'' k
  𝓔S : csearchable 𝓤₀ 𝟛ᴺ-ClosenessSpace
  𝓔S = 𝟛ᴺ-csearchable {𝓤₀}
  reg : regressor
          𝟛ᴺ-ClosenessSpace
          (FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v)
  reg = p-regressor 𝟛ᴺ-ClosenessSpace
          (FunPoints-PseudoClosenessSpace 𝟛ᴺ
            𝟛ᴺ-ClosenessSpace Ω' v)
          𝟛ᴺ-csearchable ε
  ω = M (reg M ϕᴹ Ω')

perfect-regression-test-param-only : {n : ℕ} → ℕ → Vec 𝟛ᴺ n → 𝟛ᴺ
perfect-regression-test-param-only {n} ε v
 = reg M ϕᴹ Ω'
 where
  M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
  M y = λ x → mid y (mul x x)
  k : 𝟛ᴺ
  k = 1/3
  Ω' = M k -- Ω(x) ≔ (1/3 + x²) / 2
  𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
   = FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v
  ϕᴹ' : (y : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                     (λ x → mid y (mul x x))
  ϕᴹ' y = f-ucontinuous-comp
            𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
            (λ x → mul x x) (mid y)
            mul-b-ucontinuous (mid-r-ucontinuous y)
  ϕᴹ'' : (x : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                     (λ y → mid y (mul x x))
  ϕᴹ'' x = mid-l-ucontinuous (mul x x)
  ϕᴹ : f-ucontinuous' (ι 𝟛ᴺ-ClosenessSpace)
         (FunPoints-PseudoClosenessSpace ⟨ 𝟛ᴺ-ClosenessSpace ⟩
           𝟛ᴺ-ClosenessSpace Ω' v) M 
  ϕᴹ = close-to-close
         𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         M v ϕᴹ' ϕᴹ'' k
  𝓔S : csearchable 𝓤₀ 𝟛ᴺ-ClosenessSpace
  𝓔S = 𝟛ᴺ-csearchable {𝓤₀}
  reg : regressor
          𝟛ᴺ-ClosenessSpace
          (FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v)
  reg = p-regressor 𝟛ᴺ-ClosenessSpace
          (FunPoints-PseudoClosenessSpace 𝟛ᴺ
            𝟛ᴺ-ClosenessSpace Ω' v)
          𝟛ᴺ-csearchable ε

-- Move to Chapter 3
id-ucontinuous : (X : ClosenessSpace 𝓤)
               → f-ucontinuous X X id
id-ucontinuous X ε = ε , λ _ _ → id

simpler-perfect-regression-test : {n : ℕ} → ℕ → Vec 𝟛ᴺ n → (𝟛ᴺ → 𝟛ᴺ)
simpler-perfect-regression-test {n} ε v
 = M (reg M ϕᴹ Ω')
 where
  M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
  M = mid
  k : 𝟛ᴺ
  k = 1/3
  Ω' = M k -- Ω(x) ≔ (1/3 + x) / 2
  𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
   = FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v
  ϕᴹ' : (y : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                     (λ x → mid y x)
  ϕᴹ' y = f-ucontinuous-comp
            𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
            id (mid y)
            (id-ucontinuous 𝟛ᴺ-ClosenessSpace) (mid-r-ucontinuous y)
  ϕᴹ'' : (x : 𝟛ᴺ) → f-ucontinuous 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
                     (λ y → mid y x)
  ϕᴹ'' x = mid-l-ucontinuous x
  ϕᴹ : f-ucontinuous' (ι 𝟛ᴺ-ClosenessSpace)
         (FunPoints-PseudoClosenessSpace ⟨ 𝟛ᴺ-ClosenessSpace ⟩
           𝟛ᴺ-ClosenessSpace Ω' v) M 
  ϕᴹ = close-to-close
         𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         M v ϕᴹ' ϕᴹ'' k
  𝓔S : csearchable 𝓤₀ 𝟛ᴺ-ClosenessSpace
  𝓔S = 𝟛ᴺ-csearchable {𝓤₀}
  reg : regressor
          𝟛ᴺ-ClosenessSpace
          (FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v)
  reg = p-regressor 𝟛ᴺ-ClosenessSpace
          (FunPoints-PseudoClosenessSpace 𝟛ᴺ
            𝟛ᴺ-ClosenessSpace Ω' v)
          𝟛ᴺ-csearchable ε

endpoints : Vec 𝟛ᴺ 3
endpoints = repeat −1 ∷ ((repeat O) ∷ [ (repeat +1) ])

preg-test-eq : ℕ → (𝟛ᴺ → 𝟛ᴺ)
preg-test-eq n = simpler-perfect-regression-test n endpoints

allofthemare : (Y : PseudoClosenessSpace 𝓥)
-- Replace condition in Theorem 4.2.8 with this
             → (Ω : ⟪ Y ⟫)
             → let c = pr₁ (pr₂ Y) in
               f-ucontinuous' Y (ι ℕ∞-ClosenessSpace) (c Ω)
allofthemare Y Ω ϵ = ϵ , γ
 where
  c = pr₁ (pr₂ Y)
  c-sym = pr₁ (pr₂ (pr₂ (pr₂ Y)))
  c-ult = pr₂ (pr₂ (pr₂ (pr₂ Y)))
  γ : (y₁ y₂ : ⟪ Y ⟫)
    → C' Y ϵ y₁ y₂
    → C' (ι ℕ∞-ClosenessSpace) ϵ (c Ω y₁) (c Ω y₂)
  γ y₁ y₂ Cϵy₁y₂ n n⊏ϵ
   = decidable-𝟚₁ (discrete-decidable-seq _ _ _ (succ n))
       λ k k<sn → CΩ-eq k (<-≤-trans k (succ n) ϵ k<sn (⊏-gives-< n ϵ n⊏ϵ))
   where
    CΩ-eq : (pr₁ (c Ω y₁) ∼ⁿ pr₁ (c Ω y₂)) ϵ
    CΩ-eq n n<ϵ with 𝟚-possibilities (pr₁ (c Ω y₁) n)
                   | 𝟚-possibilities (pr₁ (c Ω y₂) n)
    ... | inl cΩy₁＝₀ | inl cΩy₂＝₀ = cΩy₁＝₀ ∙ cΩy₂＝₀ ⁻¹
    ... | inl cΩy₁＝₀ | inr cΩy₂＝₁
     = 𝟘-elim (zero-is-not-one
     (cΩy₁＝₀ ⁻¹
     ∙ c-ult Ω y₂ y₁ n
         (Lemma[a＝₁→b＝₁→min𝟚ab＝₁] cΩy₂＝₁
           (ap (λ - → pr₁ - n) (c-sym y₂ y₁)
            ∙ Cϵy₁y₂ n (<-gives-⊏ n ϵ n<ϵ)))))
    ... | inr cΩy₁＝₁ | inl cΩy₂＝₀
     = 𝟘-elim (zero-is-not-one
     (cΩy₂＝₀ ⁻¹
     ∙ c-ult Ω y₁ y₂ n
         (Lemma[a＝₁→b＝₁→min𝟚ab＝₁] cΩy₁＝₁
           (Cϵy₁y₂ n (<-gives-⊏ n ϵ n<ϵ))))) 
    ... | inr cΩy₁＝₁ | inr cΩy₂＝₁ = cΩy₁＝₁ ∙ cΩy₂＝₁ ⁻¹
    

{-λ y₁ y₂ Cϵy₁y₂ n n⊏ε
 → decidable-𝟚₁ (discrete-decidable-seq 𝟚-is-discrete _ _ (succ n))
     λ i i<sn → γ y₁ y₂ Cϵy₁y₂ i
       (<-≤-trans i (succ n) ϵ i<sn (⊏-gives-< n ϵ n⊏ε))
 where
  c = pr₁ (pr₂ Y)
  γ : (y₁ y₂ : ⟪ Y ⟫) → C' Y ϵ y₁ y₂ → (pr₁ (c Ω y₁) ∼ⁿ pr₁ (c Ω y₂)) ϵ
  γ y₁ y₂ Cϵy₁y₂ n n<ϵ with C'-decidable Y ϵ Ω y₁
  ... | inl CϵΩy₁ = CϵΩy₁ n (<-gives-⊏ n ϵ n<ϵ) ∙ {!!}
  ... | inr x = {!!} -}

regression-opt : {n : ℕ} → ℕ → Vec 𝟛ᴺ n → 𝟛ᴺ
regression-opt ε v -- WORK ON THIS FIRST TOMORROW
 = pr₁ (optimisation-convergence 𝟛ᴺ-ClosenessSpace
             𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace (repeat O) 𝟛ᴺ-totally-bounded
             M Ω' ϕᴹ ϕᶜ ε)
 where
  M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
  M y x = mid (neg y) x
  Ω' = mid (repeat O) -- Ω(x) ≔ (1/3 + x) / 2
  𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
   = FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v
  ϕᴹ' : f-ucontinuous
          (×-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace)
          𝟛ᴺ-ClosenessSpace (uncurry (λ y x → mid (neg y) x))
  ϕᴹ' = seq-f-ucontinuous²-to-closeness
          𝟛-is-discrete 𝟛-is-discrete 𝟛-is-discrete
          (λ y x → mid (neg y) x)
          (seq-f-ucontinuous²¹-comp-left mid neg
            mid-ucontinuous' neg-ucontinuous')
  ϕᴹ : f-ucontinuous' (ι 𝟛ᴺ-ClosenessSpace) 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
         (λ y x → mid (neg y) x)
  ϕᴹ = close-to-close'
         𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         (λ y x → mid (neg y) x) Ω' v ϕᴹ'
  ϕᶜ : f-ucontinuous' 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace (ι ℕ∞-ClosenessSpace)
         (pr₁ (pr₂ 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace) Ω')
  ϕᶜ = allofthemare 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace Ω'

regression-opt' : {n : ℕ} → ℕ → Vec 𝟛ᴺ n → 𝟛ᴺ
regression-opt' ε v
 = pr₁ (optimisation-convergence 𝟛ᴺ-ClosenessSpace
             𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace (repeat O) 𝟛ᴺ-totally-bounded
             M Ω' ϕᴹ ϕᶜ ε)
 where
  M : 𝟛ᴺ → (𝟛ᴺ → 𝟛ᴺ)
  M y x = mid y x
  Ω' = mid (repeat O) -- Ω(x) ≔ (1/3 + x) / 2
  𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
   = FunPoints-PseudoClosenessSpace 𝟛ᴺ 𝟛ᴺ-ClosenessSpace Ω' v
  ϕᴹ' : f-ucontinuous
          (×-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace)
          𝟛ᴺ-ClosenessSpace (uncurry (λ y x → mid y x))
  ϕᴹ' = seq-f-ucontinuous²-to-closeness
          𝟛-is-discrete 𝟛-is-discrete 𝟛-is-discrete
          (λ y x → mid y x)
          mid-ucontinuous' {-
          (seq-f-ucontinuous²¹-comp-left mid neg
            mid-ucontinuous' neg-ucontinuous') -}
  ϕᴹ : f-ucontinuous' (ι 𝟛ᴺ-ClosenessSpace) 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace
         (λ y x → mid y x)
  ϕᴹ = close-to-close'
         𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace 𝟛ᴺ-ClosenessSpace
         (λ y x → mid y x) Ω' v ϕᴹ'
  ϕᶜ : f-ucontinuous' 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace (ι ℕ∞-ClosenessSpace)
         (pr₁ (pr₂ 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace) Ω')
  ϕᶜ = allofthemare 𝟛ᴺ→𝟛ᴺ-PseudoClosenessSpace Ω'

regression-opt-example : ℕ → 𝟛ᴺ
regression-opt-example n = regression-opt' n endpoints 

run = Seq-to-Vec






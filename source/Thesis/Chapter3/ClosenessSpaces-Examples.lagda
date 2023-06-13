\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import CoNaturals.GenericConvergentSequence
 renaming (ℕ-to-ℕ∞ to _↑)
open import Notation.Order
open import Naturals.Order
open import Naturals.Properties
open import NotionsOfDecidability.Complemented
open import TypeTopology.DiscreteAndSeparated
open import UF.FunExt
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient
open import UF.Miscelanea
open import UF.Embeddings
open import MLTT.Two-Properties

module Thesis.Chapter3.ClosenessSpaces-Examples (fe : FunExt) where

open import Thesis.Chapter2.FiniteDiscrete
open import Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Closeness fe hiding (is-ultra; is-closeness)

-- [ TODO: Move to SequenceTypes file ]
_∼ⁿ_ : {X : 𝓤 ̇ } → (ℕ → X) → (ℕ → X) → ℕ → 𝓤 ̇
(α ∼ⁿ β) n = (i : ℕ) → i < n → α i ＝ β i

discrete-decidable-seq
 : {X : 𝓤 ̇ } → is-discrete X
 → (α β : ℕ → X) → (n : ℕ) → is-decidable ((α ∼ⁿ β) n)
discrete-decidable-seq d α β 0 = inl (λ _ ())
discrete-decidable-seq d α β (succ n)
 = Cases (discrete-decidable-seq d α β n) γ₁ (inr ∘ γ₂)
 where
   γ₁ : (α ∼ⁿ β) n → is-decidable ((α ∼ⁿ β) (succ n))
   γ₁ α∼ⁿβ = Cases (d (α n) (β n)) (inl ∘ γ₁₁) (inr ∘ γ₁₂)
    where
      γ₁₁ :    α n ＝ β n →     (α ∼ⁿ β) (succ n)
      γ₁₁ e k k<sn = Cases (≤-split (succ k) n k<sn)
                       (λ k<n → α∼ⁿβ k k<n)
                       (λ sk=sn → transport (λ - → α - ＝ β -)
                         (succ-lc sk=sn ⁻¹) e)
      γ₁₂ : ¬ (α n ＝ β n) → ¬ ((α ∼ⁿ β) (succ n))
      γ₁₂ g α∼ˢⁿβ = g (α∼ˢⁿβ n (<-succ n))
   γ₂ : ¬ ((α ∼ⁿ β) n) → ¬ ((α ∼ⁿ β) (succ n))
   γ₂ f = f
        ∘ λ α∼ˢⁿβ k k<n → α∼ˢⁿβ k (<-trans k n (succ n) k<n (<-succ n))

decidable-𝟚 : {X : 𝓤 ̇ } → is-decidable X → 𝟚
decidable-𝟚 (inl _) = ₁
decidable-𝟚 (inr _) = ₀

decidable-𝟚₁ : {X : 𝓤 ̇ } → (d : is-decidable X)
             → X → decidable-𝟚 d ＝ ₁
decidable-𝟚₁ (inl  x) _ = refl
decidable-𝟚₁ (inr ¬x) x = 𝟘-elim (¬x x)

decidable-𝟚₀ : {X : 𝓤 ̇ } → (d : is-decidable X)
             → ¬ X → decidable-𝟚 d ＝ ₀
decidable-𝟚₀ (inl  x) ¬x = 𝟘-elim (¬x x)
decidable-𝟚₀ (inr ¬x)  _ = refl

𝟚-decidable₁ : {X : 𝓤 ̇ } → (d : is-decidable X)
             → decidable-𝟚 d ＝ ₁ → X
𝟚-decidable₁ d e with d
... | inl  x = x
... | inr ¬x = 𝟘-elim (zero-is-not-one e)

𝟚-decidable₀ : {X : 𝓤 ̇ } → (d : is-decidable X)
             → decidable-𝟚 d ＝ ₀ → ¬ X
𝟚-decidable₀ d e with d
... | inl  x = 𝟘-elim (zero-is-not-one (e ⁻¹))
... | inr ¬x = ¬x

decidable-seq-𝟚 : {X : ℕ → 𝓤 ̇ } → is-complemented X → (ℕ → 𝟚)
decidable-seq-𝟚 d n = decidable-𝟚 (d (succ n))

discrete-seq-clofun'
 : {X : 𝓤 ̇ } → is-discrete X → (ℕ → X) → (ℕ → X) → (ℕ → 𝟚)
discrete-seq-clofun' d α β
 = decidable-seq-𝟚 (discrete-decidable-seq d α β)

discrete-seq-clofun'-e
 : {X : 𝓤 ̇ } → (d : is-discrete X) → (α β : ℕ → X)
 → ((n : ℕ) → discrete-seq-clofun' d α β n ＝ ₁)
 → α ＝ β
discrete-seq-clofun'-e d α β f
 = dfunext (fe _ _)
     (λ n → 𝟚-decidable₁ (discrete-decidable-seq d α β (succ n))
              (f n) n (<-succ n))

discrete-seq-clofun'-i
 : {X : 𝓤 ̇ } → (d : is-discrete X) → (α : ℕ → X)
 → (n : ℕ) → discrete-seq-clofun' d α α n ＝ ₁
discrete-seq-clofun'-i d α n
 = decidable-𝟚₁ (discrete-decidable-seq d α α (succ n)) (λ _ _ → refl)

discrete-seq-clofun'-s
 : {X : 𝓤 ̇ } → (d : is-discrete X) → (α β : ℕ → X)
 → (n : ℕ)
 → discrete-seq-clofun' d α β n ＝ discrete-seq-clofun' d β α n
discrete-seq-clofun'-s d α β n
 with discrete-decidable-seq d α β (succ n)
... | inl  α∼ⁿβ
 = decidable-𝟚₁ (discrete-decidable-seq d β α (succ n))
     (λ i i<n → α∼ⁿβ i i<n ⁻¹) ⁻¹
... | inr ¬α∼ⁿβ
 = decidable-𝟚₀ (discrete-decidable-seq d β α (succ n))
     (λ α∼ⁿβ → ¬α∼ⁿβ (λ i i<n → α∼ⁿβ i i<n ⁻¹)) ⁻¹

discrete-seq-clofun'-u
 : {X : 𝓤 ̇ } → (d : is-discrete X) → (α β ζ : ℕ → X)
 → (n : ℕ)
 → min𝟚 (discrete-seq-clofun' d α β n)
        (discrete-seq-clofun' d β ζ n) ＝ ₁
 → discrete-seq-clofun' d α ζ n ＝ ₁
discrete-seq-clofun'-u d α β ζ n minₙ=1
 with discrete-decidable-seq d α β (succ n)
    | discrete-decidable-seq d β ζ (succ n)
    | discrete-decidable-seq d α ζ (succ n)
... |        _ |        _ | inl     _ = refl
... | inl α∼ⁿβ | inl β∼ⁿζ | inr ¬α∼ⁿζ
 = 𝟘-elim (¬α∼ⁿζ (λ i i<n → α∼ⁿβ i i<n ∙ β∼ⁿζ i i<n))

discrete-decidable-seq-𝟚-decreasing
 : {X : 𝓤 ̇ } → (d : is-discrete X) → (α β : ℕ → X)
 → is-decreasing (discrete-seq-clofun' d α β)
discrete-decidable-seq-𝟚-decreasing d α β n
 with discrete-decidable-seq d α β (succ n)
    | discrete-decidable-seq d α β (succ (succ n))
... | inl     _ |          _ = ₁-top
... | inr ¬α∼ⁿβ | inl  α∼ˢⁿβ
 = ¬α∼ⁿβ (λ i i≤n → α∼ˢⁿβ i (≤-trans i n (succ n)
                      i≤n (≤-succ n)))
... | inr     _ | inr      _ = ⋆

discrete-seq-clofun
 : {X : 𝓤 ̇ } → is-discrete X → (ℕ → X) → (ℕ → X) → ℕ∞
discrete-seq-clofun d α β
 = discrete-seq-clofun' d α β
 , discrete-decidable-seq-𝟚-decreasing d α β

discrete-seq-clofun-e
 : {X : 𝓤 ̇ } → (d : is-discrete X)
 → indistinguishable-are-equal (discrete-seq-clofun d)
discrete-seq-clofun-e d α β cαβ=∞
 = discrete-seq-clofun'-e d α β (λ n → ap (λ - → pr₁ - n) cαβ=∞) 
     
discrete-seq-clofun-i : {X : 𝓤 ̇ } → (d : is-discrete X)
                      → self-indistinguishable (discrete-seq-clofun d)
discrete-seq-clofun-i d α
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _) (discrete-seq-clofun'-i d α))

discrete-seq-clofun-s : {X : 𝓤 ̇ } → (d : is-discrete X)
                      → is-symmetric (discrete-seq-clofun d)
discrete-seq-clofun-s d α β
 = to-subtype-＝ (being-decreasing-is-prop (fe _ _))
     (dfunext (fe _ _) (discrete-seq-clofun'-s d α β))

discrete-seq-clofun-u : {X : 𝓤 ̇ } → (d : is-discrete X)
                      → is-ultra (discrete-seq-clofun d)
discrete-seq-clofun-u = discrete-seq-clofun'-u

discrete-seq-clofun-c : {X : 𝓤 ̇ } → (d : is-discrete X)
                      → is-closeness (discrete-seq-clofun d)
discrete-seq-clofun-c d = discrete-seq-clofun-e d
                        , discrete-seq-clofun-i d
                        , discrete-seq-clofun-s d
                        , discrete-seq-clofun-u d

ℕ→D-clofun : {X : 𝓤 ̇ } → (d : is-discrete X)
           → Σ c ꞉ ((ℕ → X) → (ℕ → X) → ℕ∞)
           , is-closeness c
ℕ→D-clofun d = discrete-seq-clofun d
             , discrete-seq-clofun-c d

ℕ→D-ClosenessSpace : {X : 𝓤 ̇ } → (d : is-discrete X)
                   → ClosenessSpace 𝓤
ℕ→D-ClosenessSpace {𝓤} {X} d = (ℕ → X) , ℕ→D-clofun d

Σ-clofun : {X : 𝓤 ̇ } (P : X → 𝓥 ̇ )
         → ((x : X) → is-prop (P x))
         → Σ cx ꞉ (X → X → ℕ∞) , is-closeness cx
         → Σ c ꞉ (Σ P → Σ P → ℕ∞) , is-closeness c
Σ-clofun {𝓤} {𝓥} {X} P p (cx , ex , ix , sx , ux) = c , e , i , s , u
 where
  c : Σ P → Σ P → ℕ∞
  c (x , _) (y , _) = cx x y
  e : indistinguishable-are-equal c
  e (x , _) (y , _) cxy=∞ = to-subtype-＝ p (ex x y cxy=∞)
  i : self-indistinguishable c
  i (x , _) = ix x
  s : is-symmetric c
  s (x , _) (y , _) = sx x y
  u : is-ultra c
  u (x , _) (y , _) (z , _) = ux x y z

Σ-ClosenessSpace : (X : ClosenessSpace 𝓤)
                 → (P : ⟨ X ⟩ → 𝓥 ̇ ) → ((x : ⟨ X ⟩) → is-prop (P x))
                 → ClosenessSpace (𝓤 ⊔ 𝓥)
Σ-ClosenessSpace {𝓤} {𝓥} (X , cx) P p = Σ P  , Σ-clofun P p cx

↪-clofun : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X ↪ Y)
         → Σ cy ꞉ (Y → Y → ℕ∞) , is-closeness cy
         → Σ c  ꞉ (X → X → ℕ∞) , is-closeness c
↪-clofun {𝓤} {𝓥} {X} {Y} (f , η) (cy , ey , iy , sy , uy)
 = c , e , i , s , u
 where
  c : X → X → ℕ∞
  c x y = cy (f x) (f y)
  e : indistinguishable-are-equal c
  e x y cxy＝∞
   = ap pr₁ (η (f y) (x , ey (f x) (f y) cxy＝∞) (y , refl))
  i : self-indistinguishable c
  i x = iy (f x)
  s : is-symmetric c
  s x y = sy (f x) (f y)
  u : is-ultra c
  u x y z = uy (f x) (f y) (f z)

ℕ→𝟚-ClosenessSpace : ClosenessSpace 𝓤₀
ℕ→𝟚-ClosenessSpace = ℕ→D-ClosenessSpace 𝟚-is-discrete

ℕ∞-ClosenessSpace : ClosenessSpace 𝓤₀
ℕ∞-ClosenessSpace = Σ-ClosenessSpace ℕ→𝟚-ClosenessSpace is-decreasing
                     (being-decreasing-is-prop (fe _ _))

open import Thesis.Chapter5.PLDIPrelude

Vec-to-Seq : {X : 𝓤 ̇ } {n : ℕ} → X → Vec X n → (ℕ → X)
Vec-to-Seq x₀ [] n = x₀
Vec-to-Seq x₀ (x ∷ xs) 0 = x
Vec-to-Seq x₀ (x ∷ xs) (succ n) = Vec-to-Seq x₀ xs n

open import UF.Equiv
open import Naturals.Addition
open import Naturals.Multiplication
open import Fin.Type
open import Fin.ArithmeticViaEquivalence
open import UF.EquivalenceExamples

-- TODO: Maybe change to use Martin's Fin type
𝔽-≃ : {n : ℕ} → 𝔽 n ≃ Fin n
𝔽-≃ {n} = qinveq g (h , η , μ)
 where
  g : {n : ℕ} → 𝔽 n → Fin n
  g {succ n} (inl ⋆) = 𝟎
  g {succ n} (inr x) = suc (g x)
  h : {n : ℕ} → Fin n → 𝔽 n
  h {succ n} 𝟎       = inl ⋆
  h {succ n} (suc x) = inr (h x)
  η : {n : ℕ} → (λ (x : 𝔽 n) → h (g x)) ∼ (λ x → x)
  η {succ n} (inl ⋆) = refl
  η {succ n} (inr x) = ap inr (η x)
  μ : {n : ℕ} → (λ (x : Fin n) → g (h x)) ∼ (λ x → x)
  μ {succ n} 𝟎       = refl
  μ {succ n} (suc x) = ap suc (μ x)
  
Vec-finite-discrete : {F : 𝓤 ̇ } (ϵ : ℕ) → finite-discrete F
                    → finite-discrete (Vec F ϵ)
Vec-finite-discrete {𝓤} {F} zero (n , f) = 1 , qinveq g (h , η , μ)
 where
  g : 𝔽 1 → Vec F zero
  g _ = []
  h : Vec F zero → 𝔽 1
  h _ = inl ⋆
  η : (λ x → h (g x)) ∼ (λ x → x)
  η (inl ⋆) = refl
  μ : (λ x → g (h x)) ∼ (λ x → x)
  μ [] = refl
Vec-finite-discrete {𝓤} {F} (succ ϵ) (n , f)
 = n ×' m , (𝔽-≃
          ● Fin×homo n m
          ● ×-cong (≃-sym 𝔽-≃) (≃-sym 𝔽-≃)
          ● ×-cong f (pr₂ IH)
          ● qinveq g (h , η , μ))
 where
  IH : finite-discrete (Vec F ϵ)
  IH = Vec-finite-discrete ϵ (n , f)
  m : ℕ
  m = pr₁ IH
  g : F × Vec F ϵ → Vec F (succ ϵ)
  g (f , vs) = f ∷ vs
  h : Vec F (succ ϵ) → F × Vec F ϵ
  h (f ∷ vs) = f , vs
  η : (λ x → h (g x)) ∼ (λ x → x)
  η (f , vs) = refl
  μ : (λ x → g (h x)) ∼ (λ x → x)
  μ (f ∷ vs) = refl

-- Should be in paper
ℕ→F-is-totally-bounded : {F : 𝓤 ̇ } → (f : finite-discrete F) → F
                       → totally-bounded
                           (ℕ→D-ClosenessSpace
                             (finite-discrete-is-discrete f)) 𝓤
ℕ→F-is-totally-bounded {𝓤} {F} f x₀ ϵ
 = (Vec F ϵ , Vec-to-Seq x₀ , γ ϵ) , Vec-finite-discrete ϵ f
 where
  d : is-discrete F
  d = finite-discrete-is-discrete f
  γ : (ϵ : ℕ) → (α : ℕ → F) → Σ v ꞉ (Vec F ϵ)
    , (C (ℕ→D-ClosenessSpace d) ϵ α (Vec-to-Seq x₀ v))
  ζ : (α : ℕ → F) (ϵ n : ℕ) → n < succ ϵ
    → (α ∼ⁿ (Vec-to-Seq x₀ (α 0 ∷ pr₁ (γ ϵ (α ∘ succ))))) (succ n)
  
  γ 0 α = [] , (λ _ ())
  γ (succ ϵ) α
   = (α 0 ∷ pr₁ (γ ϵ (α ∘ succ)))
   , λ n n⊏ϵ → decidable-𝟚₁ (discrete-decidable-seq _ _ _ (succ n))
                 (ζ (λ z → α z) ϵ n (⊏-gives-< n (succ ϵ) n⊏ϵ)) 

  ζ α ϵ n n<ϵ zero i<n = refl
  ζ α (succ ϵ) (succ n) n<ϵ (succ i) i<n = ζ (α ∘ succ) ϵ n n<ϵ i i<n

Vec-decreasing : {n : ℕ} → Vec 𝟚 n → 𝓤₀ ̇
Vec-decreasing {0} []    = 𝟙
Vec-decreasing {1} [ ₀ ] = 𝟙
Vec-decreasing {1} [ ₁ ] = 𝟙
Vec-decreasing {succ (succ n)} (₀ ∷ (₀ ∷ v))
 = Vec-decreasing (₀ ∷ v)
Vec-decreasing {succ (succ n)} (₀ ∷ (₁ ∷ v))
 = 𝟘
Vec-decreasing {succ (succ n)} (₁ ∷ v)
 = Vec-decreasing v

Vec-decreasing-is-prop : {n : ℕ} → (x : Vec 𝟚 n)
                       → is-prop (Vec-decreasing x)
Vec-decreasing-is-prop {0} []    = 𝟙-is-prop
Vec-decreasing-is-prop {1} [ ₀ ] = 𝟙-is-prop
Vec-decreasing-is-prop {1} [ ₁ ] = 𝟙-is-prop
Vec-decreasing-is-prop {succ (succ n)} (₀ ∷ (₀ ∷ v))
 = Vec-decreasing-is-prop (₀ ∷ v)
Vec-decreasing-is-prop {succ (succ n)} (₀ ∷ (₁ ∷ v))
 = 𝟘-is-prop
Vec-decreasing-is-prop {succ (succ n)} (₁ ∷ v)
 = Vec-decreasing-is-prop v

Vec-comp-decreasing : {n : ℕ} → ((v , _) : Σ (Vec-decreasing {n}))
                    → Vec-decreasing (₁ ∷ v)
Vec-comp-decreasing {zero} ([] , _) = ⋆
Vec-comp-decreasing {succ n} (_ , d) = d

repeat-vec : {X : 𝓤 ̇ } {n : ℕ} → X → Vec X n
repeat-vec {𝓤} {X} {zero} x₀ = []
repeat-vec {𝓤} {X} {succ n} x₀ = x₀ ∷ repeat-vec x₀

repeat-₀-decreasing : (n : ℕ) → Vec-decreasing {n} (repeat-vec ₀)
repeat-₀-decreasing zero = ⋆
repeat-₀-decreasing (succ zero) = ⋆
repeat-₀-decreasing (succ (succ n)) = repeat-₀-decreasing (succ n)

head-₀-only-repeat-₀-decreasing
 : (n : ℕ) → ((v , _) : Σ (Vec-decreasing {n}))
 → Vec-decreasing (₀ ∷ v)
 → repeat-vec ₀ ＝ v
head-₀-only-repeat-₀-decreasing zero ([] , _) _         = refl
head-₀-only-repeat-₀-decreasing (succ zero) ([ ₀ ] , _) _ = refl
head-₀-only-repeat-₀-decreasing (succ (succ n)) ((₀ ∷ (₀ ∷ v)) , d) d'
 = ap (₀ ∷_) (head-₀-only-repeat-₀-decreasing (succ n) (₀ ∷ v , d) d')

Vec-decreasing-finite : (n : ℕ) → finite-discrete (Σ (Vec-decreasing {n}))
Vec-decreasing-finite n = succ n , qinveq (g n) (h n , η n , μ n)
 where
  g : (n : ℕ) → 𝔽 (succ n) → Σ (Vec-decreasing {n})
  g 0     (inl _) = []    , ⋆
  g 1     (inl _) = [ ₀ ] , ⋆
  g 1     (inr _) = [ ₁ ] , ⋆
  g (succ (succ n)) (inl _) = repeat-vec ₀
                            , repeat-₀-decreasing (succ (succ n))
  g (succ (succ n)) (inr x) = (₁ ∷ pr₁ (g (succ n) x))
                            , pr₂ (g (succ n) x)
  h : (n : ℕ) → Σ (Vec-decreasing {n}) → 𝔽 (succ n)
  h 0     ([]    , ⋆) = inl ⋆
  h 1     ([ ₀ ] , ⋆) = inl ⋆
  h 1     ([ ₁ ] , ⋆) = inr (inl ⋆)
  h (succ (succ n)) ((₀ ∷ _) , _) = inl ⋆
  h (succ (succ n)) ((₁ ∷ v) , d) = inr (h (succ n) (v , d))
  η : (n : ℕ) → (x : 𝔽 (succ n)) → h n (g n x) ＝ x
  η 0     (inl ⋆) = refl
  η 1     (inl ⋆) = refl
  η 1     (inr (inl ⋆)) = refl
  η (succ (succ n)) (inl ⋆) = refl
  η (succ (succ n)) (inr x) = ap inr (η (succ n) x)
  μ : (n : ℕ) → (x : Σ (Vec-decreasing {n})) → g n (h n x) ＝ x
  μ 0     ([]    , ⋆) = refl
  μ 1     ([ ₀ ] , ⋆) = refl
  μ 1     ([ ₁ ] , ⋆) = refl
  μ (succ (succ n)) ((₀ ∷ v) , d)
   = to-subtype-＝ Vec-decreasing-is-prop
      (head-₀-only-repeat-₀-decreasing (succ (succ n)) ((₀ ∷ v) , d) d)
  μ (succ (succ n)) ((₁ ∷ v) , d)
   = to-subtype-＝ Vec-decreasing-is-prop
      (ap (₁ ∷_) (ap pr₁ (μ (succ n) (v , d))))

Seq-to-Vec : {X : 𝓤 ̇ } → (ℕ → X) → (n : ℕ) → Vec X n
Seq-to-Vec α zero = []
Seq-to-Vec α (succ n) = (α 0) ∷ (Seq-to-Vec (α ∘ succ) n)

Seq-to-Vec-decreasing' : (n : ℕ) (v : Vec 𝟚 n)
                       → (a b : 𝟚) → ¬ ((a ＝ ₀) × (b ＝ ₁))
                       → Vec-decreasing (b ∷ v)
                       → Vec-decreasing (a ∷ (b ∷ v))
Seq-to-Vec-decreasing' n v ₀ ₀ f g = g
Seq-to-Vec-decreasing' n v ₁ ₀ f g = g
Seq-to-Vec-decreasing' n v ₁ ₁ f g = g
Seq-to-Vec-decreasing' n v ₀ ₁ f g = 𝟘-elim (f (refl , refl))

Seq-to-Vec-decreasing : (n : ℕ) (α : ℕ → 𝟚)
                      → is-decreasing α
                      → Vec-decreasing (Seq-to-Vec α n)
Seq-to-Vec-decreasing zero α d = ⋆
Seq-to-Vec-decreasing (succ zero) α d with α 0
... | ₀ = ⋆
... | ₁ = ⋆
Seq-to-Vec-decreasing (succ (succ n)) α d
 = Seq-to-Vec-decreasing' n (Seq-to-Vec (α ∘ succ ∘ succ) n)
     (α 0) (α 1) γ
     (Seq-to-Vec-decreasing (succ n) (α ∘ succ) (d ∘ succ))
 where
  γ : ¬ ((α 0 ＝ ₀) × (α 1 ＝ ₁))
  γ (e₀ , e₁) = u (α 0) (α 1) e₀ e₁ (d 0)
   where
    u : (a b : 𝟚) → a ＝ ₀ → b ＝ ₁ → ¬ (a ≥ b)
    u a b refl refl = id

Vec-to-Seq-decreasing : (n : ℕ) (v : Vec 𝟚 n)
                      → Vec-decreasing v
                      → is-decreasing (Vec-to-Seq ₀ v)
Vec-to-Seq-decreasing 0 [] d _ = ⋆
Vec-to-Seq-decreasing 1 [ ₀ ] d _ = ⋆
Vec-to-Seq-decreasing 1 [ ₁ ] d _ = ⋆
Vec-to-Seq-decreasing (succ (succ n)) (₀ ∷ (₀ ∷ v)) d = γ
 where
  γ : is-decreasing (Vec-to-Seq ₀ (₀ ∷ (₀ ∷ v)))
  γ zero = ⋆
  γ (succ i) = Vec-to-Seq-decreasing (succ n) (₀ ∷ v) d i
Vec-to-Seq-decreasing (succ (succ n)) (₁ ∷ (₀ ∷ v)) d = γ
 where
  γ : is-decreasing (Vec-to-Seq ₀ (₁ ∷ (₀ ∷ v)))
  γ zero = ⋆
  γ (succ i) = Vec-to-Seq-decreasing (succ n) (₀ ∷ v) d i
Vec-to-Seq-decreasing (succ (succ n)) (₁ ∷ (₁ ∷ v)) d = γ
 where
  γ : is-decreasing (Vec-to-Seq ₀ (₁ ∷ (₁ ∷ v)))
  γ zero = ⋆
  γ (succ i) = Vec-to-Seq-decreasing (succ n) (₁ ∷ v) d i

ℕ∞-is-totally-bounded : totally-bounded ℕ∞-ClosenessSpace 𝓤₀
ℕ∞-is-totally-bounded ϵ'
 = (Σ Vec-decreasing , (f ϵ' , γ ϵ')) , Vec-decreasing-finite ϵ'
 where
  f : (n : ℕ) → Σ (Vec-decreasing {n}) → ⟨ ℕ∞-ClosenessSpace ⟩
  f n (v , d) = (Vec-to-Seq ₀ v) , Vec-to-Seq-decreasing n v d

  γ : (ϵ : ℕ) → (α : ℕ∞) → Σ v ꞉ (Σ Vec-decreasing)
    , (C ℕ∞-ClosenessSpace ϵ α (f ϵ v))
  ζ : (α : ℕ∞) (ϵ n : ℕ) → n < ϵ
    → ((λ z → pr₁ α z) ∼ⁿ
       (λ z →
          pr₁
          (f ϵ
           (Seq-to-Vec (pr₁ α) ϵ , Seq-to-Vec-decreasing ϵ (pr₁ α) (pr₂ α)))
          z))
      (succ n)

  γ ϵ α = (Seq-to-Vec (pr₁ α) ϵ
               , Seq-to-Vec-decreasing ϵ (pr₁ α) (pr₂ α))
               , λ n n⊏ϵ → decidable-𝟚₁
                   (discrete-decidable-seq _ _ _ (succ n))
                   (ζ α ϵ n (⊏-gives-< n ϵ n⊏ϵ))
   where
    IH = γ ϵ ((pr₁ α ∘ succ) , (pr₂ α ∘ succ))
  ζ α (succ ϵ) n n<ϵ zero i<n = refl
  ζ α (succ ϵ) (succ n) n<ϵ (succ i) i<n
   = ζ ((pr₁ α ∘ succ) , (pr₂ α ∘ succ)) ϵ n n<ϵ i i<n

\end{code}

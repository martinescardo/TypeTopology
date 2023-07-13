\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import UF.FunExt
open import NotionsOfDecidability.Complemented
open import UF.Subsingletons
open import UF.Equiv

module TWA.Thesis.Chapter3.Tychonoff (fe : FunExt) where

open import TWA.Thesis.Chapter2.Sequences
open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.ClosenessSpaces-Examples fe
open import TWA.Thesis.Chapter3.SearchableTypes fe
 hiding (tail-predicate)
open import TypeTopology.DiscreteAndSeparated
open import TWA.Thesis.Chapter6.SequenceContinuity fe




\end{code}

tail-predicate-reduce-mod
  : ((T , cs) : sequence-of-clofun-types 𝓤)
  → (is : (n : ℕ) → is-clofun (cs n))
  → ((p , d) : d-predicate (Π T))
  → (x : T 0) → (δ : ℕ)
  → (succ δ) is-u-mod-of p on Π-clofun (T , cs)
  →       δ  is-u-mod-of (pr₁ (tail-predicate (p , d) x))
                      on Π-clofun ((T ∘ succ) , (cs ∘ succ))
tail-predicate-reduce-mod (T , cs) is p x δ ϕ (xs , ys) δ≼cxsys
 = ϕ (x :: xs , x :: ys)
     (build-up (T , cs) x x xs ys δ (≼-clofun-refl (cs 0) (is 0) (succ δ) x) δ≼cxsys)


head-predicate-attempt : ((T , cs) : sequence-of-clofun-types 𝓤)
                       → ((n : ℕ) → is-clofun (cs n))
                       → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
                       → ((p , d) : d-predicate (Π T))
                       → (δ : ℕ) → succ δ is-u-mod-of p on (Π-clofun (T , cs))
                       → d-predicate (T 0)
head-predicate-attempt (T , cs) is 𝓔s (p , d) δ ϕ
 = (λ x → p (x :: 𝓔xs x)) , (λ x → d (x :: 𝓔xs x))
 where
   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ)
             (tail-predicate (p , d) x)
             δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)


head-predicate-same-mod-attempt
  : ((T , cs) : sequence-of-clofun-types 𝓤)
  → (is : (n : ℕ) → is-clofun (cs n))
  → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
  → ((p , d) : d-predicate (Π T))
  → (δ : ℕ) → (ϕ : succ δ is-u-mod-of p on (Π-clofun (T , cs)))
  → succ δ is-u-mod-of pr₁ (head-predicate-attempt (T , cs) is 𝓔s (p , d) δ ϕ) on (cs 0)
head-predicate-same-mod-attempt (T , cs) is 𝓔s (p , d) δ ϕ (x , y) δ≼cxy
 = ϕ (x :: 𝓔xs x , y :: 𝓔xs y)
     (build-up (T , cs) x y (𝓔xs x) (𝓔xs y) δ δ≼cxy gap)
  where
    𝓔xs : T 0 → Π (T ∘ succ)
    𝓔xs x = Searcher-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ)
              (tail-predicate (p , d) x)
              δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
    gap : (δ ↑) ≼ Π-clofun (T ∘ succ , cs ∘ succ) (𝓔xs x , 𝓔xs y)
    gap = lol


head-predicate-full-attempt
  : ((T , cs) : sequence-of-clofun-types 𝓤)
  → ((n : ℕ) → is-clofun (cs n))
  → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
  → ((p , d) : d-predicate (Π T))
  → (δ : ℕ) → succ δ is-u-mod-of p on (Π-clofun (T , cs))
  → uc-d-predicate (T 0) (cs 0)
head-predicate-full-attempt (T , cs) is 𝓔s (p , d) δ ϕ
 = head-predicate-attempt (T , cs) is 𝓔s (p , d) δ ϕ
 , succ δ
 , head-predicate-same-mod-attempt (T , cs) is 𝓔s (p , d) δ ϕ
```

We attempt to define the `Searcher` and `Condition` as before...

```agda
Searcher-attempt  (T , cs) is 𝓔s (p , d) 0        ϕ
 = λ n → c-searchable-types-are-inhabited (cs n) (𝓔s n)

Searcher-attempt  (T , cs) is 𝓔s (p , d) (succ δ) ϕ
 = x :: 𝓔xs x
 where
   pₕ = pr₁ (head-predicate-attempt (T , cs) is 𝓔s (p , d) δ ϕ)

   S-head : Σ x₀ ꞉ T 0 , (Σ pₕ → pₕ x₀)
   S-head = 𝓔s 0 (head-predicate-full-attempt (T , cs) is 𝓔s (p , d) δ ϕ)

   x : T 0
   x = pr₁ S-head

   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x' = Searcher-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ)
              (tail-predicate (p , d) x')
              δ (tail-predicate-reduce-mod (T , cs) is (p , d) x' δ ϕ)

Condition-attempt (T , cs) is Is (p , d) 0        ϕ (α , pα)
 = 0-mod-always-satisfied (Π-clofun (T , cs)) (p , d) ϕ (α , pα)
     (Searcher-attempt (T , cs) is Is (p , d) 0 ϕ)
     
Condition-attempt (T , cs) is Is (p , d) (succ δ) ϕ (α , pα)
 = γ (α , pα)
 where
   pₕ = pr₁ (head-predicate-attempt (T , cs) is Is (p , d) δ ϕ)
   pₜ = λ x' → pr₁ (tail-predicate (p , d) x')

   S-head : Σ x₀ ꞉ T 0 , (Σ pₕ → pₕ x₀)
   S-head = Is 0 (head-predicate-full-attempt (T , cs) is Is (p , d) δ ϕ)

   x : T 0
   x = pr₁ S-head

   γₕ : Σ pₕ → pₕ x
   γₕ = pr₂ S-head

   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x' = Searcher-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ)
              (tail-predicate (p , d) x')
              δ (tail-predicate-reduce-mod (T , cs) is (p , d) x' δ ϕ)
               
   γₜ : (x' : T 0) → Σ (pₜ x') → pₜ x' (𝓔xs x')
   γₜ x' = Condition-attempt (T ∘ succ , cs ∘ succ) (is ∘ succ) (Is ∘ succ)
               (tail-predicate (p , d) x')
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x' δ ϕ)

   γ : Σ p → p (x :: 𝓔xs x)
   γ (α₀ , pα₀) = step₆ where
     x₀  = head α₀
     xs₀ = tail α₀

     step₁ : p (x₀ :: xs₀)
     step₁ = transport p (head-tail-eta α₀) pα₀

     step₂ : (pₜ x₀) xs₀
     step₂ = step₁
    
     step₃ : (pₜ x₀) (𝓔xs x₀)
     step₃ = γₜ x₀ (xs₀ , step₂)
 
     step₄ : pₕ x₀
     step₄ = step₃
    
     step₅ : pₕ x
     step₅ = γₕ (x₀ , step₄)

     step₆ : p (x :: 𝓔xs x)
     step₆ = step₅

agree-everywhere : {X : 𝓤 ̇ } → d-predicate X → d-predicate X → 𝓤 ̇
agree-everywhere {𝓤} {X} (p₁ , d₁) (p₂ , d₂) = ((x : X) → p₁ x → p₂ x)
                                             × ((x : X) → p₂ x → p₁ x)


agree-everywhere-self : {X : 𝓤 ̇ } → ((p , d) : d-predicate X)
                      → agree-everywhere (p , d) (p , d)
agree-everywhere-self (p , d) = (λ x px → px) , (λ x px → px)

agreeable : {X : 𝓤 ̇ } → (c : X × X → ℕ∞) → c-searchable X c → (𝓤₀ ⁺) ⊔ 𝓤 ̇ 
agreeable {𝓤} {X} c S = ((p₁ , d₁) (p₂ , d₂) : d-predicate X)
                      → (δ : ℕ)
                      → agree-everywhere (p₁ , d₁) (p₂ , d₂)
                      → (ϕ₁ : δ is-u-mod-of p₁ on c)
                      → (ϕ₂ : δ is-u-mod-of p₂ on c)
                      → (δ ↑) ≼ c (pr₁ (S ((p₁ , d₁) , δ , ϕ₁))
                                 , pr₁ (S ((p₂ , d₂) , δ , ϕ₂)))

𝟚-is-c-searchable' : (p : 𝟚 → 𝓤 ̇ )
                   → decidable (p ₁)
                   → Σ x₀ ꞉ 𝟚 , (Σ p → p x₀)
𝟚-is-c-searchable' p (inl  p₁)
 = ₁ , (λ _ → p₁)
𝟚-is-c-searchable' p (inr ¬p₁)
 = ₀ , γ
 where
   γ : Σ p → p ₀
   γ (₀ , p₀) = p₀
   γ (₁ , p₁) = 𝟘-elim (¬p₁ p₁)

𝟚-is-c-searchable : c-searchable 𝟚 (discrete-clofun 𝟚-is-discrete)
𝟚-is-c-searchable ((p , d) , _) = 𝟚-is-c-searchable' p (d ₁)

𝟚-is-c-searchable'-agree-eq : ((p₁ , d₁) (p₂ , d₂) : d-predicate 𝟚)
                            → agree-everywhere (p₁ , d₁) (p₂ , d₂)
                            → pr₁ (𝟚-is-c-searchable' p₁ (d₁ ₁))
                            ＝ pr₁ (𝟚-is-c-searchable' p₂ (d₂ ₁))
𝟚-is-c-searchable'-agree-eq (p₁ , d₁) (p₂ , d₂) (f , g) = γ (d₁ ₁) (d₂ ₁)
 where
   γ : (d₁₁ : decidable (p₁ ₁)) (d₂₁ : decidable (p₂ ₁))
     → pr₁ (𝟚-is-c-searchable' p₁ d₁₁) ＝ pr₁ (𝟚-is-c-searchable' p₂ d₂₁)
   γ (inl  _ ) (inl  _ ) = refl
   γ (inr  _ ) (inr  _ ) = refl
   γ (inl  p₁) (inr ¬p₁) = 𝟘-elim (¬p₁ (f ₁ p₁))
   γ (inr ¬p₁) (inl  p₁) = 𝟘-elim (¬p₁ (g ₁ p₁))
   
𝟚-has-agreeable-searcher : agreeable (discrete-clofun 𝟚-is-discrete)
                             𝟚-is-c-searchable
𝟚-has-agreeable-searcher (p₁ , d₁) (p₂ , d₂) δ (f , g) ϕ₁ ϕ₂
 = transport (λ - → (δ ↑) ≼ discrete-clofun 𝟚-is-discrete
               (pr₁ (𝟚-is-c-searchable' p₁ (d₁ ₁)) , -))
     (𝟚-is-c-searchable'-agree-eq (p₁ , d₁) (p₂ , d₂) (f , g))
     (≼-clofun-refl (discrete-clofun 𝟚-is-discrete)
       (discrete-is-clofun 𝟚-is-discrete)
       δ (pr₁ (𝟚-is-c-searchable' p₁ (d₁ ₁))))

tychonoff : ((T , cs) : sequence-of-clofun-types 𝓤)
          → ((n : ℕ) → is-clofun (cs n))
          → (Is : (n : ℕ) → c-searchable (T n) (cs n))
          → ((n : ℕ) → agreeable (cs n) (Is n))       -- New!
          → c-searchable (Π T) (Π-clofun (T , cs))    

Searcher : ((T , cs) : sequence-of-clofun-types 𝓤)
         → ((n : ℕ) → is-clofun (cs n))
         → (Is : (n : ℕ) → c-searchable (T n) (cs n))
         → ((n : ℕ) → agreeable (cs n) (Is n))        -- New!
         → ((p , d) : d-predicate (Π T))
         → (δ : ℕ)
         → δ is-u-mod-of p on Π-clofun (T , cs)
         → Π T

Condition : ((T , cs) : sequence-of-clofun-types 𝓤)
          → (is : (n : ℕ) → is-clofun (cs n))
          → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
          → (as : (n : ℕ) → agreeable (cs n) (𝓔s n))  -- New!
          → ((p , d) : d-predicate (Π T))
          → (δ : ℕ)
          → (ϕ : δ is-u-mod-of p on Π-clofun (T , cs))
          → Σ p → p (Searcher (T , cs) is 𝓔s as (p , d) δ ϕ)

tychonoff (T , cs) is 𝓔s as ((p , d) , δ , ϕ)
 = Searcher  (T , cs) is 𝓔s as (p , d) δ ϕ
 , Condition (T , cs) is 𝓔s as (p , d) δ ϕ

Agreeable : ((T , cs) : sequence-of-clofun-types 𝓤)
          → (is : (n : ℕ) → is-clofun (cs n))
          → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
          → (as : (n : ℕ) → agreeable (cs n) (𝓔s n))
          → ((p₁ , d₁) (p₂ , d₂) : d-predicate (Π T))
          → (δ : ℕ)
          → agree-everywhere (p₁ , d₁) (p₂ , d₂)
          → (ϕ₁ : δ is-u-mod-of p₁ on (Π-clofun (T , cs)))
          → (ϕ₂ : δ is-u-mod-of p₂ on (Π-clofun (T , cs)))
          → (δ ↑) ≼ Π-clofun (T , cs)
                      (Searcher (T , cs) is 𝓔s as (p₁ , d₁) δ ϕ₁
                     , Searcher (T , cs) is 𝓔s as (p₂ , d₂) δ ϕ₂)

tail-predicate-agree : ((T , cs) : sequence-of-clofun-types 𝓤)
                     → (is : (n : ℕ) → is-clofun (cs n))
                     → ((p₁ , d₁) (p₂ , d₂) : d-predicate (Π T))
                     → (δ : ℕ)
                     → (x y : T 0)
                     → (succ δ ↑) ≼ cs 0 (x , y)
                     → agree-everywhere (p₁ , d₁) (p₂ , d₂)
                     → (ϕ₁ : succ δ is-u-mod-of p₁ on (Π-clofun (T , cs)))
                     → (ϕ₂ : succ δ is-u-mod-of p₂ on (Π-clofun (T , cs)))
                     → agree-everywhere (tail-predicate (p₁ , d₁) x)
                                        (tail-predicate (p₂ , d₂) y)
tail-predicate-agree (T , cs) is (p₁ , d₁) (p₂ , d₂) δ x y δ≼cxy (f , g) ϕ₁ ϕ₂
 = (λ xs pₜ₁xs → ϕ₂ (x :: xs , y :: xs)
                    (build-up (T , cs) x y xs xs δ δ≼cxy (δ≼cxsxs xs))
                    (f (x :: xs) pₜ₁xs))
 , (λ xs pₜ₂xs → ϕ₁ (y :: xs , x :: xs)
                    (build-up (T , cs) y x xs xs δ δ≼cyx (δ≼cxsxs xs))
                    (g (y :: xs) pₜ₂xs))
 where
   δ≼cxsxs = ≼-clofun-refl (Π-clofun (T ∘ succ , cs ∘ succ))
                        (Π-is-clofun (T ∘ succ , cs ∘ succ) (is ∘ succ)) δ
   δ≼cyx   = ≼-clofun-sym (cs 0) (is 0) (succ δ) x y δ≼cxy

head-predicate : ((T , cs) : sequence-of-clofun-types 𝓤)
               → ((n : ℕ) → is-clofun (cs n))
               → (Is : (n : ℕ) → c-searchable (T n) (cs n))
               → ((n : ℕ) → agreeable (cs n) (Is n))
               → ((p , d) : d-predicate (Π T))
               → (δ : ℕ) → succ δ is-u-mod-of p on (Π-clofun (T , cs))
               → d-predicate (T 0)
head-predicate (T , cs) is 𝓔s as (p , d) δ ϕ
 = (λ x → p (x :: 𝓔xs x)) , (λ x → d (x :: 𝓔xs x))
 where
   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)

head-predicate-same-mod
  : ((T , cs) : sequence-of-clofun-types 𝓤)
  → (is : (n : ℕ) → is-clofun (cs n))
  → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
  → (as : (n : ℕ) → agreeable (cs n) (𝓔s n))
  → ((p , d) : d-predicate (Π T))
  → (δ : ℕ) → (ϕ : succ δ is-u-mod-of p on (Π-clofun (T , cs)))
  → succ δ is-u-mod-of pr₁ (head-predicate (T , cs) is 𝓔s as (p , d) δ ϕ) on (cs 0)
head-predicate-same-mod (T , cs) is 𝓔s as (p , d) δ ϕ (x , y) δ≼cxy
 = ϕ (x :: 𝓔xs x , y :: 𝓔xs y)
     (build-up (T , cs) x y (𝓔xs x) (𝓔xs y) δ δ≼cxy gap)
  where
    𝓔xs : T 0 → Π (T ∘ succ)
    𝓔xs x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
              (tail-predicate (p , d) x)
              δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
    gap : (δ ↑) ≼ Π-clofun (T ∘ succ , cs ∘ succ) (𝓔xs x , 𝓔xs y)
    gap = Agreeable (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
           (tail-predicate (p , d) x)
           (tail-predicate (p , d) y)
           δ
           (tail-predicate-agree (T , cs) is (p , d) (p , d) δ x y δ≼cxy
             (agree-everywhere-self (p , d)) ϕ ϕ)
           (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
           (tail-predicate-reduce-mod (T , cs) is (p , d) y δ ϕ)

head-predicate-full : ((T , cs) : sequence-of-clofun-types 𝓤)
                    → ((n : ℕ) → is-clofun (cs n))
                    → (Is : (n : ℕ) → c-searchable (T n) (cs n))
                    → ((n : ℕ) → agreeable (cs n) (Is n))
                    → ((p , d) : d-predicate (Π T))
                    → (δ : ℕ) → succ δ is-u-mod-of p on (Π-clofun (T , cs))
                    → uc-d-predicate (T 0) (cs 0)
head-predicate-full (T , cs) is 𝓔s as (p , d) δ ϕ
 = head-predicate (T , cs) is 𝓔s as (p , d) δ ϕ
 , succ δ
 , head-predicate-same-mod (T , cs) is 𝓔s as (p , d) δ ϕ

head-predicate-agree
  : ((T , cs) : sequence-of-clofun-types 𝓤)
  → (is : (n : ℕ) → is-clofun (cs n))
  → (𝓔s : (n : ℕ) → c-searchable (T n) (cs n))
  → (as : (n : ℕ) → agreeable (cs n) (𝓔s n))
  → ((p₁ , d₁) (p₂ , d₂) : d-predicate (Π T))
  → (δ : ℕ)
  → agree-everywhere (p₁ , d₁) (p₂ , d₂)
  → (ϕ₁ : succ δ is-u-mod-of p₁ on (Π-clofun (T , cs)))
  → (ϕ₂ : succ δ is-u-mod-of p₂ on (Π-clofun (T , cs)))
  → agree-everywhere
      (head-predicate (T , cs) is 𝓔s as (p₁ , d₁) δ ϕ₁)
      (head-predicate (T , cs) is 𝓔s as (p₂ , d₂) δ ϕ₂)
head-predicate-agree (T , cs) is 𝓔s as (p₁ , d₁) (p₂ , d₂) δ (f , g) ϕ₁ ϕ₂
 = (λ x pₕ₁x → ϕ₂ (x :: 𝓔xs₁ x , x :: 𝓔xs₂ x) (γ  x) (f (x :: 𝓔xs₁ x) pₕ₁x))
 , (λ x pₕ₂x → ϕ₁ (x :: 𝓔xs₂ x , x :: 𝓔xs₁ x) (γ' x) (g (x :: 𝓔xs₂ x) pₕ₂x))
 where
   𝓔xs₁ 𝓔xs₂ : T 0 → Π (T ∘ succ)
   𝓔xs₁ x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p₁ , d₁) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p₁ , d₁) x δ ϕ₁)
   𝓔xs₂ x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p₂ , d₂) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p₂ , d₂) x δ ϕ₂)
   γ : (x : T 0) → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: 𝓔xs₁ x , x :: 𝓔xs₂ x)
   γ x = build-up (T , cs) x x (𝓔xs₁ x) (𝓔xs₂ x) δ δ≼cxx
           (Agreeable (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
             (tail-predicate (p₁ , d₁) x) (tail-predicate (p₂ , d₂) x)
             δ
             (tail-predicate-agree (T , cs) is (p₁ , d₁) (p₂ , d₂)
               δ x x δ≼cxx (f , g) ϕ₁ ϕ₂)
             (tail-predicate-reduce-mod (T , cs) is (p₁ , d₁) x δ ϕ₁)
             (tail-predicate-reduce-mod (T , cs) is (p₂ , d₂) x δ ϕ₂))
    where
      δ≼cxx = ≼-clofun-refl (cs 0) (is 0) (succ δ) x
   γ' : (x : T 0) → (succ δ ↑) ≼ Π-clofun (T , cs) (x :: 𝓔xs₂ x , x :: 𝓔xs₁ x)
   γ' x = ≼-clofun-sym (Π-clofun (T , cs)) (Π-is-clofun (T , cs) is)
            (succ δ) (x :: 𝓔xs₁ x) (x :: 𝓔xs₂ x) (γ x)

Searcher  (T , cs) is 𝓔s as (p , d) 0        ϕ
 = λ n → c-searchable-types-are-inhabited (cs n) (𝓔s n)

Searcher  (T , cs) is 𝓔s as (p , d) (succ δ) ϕ
 = x :: 𝓔xs x
 where
   pₕ = pr₁ (head-predicate (T , cs) is 𝓔s as (p , d) δ ϕ)

   S-head : Σ x₀ ꞉ T 0 , (Σ pₕ → pₕ x₀)
   S-head = 𝓔s 0 (head-predicate-full (T , cs) is 𝓔s as (p , d) δ ϕ)

   x : T 0
   x = pr₁ S-head

   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)

Condition (T , cs) is 𝓔s as (p , d) 0        ϕ (α , pα)
 = 0-mod-always-satisfied (Π-clofun (T , cs)) (p , d) ϕ (α , pα)
     (Searcher (T , cs) is 𝓔s as (p , d) 0 ϕ)
     
Condition (T , cs) is 𝓔s as (p , d) (succ δ) ϕ (α , pα)
 = γ (α , pα)
 where
   pₕ = pr₁ (head-predicate (T , cs) is 𝓔s as (p , d) δ ϕ)
   pₜ = λ x' → pr₁ (tail-predicate (p , d) x')

   S-head : Σ x₀ ꞉ T 0 , (Σ pₕ → pₕ x₀)
   S-head = 𝓔s 0 (head-predicate-full (T , cs) is 𝓔s as (p , d) δ ϕ)

   x : T 0
   x = pr₁ S-head

   γₕ : Σ pₕ → pₕ x
   γₕ = pr₂ S-head

   𝓔xs : T 0 → Π (T ∘ succ)
   𝓔xs x = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)
               
   γₜ : (x' : T 0) → Σ (pₜ x') → pₜ x' (𝓔xs x')
   γₜ x = Condition (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p , d) x)
               δ (tail-predicate-reduce-mod (T , cs) is (p , d) x δ ϕ)

   γ : Σ p → p (x :: 𝓔xs x)
   γ (α₀ , pα₀) = step₆ where
     x₀  = head α₀
     xs₀ = tail α₀

     step₁ : p (x₀ :: xs₀)
     step₁ = transport p (head-tail-eta α₀) pα₀

     step₂ : (pₜ x₀) xs₀
     step₂ = step₁
    
     step₃ : (pₜ x₀) (𝓔xs x₀)
     step₃ = γₜ x₀ (xs₀ , step₂)
 
     step₄ : pₕ x₀
     step₄ = step₃
    
     step₅ : pₕ x
     step₅ = γₕ (x₀ , step₄)

     step₆ : p (x :: 𝓔xs x)
     step₆ = step₅

Agreeable (T , cs) is 𝓔s as (p₁ , d₁) (p₂ , d₂) 0        (f , g) ϕ₁ ϕ₂
  = ≼-clofun-refl (Π-clofun (T , cs)) (Π-is-clofun (T , cs) is)
      0 (Searcher (T , cs) is 𝓔s as (p₁ , d₁) 0 ϕ₁)

Agreeable (T , cs) is 𝓔s as (p₁ , d₁) (p₂ , d₂) (succ δ) (f , g) ϕ₁ ϕ₂
 = build-up (T , cs) x y (𝓔xs₁ x) (𝓔xs₂ y) δ γ₁ γ₂
 where
   x y : T 0
   x = pr₁ (𝓔s 0 (head-predicate-full (T , cs) is 𝓔s as (p₁ , d₁) δ ϕ₁))
   y = pr₁ (𝓔s 0 (head-predicate-full (T , cs) is 𝓔s as (p₂ , d₂) δ ϕ₂))
   𝓔xs₁ 𝓔xs₂ : T 0 → Π (T ∘ succ)
   𝓔xs₁ x' = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p₁ , d₁) x')
               δ (tail-predicate-reduce-mod (T , cs) is (p₁ , d₁) x' δ ϕ₁)
   𝓔xs₂ x' = Searcher (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
               (tail-predicate (p₂ , d₂) x')
               δ (tail-predicate-reduce-mod (T , cs) is (p₂ , d₂) x' δ ϕ₂)
   γ₁ : (succ δ ↑) ≼ cs 0 (x , y)
   γ₁ = as 0
          (head-predicate (T , cs) is 𝓔s as (p₁ , d₁) δ ϕ₁)
          (head-predicate (T , cs) is 𝓔s as (p₂ , d₂) δ ϕ₂)
          (succ δ)
          (head-predicate-agree (T , cs) is 𝓔s as (p₁ , d₁) (p₂ , d₂)
            δ (f , g) ϕ₁ ϕ₂)
          (head-predicate-same-mod (T , cs) is 𝓔s as (p₁ , d₁) δ ϕ₁)
          (head-predicate-same-mod (T , cs) is 𝓔s as (p₂ , d₂) δ ϕ₂)
   γ₂ : (δ ↑) ≼ Π-clofun (T ∘ succ , cs ∘ succ) (𝓔xs₁ x , 𝓔xs₂ y)
   γ₂ = Agreeable (T ∘ succ , cs ∘ succ) (is ∘ succ) (𝓔s ∘ succ) (as ∘ succ)
          (tail-predicate (p₁ , d₁) x)
          (tail-predicate (p₂ , d₂) y)
          δ
          (tail-predicate-agree (T , cs) is (p₁ , d₁) (p₂ , d₂)
             δ x y γ₁ (f , g) ϕ₁ ϕ₂)
          (tail-predicate-reduce-mod (T , cs) is (p₁ , d₁) x δ ϕ₁)
          (tail-predicate-reduce-mod (T , cs) is (p₂ , d₂) y δ ϕ₂)

ℕ→𝟚-is-c-searchable'
 : c-searchable (ℕ → 𝟚)
     (Π-clofun ((λ _ → 𝟚) , (λ _ → discrete-clofun 𝟚-is-discrete)))
ℕ→𝟚-is-c-searchable'
 = tychonoff
     ((λ _ → 𝟚)
       , (λ _ → discrete-clofun 𝟚-is-discrete))
     (λ _ → discrete-is-clofun 𝟚-is-discrete)
     (λ _ → 𝟚-is-c-searchable)
     (λ _ → 𝟚-has-agreeable-searcher)

ℕ→ℕ→𝟚-is-c-searchable' : c-searchable (ℕ → (ℕ → 𝟚))
                           (Π-clofun ((λ _ → ℕ → 𝟚)
                           , (λ _ → Π-clofun ((λ _ → 𝟚)
                           , (λ _ → discrete-clofun 𝟚-is-discrete)))))
ℕ→ℕ→𝟚-is-c-searchable'
 = tychonoff
   ((λ _ → ℕ → 𝟚) , (λ _ → Π-clofun ((λ _ → 𝟚)
     , (λ _ → discrete-clofun 𝟚-is-discrete))))
   (λ _ → Π-is-clofun ((λ _ → 𝟚)
     , (λ _ → discrete-clofun 𝟚-is-discrete))
   (λ _ → discrete-is-clofun 𝟚-is-discrete))
   (λ _ → ℕ→𝟚-is-c-searchable')
   (λ _ → Agreeable ((λ _ → 𝟚)
       , (λ _ → discrete-clofun 𝟚-is-discrete))
     (λ _ → discrete-is-clofun 𝟚-is-discrete)
     (λ _ → 𝟚-is-c-searchable)
     (λ _ → 𝟚-has-agreeable-searcher))

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan

open import UF.FunExt 
open import Notation.Order
open import Naturals.Order
open import TypeTopology.DiscreteAndSeparated
open import CoNaturals.GenericConvergentSequence
 hiding (max)
 renaming (ℕ-to-ℕ∞ to _↑)

open import TWA.Thesis.Chapter2.Vectors 
open import TWA.Thesis.Chapter2.Sequences 
open import TWA.Thesis.Chapter5.SignedDigit

module TWA.Thesis.Chapter6.SignedDigitContinuity (fe : FunExt) where

open import TWA.Thesis.Chapter3.ClosenessSpaces fe
open import TWA.Thesis.Chapter3.SearchableTypes fe
-- open import TWA.Thesis.Chapter5.Prelude
{-
_∼ⁿ⋆_ : {X : 𝓤 ̇ } {d : ℕ}
     → (Vec (ℕ → X) (succ d)) → (Vec (ℕ → X) (succ d))
     → Vec ℕ (succ d) → 𝓤 ̇
_∼ⁿ⋆_ {𝓤} {X} {zero} = ?
_∼ⁿ⋆_ {𝓤} {X} {succ d} (α ∷ αs) (β ∷ βs) (n ∷ ns)
 = (α ∼ⁿ β) n × (αs ∼ⁿ⋆ βs) ns

_∼ⁿ⋆⋆_ : {X : 𝓤 ̇ } → (ℕ → (ℕ → X)) → (ℕ → (ℕ → X)) → ℕ → ℕ → 𝓤 ̇
_∼ⁿ⋆⋆_ {𝓤} {X} αs βs m n = (k : ℕ) → k < n → (αs k ∼ⁿ βs k) m

∼ⁿ-uc-mod-of² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {d e : ℕ}
             → (Vec (ℕ → X) (succ d) → Vec (ℕ → Y) (succ e))
             → Vec ℕ (succ e) → Vec ℕ (succ d) → 𝓤 ⊔ 𝓥 ̇
∼ⁿ-uc-mod-of² f ε δ = ∀ α β → (α ∼ⁿ⋆ β) δ → (f α ∼ⁿ⋆ f β) ε

∼ⁿ-continuous² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {d e : ℕ}
              → (Vec (ℕ → X) (succ d) → Vec (ℕ → Y) (succ e) ) → 𝓤 ⊔ 𝓥 ̇
∼ⁿ-continuous² f = ∀ ε → Σ (∼ⁿ-uc-mod-of² f ε)

∼ⁿ-uc-mod-of : {X : 𝓤 ̇ } {d : ℕ}
            → (Vec (ℕ → X) (succ d) → 𝓥 ̇ )
            → Vec ℕ (succ d) → 𝓤 ⊔ 𝓥 ̇
∼ⁿ-uc-mod-of p δ = ∀ α β → (α ∼ⁿ⋆ β) δ → p α → p β

∼ⁿ-continuous : {X : 𝓤 ̇ } {d : ℕ}
             → (Vec (ℕ → X) (succ d) → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
∼ⁿ-continuous p = Σ (∼ⁿ-uc-mod-of p)

∼ⁿ⋆⋆-uc-mod-of² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {d : ℕ}
              → ((ℕ → (ℕ → X)) → Vec (ℕ → Y) (succ d))
              → Vec ℕ (succ d) → ℕ → ℕ → 𝓤 ⊔ 𝓥 ̇
∼ⁿ⋆⋆-uc-mod-of² f ε δ₁ δ₂ = ∀ αs βs → (αs ∼ⁿ⋆⋆ βs) δ₁ δ₂ → (f αs ∼ⁿ⋆ f βs) ε

∼ⁿ⋆⋆-continuous² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {d : ℕ}
               → ((ℕ → (ℕ → X)) → Vec (ℕ → Y) (succ d)) → 𝓤 ⊔ 𝓥 ̇ 
∼ⁿ⋆⋆-continuous² f = ∀ ε → Σ (δs , δ) ꞉ (ℕ × ℕ) , (∼ⁿ⋆⋆-uc-mod-of² f ε δs δ)

vec-repeat : {X : 𝓤 ̇ } {n : ℕ} → X → Vec X (succ n)
vec-repeat {𝓤} {X} {0} x = [ x ]
vec-repeat {𝓤} {X} {succ n} x = x ∷ vec-repeat x

vec-max : {n : ℕ} → Vec ℕ (succ n) → ℕ
vec-max {0} [ x ] = x
vec-max {succ n} (x ∷ xs) = max x (vec-max xs)

max⊏ : (k n m : ℕ) → k ⊏ (n ↑) → k ⊏ ((max n m) ↑)
max⊏ k (succ n) zero k⊏n = k⊏n
max⊏ zero (succ n) (succ m) k⊏n = refl
max⊏ (succ k) (succ n) (succ m) k⊏n = max⊏ k n m k⊏n

max≼ : (n m : ℕ) (v : ℕ∞)
     → ((max n m) ↑) ≼ v
     → (n ↑) ≼ v
     × (m ↑) ≼ v
max≼ n m v maxnm≼v
 = (λ k p → maxnm≼v k (max⊏ k n m p))
 , (λ k q → maxnm≼v k
     (transport (λ - → k ⊏ (- ↑))
       (max-comm m n) (max⊏ k m n q)))
-}
{-
∼ⁿ⋆→≼ : {X : 𝓤 ̇ } (dˣ : is-discrete X)
     → (n : ℕ) (x y : (ℕ → X) ^⟨succ n ⟩)
     → (ε : ℕ) → (x ∼ⁿ⋆ y) (vec-repeat ε)
     → (ε ↑) ≼ ×ⁿ-codistance (codistance X dˣ) n x y
∼ⁿ⋆→≼ dˣ 0 = ∼ⁿ→≼ dˣ
∼ⁿ⋆→≼ {𝓤} {X} dˣ (succ n) (x , xs) (y , ys) ε (x∼ⁿy , xs∼ⁿys)
 = ×-codistance-min
     (codistance X dˣ)
     (×ⁿ-codistance (codistance X dˣ) n)
     (under ε) x y xs ys
     (∼ⁿ→≼ dˣ x y ε x∼ⁿy)
     (∼ⁿ⋆→≼ dˣ n xs ys ε xs∼ⁿys)

≼→∼ⁿ⋆ : {X : 𝓤 ̇ } (dˣ : is-discrete X)
     → (n : ℕ) (x y : (ℕ → X) ^⟨succ n ⟩)
     → (ε : ℕ)
     → under ε ≼ ×ⁿ-codistance
                   (codistance X dˣ) n x y
     → (x ∼ⁿ⋆ y) (vec-repeat ε)
≼→∼ⁿ⋆ dˣ 0 = ≼→∼ⁿ dˣ
≼→∼ⁿ⋆ {𝓤} {X} dˣ (succ n) (x , xs) (y , ys) ε ε≼cxy
 = ≼→∼ⁿ dˣ x y ε (pr₁ γ)
 , ≼→∼ⁿ⋆ dˣ n xs ys ε (pr₂ γ)
 where
   γ = ×-codistance-min'
         (codistance X dˣ)
         (×ⁿ-codistance (codistance X dˣ) n)
         (under ε) x y xs ys
         ε≼cxy

≼→∼ⁿ⋆' : {X : 𝓤 ̇ } (dˣ : is-discrete X)
      → (d n : ℕ) (x y : (ℕ → X) ^⟨succ n ⟩)
      → (ε : ℕ) (f : ℕ ^⟨succ d ⟩ → ℕ ^⟨succ n ⟩)
      → under (vec-max (f (vec-repeat ε)))
                ≼ ×ⁿ-codistance
                    (codistance X dˣ) n x y
      → (x ∼ⁿ⋆ y) (f (vec-repeat ε))
≼→∼ⁿ⋆' dˣ d 0 x y ε f = ≼→∼ⁿ dˣ x y (f (vec-repeat ε))
≼→∼ⁿ⋆' {𝓤} {X} dˣ d (succ n) (x , xs) (y , ys) ε f δ≼cxy
 = ≼→∼ⁿ dˣ x y (pr₁ (f (vec-repeat ε)))
     (pr₁ (max≼ δ₁ δ₂ (codistance X dˣ x y) (pr₁ γ)))
 , ≼→∼ⁿ⋆' dˣ d n xs ys ε (pr₂ ∘ f)
     (pr₂ (max≼ δ₁ δ₂ (×ⁿ-codistance (codistance X dˣ) n xs ys) (pr₂ γ)))
 where
   δ₁ = pr₁ (f (vec-repeat ε))
   δ₂ = vec-max (pr₂ (f (vec-repeat ε)))
   δ = max δ₁ δ₂
   γ = ×-codistance-min'
         (codistance X dˣ)
         (×ⁿ-codistance (codistance X dˣ) n)
         (under δ) x y xs ys
         δ≼cxy
-}
{-
∼ⁿ-continuous→≼-continuous
              : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → (dˣ : is-discrete X) (dʸ : is-discrete Y)
              → (d e : ℕ)
              → (f : (ℕ → X) ^⟨succ d ⟩ → (ℕ → Y) ^⟨succ e ⟩)
              → ∼ⁿ-continuous² f
              → f-ucontinuous
                  (×ⁿ-codistance (codistance X dˣ) d)
                  (×ⁿ-codistance (codistance Y dʸ) e)
                  f
∼ⁿ-continuous→≼-continuous {𝓤} {X} dˣ dʸ d e f ϕ ε
 = vec-max (pr₁ (ϕ (vec-repeat ε)))
 , (λ x y δ≼cxy → ∼ⁿ⋆→≼ dʸ e (f x) (f y) ε
     (pr₂ (ϕ (vec-repeat ε)) x y
       (≼→∼ⁿ⋆' dˣ e d x y ε (λ x → pr₁ (ϕ x)) δ≼cxy)))
-}


div2-continuous : seq-f-ucontinuous¹ div2
div2-continuous zero = 0 , λ α β _ k ()
div2-continuous (succ ε) = succ (succ ε) , γ ε where
  γ : (ε : ℕ) → (α β : ℕ → 𝟝) → (α ∼ⁿ β) (succ (succ ε))
    →  (div2 α ∼ⁿ div2 β) (succ ε)
  γ ε α β α∼ⁿβ 0 ⋆ = ap (λ - → pr₁ (div2-aux - (α 1))) (α∼ⁿβ 0 ⋆)
                   ∙ ap (λ - → pr₁ (div2-aux (β 0) -)) (α∼ⁿβ 1 ⋆)
  γ (succ ε) α β α∼ⁿβ (succ k) = γ ε α' β' α∼ⁿβ' k
   where
    α' = pr₂ (div2-aux (α 0) (α 1)) ∶∶ (tail (tail α))
    β' = pr₂ (div2-aux (β 0) (β 1)) ∶∶ (tail (tail β))
    α∼ⁿβ' : (α' ∼ⁿ β') (succ (succ ε))
    α∼ⁿβ' 0 ⋆ = ap (λ - → pr₂ (div2-aux - (α 1))) (α∼ⁿβ 0 ⋆)
             ∙ ap (λ - → pr₂ (div2-aux (β 0) -)) (α∼ⁿβ 1 ⋆)
    α∼ⁿβ' (succ j) = α∼ⁿβ (succ (succ j))

map-continuous : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } 
               → (f : X → Y) → seq-f-ucontinuous¹ (map f)
map-continuous f ε = ε , λ α β α∼ⁿβ k k<ε → ap f (α∼ⁿβ k k<ε)

zipWith-continuous : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                → (f : X → X → Y)
                → seq-f-ucontinuous² (zipWith f)
zipWith-continuous f ε
 = (ε , ε)
 , (λ α₁ α₂ β₁ β₂ α∼ β∼ k k<ϵ
    → ap (λ - → f - (β₁ k)) (α∼ k k<ϵ)
    ∙ ap (f (α₂ k)) (β∼ k k<ϵ))

neg-continuous : seq-f-ucontinuous¹ neg
neg-continuous = map-continuous flip

mid-continuous : seq-f-ucontinuous² mid
mid-continuous = seq-f-ucontinuous¹²-comp div2 add2
                   div2-continuous (zipWith-continuous _+𝟛_)

bigMid'-continuous : seq-f-ucontinuousᴺ bigMid'
bigMid'-continuous ε = dδ ε , γ ε where
  d : ℕ → ℕ
  d 0 = 0
  d (succ ε) = succ (succ ε)
  δ : ℕ → ℕ
  δ 0 = 0
  δ (succ ε) = succ (succ (succ (δ ε)))
  dδ : ℕ → ℕ × ℕ
  dδ ε = d ε , δ ε
  pr₁δs< : (n : ℕ) → d n < d (succ n)
  pr₁δs< zero = ⋆
  pr₁δs< (succ n) = ≤-refl n
  γ : (ε : ℕ) → (x₁ x₂ : (ℕ → 𝟛ᴺ))
    → ((n : ℕ) → n < d ε → (x₁ n ∼ⁿ x₂ n) (δ ε))
    → (bigMid' x₁ ∼ⁿ bigMid' x₂) ε 
  γ (succ ε) αs βs αs∼ⁿβs zero k<ε
   = ap (λ - → (- +𝟛 -) +𝟝 (αs 0 1 +𝟛 αs 1 0)) (αs∼ⁿβs 0 ⋆ 0 ⋆)
   ∙ ap (λ - → (βs 0 0 +𝟛 βs 0 0) +𝟝 (- +𝟛 αs 1 0)) (αs∼ⁿβs 0 ⋆ 1 ⋆)
   ∙ ap (λ - → (βs 0 0 +𝟛 βs 0 0) +𝟝 (βs 0 1 +𝟛 -)) (αs∼ⁿβs 1 ⋆ 0 ⋆)
  γ (succ (succ ε)) αs βs αs∼ⁿβs (succ k)
   = γ (succ ε) αs' βs' αs∼ⁿβs' k
   where
    αs' = mid (tail (tail (αs 0))) (tail (αs 1)) ∶∶ tail (tail αs) 
    βs' = mid (tail (tail (βs 0))) (tail (βs 1)) ∶∶ tail (tail βs)
    αs∼ⁿβs' : (n : ℕ) → n < d (succ ε)
            → (αs' n ∼ⁿ βs' n) (δ (succ ε))
    αs∼ⁿβs' zero n<d i i<d
     = pr₂ (mid-continuous (δ (succ ε)))
       (tail (tail (αs 0))) (tail (tail (βs 0)))
       (tail       (αs 1) ) (tail       (βs 1) ) 
       (λ i → αs∼ⁿβs zero ⋆ (succ (succ i)))
       (λ i i≤δϵ → αs∼ⁿβs 1 ⋆ (succ i)
         (≤-trans i _ _ i≤δϵ (≤-succ (δ ε)))) i i<d
    αs∼ⁿβs' (succ n) n<d i i≤δϵ
     = αs∼ⁿβs (succ (succ n)) n<d i
         (≤-trans i (succ (succ (δ ε))) (succ (succ (succ (succ (succ (δ ε))))))
           i≤δϵ (≤-+ (δ ε) 3))
           
div4-continuous : seq-f-ucontinuous¹ div4
div4-continuous zero = 0 , λ α β _ k ()
div4-continuous (succ ε) = succ (succ ε) , γ ε where
  γ : (ε : ℕ) → (α β : ℕ → 𝟡) → (α ∼ⁿ β) (succ (succ ε))
    →  (div4 α ∼ⁿ div4 β) (succ ε) 
  γ ε α β α∼ⁿβ 0 ⋆ = ap (λ - → pr₁ (div4-aux - (α 1))) (α∼ⁿβ 0 ⋆)
                  ∙ ap (λ - → pr₁ (div4-aux (β 0) -)) (α∼ⁿβ 1 ⋆)
  γ (succ ε) α β α∼ⁿβ (succ k) = γ ε α' β' α∼ⁿβ' k
   where
    α' = pr₂ (div4-aux (α 0) (α 1)) ∶∶ (tail (tail α))
    β' = pr₂ (div4-aux (β 0) (β 1)) ∶∶ (tail (tail β))
    α∼ⁿβ' : (α' ∼ⁿ β') (succ (succ ε))
    α∼ⁿβ' 0 ⋆ = ap (λ - → pr₂ (div4-aux - (α 1))) (α∼ⁿβ 0 ⋆)
             ∙ ap (λ - → pr₂ (div4-aux (β 0) -)) (α∼ⁿβ 1 ⋆)
    α∼ⁿβ' (succ j) = α∼ⁿβ (succ (succ j))  

bigMid-continuous : seq-f-ucontinuousᴺ bigMid
bigMid-continuous ε = dδ , γ where
  dδ : ℕ × ℕ
  dδ = pr₁ (bigMid'-continuous (pr₁ (div4-continuous ε)))
  γ : (x₁ x₂ : ℕ → 𝟛ᴺ)
    → ((n : ℕ) → n < pr₁ dδ → ((x₁ n) ∼ⁿ (x₂ n)) (pr₂ dδ))
    → (bigMid x₁ ∼ⁿ bigMid x₂) ε 
  γ αs βs αs∼ⁿβs
   = pr₂ (div4-continuous ε)
       (bigMid' αs) (bigMid' βs)
       (pr₂ (bigMid'-continuous (pr₁ (div4-continuous ε)))
         αs βs αs∼ⁿβs)

mul-continuous : seq-f-ucontinuous² mul
mul-continuous ε = δ ε , γ ε where
  δ : ℕ → ℕ × ℕ
  δ ε = pr₁ (bigMid-continuous ε)
  γ : (ε : ℕ) → (α₁ α₂ : 𝟛ᴺ) (β₁ β₂ : 𝟛ᴺ)
    → (α₁ ∼ⁿ α₂) (pr₁ (δ ε)) → (β₁ ∼ⁿ β₂) (pr₂ (δ ε))
    → (mul α₁ β₁ ∼ⁿ mul α₂ β₂) ε
  γ ε α₁ α₂ β₁ β₂ α∼ β∼
   = pr₂ (bigMid-continuous ε) (zipWith digitMul α₁ (λ _ → β₁)) (zipWith digitMul α₂ (λ _ → β₂))
       (λ n n<d k k<δ → ap (_*𝟛 β₁ k) (α∼ n n<d)
                      ∙ ap (α₂ n *𝟛_) (β∼ k k<δ))
         
{-
c𝟛ᴺ : 𝟛ᴺ → 𝟛ᴺ → ℕ∞
c𝟛ᴺ = codistance 𝟛 𝟛-is-discrete

c𝟛ᴺ×𝟛ᴺ : (𝟛ᴺ × 𝟛ᴺ) → (𝟛ᴺ × 𝟛ᴺ) → ℕ∞ 
c𝟛ᴺ×𝟛ᴺ = ×-codistance c𝟛ᴺ c𝟛ᴺ

∼ⁿ→≼-continuous-𝟛ᴺ = ∼ⁿ-continuous→≼-continuous 𝟛-is-discrete 𝟛-is-discrete

neg-continuous≼ : continuous² c𝟛ᴺ c𝟛ᴺ neg
neg-continuous≼ = ∼ⁿ→≼-continuous-𝟛ᴺ 0 0 neg neg-continuous

mid-continuous≼ : continuous² c𝟛ᴺ×𝟛ᴺ c𝟛ᴺ (uncurry mid)
mid-continuous≼ = ∼ⁿ→≼-continuous-𝟛ᴺ 1 0 (uncurry mid) mid-continuous

mul-continuous≼ : continuous² c𝟛ᴺ×𝟛ᴺ c𝟛ᴺ (uncurry mul)
mul-continuous≼ = ∼ⁿ→≼-continuous-𝟛ᴺ 1 0 (uncurry mul) mul-continuous
-}

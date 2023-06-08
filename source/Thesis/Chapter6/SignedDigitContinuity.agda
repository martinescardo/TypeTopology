{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt 
open import Prelude
open import NaturalsOrder
open import SignedDigit
open import DiscreteAndSeparated
open import GenericConvergentSequence hiding (max)

module SignedDigitContinuity (fe : FunExt) where

open import Codistances fe
open import Codistance fe
open import SearchableTypes fe
open sequences

_≈*_ : {X : 𝓤 ̇ } {d : ℕ}
     → ((ℕ → X) ^⟨succ d ⟩) → ((ℕ → X) ^⟨succ d ⟩)
     → (ℕ ^⟨succ d ⟩) → 𝓤 ̇
_≈*_ {𝓤} {X} {zero} = _≈_
_≈*_ {𝓤} {X} {succ d} (α , αs) (β , βs) (n , ns) = (α ≈ β) n × (αs ≈* βs) ns

_≈**_ : {X : 𝓤 ̇ } → (ℕ → (ℕ → X)) → (ℕ → (ℕ → X)) → ℕ → ℕ → 𝓤 ̇
_≈**_ {𝓤} {X} αs βs m n = (k : ℕ) → k < n → (αs k ≈ βs k) m

≈-uc-mod-of² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {d e : ℕ}
             → ((ℕ → X) ^⟨succ d ⟩ → (ℕ → Y) ^⟨succ e ⟩)
             → ℕ ^⟨succ e ⟩ → ℕ ^⟨succ d ⟩ → 𝓤 ⊔ 𝓥 ̇
≈-uc-mod-of² f ε δ = ∀ α β → (α ≈* β) δ → (f α ≈* f β) ε

≈-continuous² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {d e : ℕ}
              → ((ℕ → X) ^⟨succ d ⟩ → (ℕ → Y) ^⟨succ e ⟩ ) → 𝓤 ⊔ 𝓥 ̇
≈-continuous² f = ∀ ε → Σ (≈-uc-mod-of² f ε)

≈-uc-mod-of : {X : 𝓤 ̇ } {d : ℕ}
            → ((ℕ → X) ^⟨succ d ⟩ → 𝓥 ̇ )
            → ℕ ^⟨succ d ⟩ → 𝓤 ⊔ 𝓥 ̇
≈-uc-mod-of p δ = ∀ α β → (α ≈* β) δ → p α → p β

≈-continuous : {X : 𝓤 ̇ } {d : ℕ}
             → ((ℕ → X) ^⟨succ d ⟩ → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
≈-continuous p = Σ (≈-uc-mod-of p)

≈**-uc-mod-of² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {d : ℕ}
              → ((ℕ → (ℕ → X)) → (ℕ → Y) ^⟨succ d ⟩)
              → ℕ ^⟨succ d ⟩ → ℕ → ℕ → 𝓤 ⊔ 𝓥 ̇
≈**-uc-mod-of² f ε δ₁ δ₂ = ∀ αs βs → (αs ≈** βs) δ₁ δ₂ → (f αs ≈* f βs) ε

≈**-continuous² : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {d : ℕ}
               → ((ℕ → (ℕ → X)) → (ℕ → Y) ^⟨succ d ⟩) → 𝓤 ⊔ 𝓥 ̇ 
≈**-continuous² f = ∀ ε → Σ (δs , δ) ꞉ (ℕ × ℕ) , (≈**-uc-mod-of² f ε δs δ)

vec-repeat : {X : 𝓤 ̇ } {n : ℕ} → X → X ^⟨succ n ⟩
vec-repeat {𝓤} {X} {0} x = x
vec-repeat {𝓤} {X} {succ n} x = x , vec-repeat x

vec-max : {n : ℕ} → ℕ ^⟨succ n ⟩ → ℕ
vec-max {0} x = x
vec-max {succ n} (x , xs) = max x (vec-max xs)

max⊏ : (k n m : ℕ) → k ⊏ under n → k ⊏ under (max n m)
max⊏ k (succ n) zero k⊏n = k⊏n
max⊏ zero (succ n) (succ m) k⊏n = refl
max⊏ (succ k) (succ n) (succ m) k⊏n = max⊏ k n m k⊏n

max≼ : (n m : ℕ) (v : ℕ∞)
     → under (max n m) ≼ v
     → under n ≼ v
     × under m ≼ v
max≼ n m v maxnm≼v
 = (λ k p → maxnm≼v k (max⊏ k n m p))
 , (λ k q → maxnm≼v k
     (transport (λ - → k ⊏ under -)
       (max-comm m n) (max⊏ k m n q)))

≈*→≼ : {X : 𝓤 ̇ } (dˣ : is-discrete X)
     → (n : ℕ) (x y : (ℕ → X) ^⟨succ n ⟩)
     → (ε : ℕ) → (x ≈* y) (vec-repeat ε)
     → under ε ≼ ×ⁿ-codistance (codistance X dˣ) n x y
≈*→≼ dˣ 0 = ≈→≼ dˣ
≈*→≼ {𝓤} {X} dˣ (succ n) (x , xs) (y , ys) ε (x≈y , xs≈ys)
 = ×-codistance-min
     (codistance X dˣ)
     (×ⁿ-codistance (codistance X dˣ) n)
     (under ε) x y xs ys
     (≈→≼ dˣ x y ε x≈y)
     (≈*→≼ dˣ n xs ys ε xs≈ys)

≼→≈* : {X : 𝓤 ̇ } (dˣ : is-discrete X)
     → (n : ℕ) (x y : (ℕ → X) ^⟨succ n ⟩)
     → (ε : ℕ)
     → under ε ≼ ×ⁿ-codistance
                   (codistance X dˣ) n x y
     → (x ≈* y) (vec-repeat ε)
≼→≈* dˣ 0 = ≼→≈ dˣ
≼→≈* {𝓤} {X} dˣ (succ n) (x , xs) (y , ys) ε ε≼cxy
 = ≼→≈ dˣ x y ε (pr₁ γ)
 , ≼→≈* dˣ n xs ys ε (pr₂ γ)
 where
   γ = ×-codistance-min'
         (codistance X dˣ)
         (×ⁿ-codistance (codistance X dˣ) n)
         (under ε) x y xs ys
         ε≼cxy

≼→≈*' : {X : 𝓤 ̇ } (dˣ : is-discrete X)
      → (d n : ℕ) (x y : (ℕ → X) ^⟨succ n ⟩)
      → (ε : ℕ) (f : ℕ ^⟨succ d ⟩ → ℕ ^⟨succ n ⟩)
      → under (vec-max (f (vec-repeat ε)))
                ≼ ×ⁿ-codistance
                    (codistance X dˣ) n x y
      → (x ≈* y) (f (vec-repeat ε))
≼→≈*' dˣ d 0 x y ε f = ≼→≈ dˣ x y (f (vec-repeat ε))
≼→≈*' {𝓤} {X} dˣ d (succ n) (x , xs) (y , ys) ε f δ≼cxy
 = ≼→≈ dˣ x y (pr₁ (f (vec-repeat ε)))
     (pr₁ (max≼ δ₁ δ₂ (codistance X dˣ x y) (pr₁ γ)))
 , ≼→≈*' dˣ d n xs ys ε (pr₂ ∘ f)
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

≈-continuous→≼-continuous
              : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
              → (dˣ : is-discrete X) (dʸ : is-discrete Y)
              → (d e : ℕ)
              → (f : (ℕ → X) ^⟨succ d ⟩ → (ℕ → Y) ^⟨succ e ⟩)
              → ≈-continuous² f
              → continuous²
                  (×ⁿ-codistance (codistance X dˣ) d)
                  (×ⁿ-codistance (codistance Y dʸ) e)
                  f
≈-continuous→≼-continuous {𝓤} {X} dˣ dʸ d e f ϕ ε
 = vec-max (pr₁ (ϕ (vec-repeat ε)))
 , (λ x y δ≼cxy → ≈*→≼ dʸ e (f x) (f y) ε
     (pr₂ (ϕ (vec-repeat ε)) x y
       (≼→≈*' dˣ e d x y ε (λ x → pr₁ (ϕ x)) δ≼cxy)))

div2-continuous : ≈-continuous² div2
div2-continuous zero = 0 , λ α β _ k ()
div2-continuous (succ ε) = succ (succ ε) , γ ε where
  γ : (ε : ℕ) → ≈-uc-mod-of² div2 (succ ε) (succ (succ ε))
  γ ε α β α≈β 0 * = ap (λ - → pr₁ (div2-aux - (α 1))) (α≈β 0 *)
                  ∙ ap (λ - → pr₁ (div2-aux (β 0) -)) (α≈β 1 *)
  γ (succ ε) α β α≈β (succ k) = γ ε α' β' α≈β' k
   where
    α' = pr₂ (div2-aux (α 0) (α 1)) ∶∶ (tail (tail α))
    β' = pr₂ (div2-aux (β 0) (β 1)) ∶∶ (tail (tail β))
    α≈β' : (α' ≈ β') (succ (succ ε))
    α≈β' 0 * = ap (λ - → pr₂ (div2-aux - (α 1))) (α≈β 0 *)
             ∙ ap (λ - → pr₂ (div2-aux (β 0) -)) (α≈β 1 *)
    α≈β' (succ j) = α≈β (succ (succ j))

map-continuous : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } 
               → (f : X → Y) → ≈-continuous² (map f)
map-continuous f ε = ε , λ α β α≈β k k<ε → ap f (α≈β k k<ε)

map2-continuous : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                → (f : X → X → Y) → ≈-continuous² (uncurry (map2 f))
map2-continuous f ε = (ε , ε) , λ α β α≈β k k<ε
                    → ap (λ - → f - (pr₂ α k)) (pr₁ α≈β k k<ε)
                    ∙ ap (f (pr₁ β k)) (pr₂ α≈β k k<ε)

continuou≈-∘ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {d₁ d₂ d₃ : ℕ}
             → (f : (ℕ → Y) ^⟨succ d₂ ⟩ → (ℕ → Z) ^⟨succ d₃ ⟩)
             → (g : (ℕ → X) ^⟨succ d₁ ⟩ → (ℕ → Y) ^⟨succ d₂ ⟩)
             → ≈-continuous² f  → ≈-continuous² g
             → ≈-continuous² (f ∘ g)
continuou≈-∘ f g ϕf ϕg ε
 = pr₁ (ϕg (pr₁ (ϕf ε)))
 , λ α β α≈β
 → pr₂ (ϕf ε) (g α) (g β)
    (pr₂ (ϕg (pr₁ (ϕf ε))) α β α≈β)

neg-continuous : ≈-continuous² neg
neg-continuous = map-continuous compl

mid-continuous : ≈-continuous² (uncurry mid)
mid-continuous = continuou≈-∘ div2 (uncurry add2)
                   div2-continuous (map2-continuous _+𝟛_)

bigMid-continuous : ≈**-continuous² bigMid'
bigMid-continuous ε = δs ε , γ ε where
  δs₁ : ℕ → ℕ
  δs₁ 0 = 0
  δs₁ (succ ε) = succ (succ (succ (δs₁ ε)))
  δs₂ : ℕ → ℕ
  δs₂ 0 = 0
  δs₂ (succ ε) = succ (succ ε)
  δs : ℕ → ℕ × ℕ
  δs ε = δs₁ ε , δs₂ ε
  pr₁δs< : (n : ℕ) → pr₁ (δs n) < pr₁ (δs (succ n))
  pr₁δs< zero = *
  pr₁δs< (succ n) = pr₁δs< n
  γ : (ε : ℕ) → ≈**-uc-mod-of² bigMid' ε (pr₁ (δs ε)) (pr₂ (δs ε))
  γ (succ ε) αs βs αs≈βs 0 k<ε
    = ap (λ - → (- +𝟛 -) +𝟝 (αs 0 1 +𝟛 αs 1 0)) (αs≈βs 0 * 0 *)
    ∙ ap (λ - → (βs 0 0 +𝟛 βs 0 0) +𝟝 (- +𝟛 αs 1 0)) (αs≈βs 0 * 1 *)
    ∙ ap (λ - → (βs 0 0 +𝟛 βs 0 0) +𝟝 (βs 0 1 +𝟛 -)) (αs≈βs 1 * 0 *)
  γ 1 αs βs αs≈βs (succ k) ()
  γ (succ (succ ε)) αs βs αs≈βs (succ k) x₁
   = γ (succ ε) αs' βs' αs≈βs' k x₁
   where
    αs' = mid (tail (tail (αs 0))) (tail (αs 1)) ∶∶ tail (tail αs) 
    βs' = mid (tail (tail (βs 0))) (tail (βs 1)) ∶∶ tail (tail βs)
    αs≈βs' : (αs' ≈** βs') (pr₁ (δs (succ ε))) (pr₂ (δs (succ ε)))
    αs≈βs' zero x i x₁
     = pr₂ (mid-continuous (pr₁ (δs (succ ε))))
         (tail (tail (αs 0)) , tail (αs 1))
         (tail (tail (βs 0)) , tail (βs 1))
         ((λ k₁ x₃ → αs≈βs 0 * (succ (succ k₁)) x₃) ,
          (λ k₁ x₃ → αs≈βs 1 * (succ k₁) (<-trans (succ k₁) (succ (succ k₁)) (pr₁ (δs (succ (succ ε)))) (<-succ k₁) x₃))) i x₁
    αs≈βs' (succ k) x i x₄ = αs≈βs (succ (succ k)) x i
                               (<-trans i (pr₁ (δs (succ ε))) (pr₁ (δs (succ (succ ε)))) x₄ (pr₁δs< (succ ε)))

div4-continuous : ≈-continuous² div4
div4-continuous zero = 0 , λ α β _ k ()
div4-continuous (succ ε) = succ (succ ε) , γ ε where
  γ : (ε : ℕ) → ≈-uc-mod-of² div4 (succ ε) (succ (succ ε))
  γ ε α β α≈β 0 * = ap (λ - → pr₁ (div4-aux - (α 1))) (α≈β 0 *)
                  ∙ ap (λ - → pr₁ (div4-aux (β 0) -)) (α≈β 1 *)
  γ (succ ε) α β α≈β (succ k) = γ ε α' β' α≈β' k
   where
    α' = pr₂ (div4-aux (α 0) (α 1)) ∶∶ (tail (tail α))
    β' = pr₂ (div4-aux (β 0) (β 1)) ∶∶ (tail (tail β))
    α≈β' : (α' ≈ β') (succ (succ ε))
    α≈β' 0 * = ap (λ - → pr₂ (div4-aux - (α 1))) (α≈β 0 *)
             ∙ ap (λ - → pr₂ (div4-aux (β 0) -)) (α≈β 1 *)
    α≈β' (succ j) = α≈β (succ (succ j))  

bigMid''-continuous : ≈**-continuous² bigMid
bigMid''-continuous ε = δ , γ where
  δ : ℕ × ℕ
  δ = pr₁ (bigMid-continuous (pr₁ (div4-continuous ε)))
  γ : ≈**-uc-mod-of² bigMid ε (pr₁ δ) (pr₂ δ)
  γ αs βs αs≈βs
   = pr₂ (div4-continuous ε)
       (bigMid' αs) (bigMid' βs)
       (pr₂ (bigMid-continuous (pr₁ (div4-continuous ε)))
         αs βs αs≈βs)

mul-continuous : ≈-continuous² (uncurry mul)
mul-continuous ε = δ ε , γ ε where
  δ : ℕ → ℕ × ℕ
  δ ε = pr₂ (pr₁ (bigMid''-continuous ε))
      , pr₁ (pr₁ (bigMid''-continuous ε))
  γ : (ε : ℕ) → ≈-uc-mod-of² (uncurry mul) ε (δ ε)
  γ ε (α₁ , α₂) (β₁ , β₂) (α≈β₁ , α≈β₂)
   = pr₂ (bigMid''-continuous ε)
       (map2 digitMul α₁ (repeat α₂))
       (map2 digitMul β₁ (repeat β₂))
         (λ n n<x k k<y
         → ap (_*𝟛 α₂ k) (α≈β₁ n n<x)
         ∙ ap (β₁ n *𝟛_) (α≈β₂ k k<y))

max-< : (n m k : ℕ) → k < n + k < m → k < max n m
max-< zero (succ m) k (inr x) = x
max-< (succ n) zero k (inl x) = x
max-< (succ n) (succ m) 0 _ = *
max-< (succ n) (succ m) (succ k) = max-< n m k

<ₙ-max : {P : ℕ → 𝓤 ̇ } (n m : ℕ) → <ₙ P (max n m) → <ₙ P n × <ₙ P m
<ₙ-max n m f = (λ k k<n → f k (max-< n m k (inl k<n)))
             , (λ k k<m → f k (max-< n m k (inr k<m)))

_**⟨succ_⟩ : 𝟛ᴺ → ℕ → 𝟛ᴺ
α **⟨succ 0 ⟩ = α
α **⟨succ succ n ⟩ = mul α (α **⟨succ n ⟩)

pow-continuous : (n : ℕ) → ≈-continuous² _**⟨succ n ⟩
pow-continuous 0 = map-continuous id
pow-continuous (succ n) ε
 = max a b
 , λ α β α≈β k k<ε
 → pr₂ (mul-continuous ε)
     (α , α **⟨succ n ⟩) (β , β **⟨succ n ⟩)
     (pr₁ (<ₙ-max a b α≈β)
     , pr₂ (pow-continuous n (pr₂ (pr₁ (mul-continuous ε))))
         α β (pr₂ (<ₙ-max a b α≈β))) k k<ε
 where
   a = pr₁ (pr₁ (mul-continuous ε))
   b = pr₁ (pow-continuous n (pr₂ (pr₁ (mul-continuous ε))))

c𝟛ᴺ : 𝟛ᴺ → 𝟛ᴺ → ℕ∞
c𝟛ᴺ = codistance 𝟛 𝟛-is-discrete

c𝟛ᴺ×𝟛ᴺ : (𝟛ᴺ × 𝟛ᴺ) → (𝟛ᴺ × 𝟛ᴺ) → ℕ∞ 
c𝟛ᴺ×𝟛ᴺ = ×-codistance c𝟛ᴺ c𝟛ᴺ

≈→≼-continuous-𝟛ᴺ = ≈-continuous→≼-continuous 𝟛-is-discrete 𝟛-is-discrete

neg-continuous≼ : continuous² c𝟛ᴺ c𝟛ᴺ neg
neg-continuous≼ = ≈→≼-continuous-𝟛ᴺ 0 0 neg neg-continuous

mid-continuous≼ : continuous² c𝟛ᴺ×𝟛ᴺ c𝟛ᴺ (uncurry mid)
mid-continuous≼ = ≈→≼-continuous-𝟛ᴺ 1 0 (uncurry mid) mid-continuous

mul-continuous≼ : continuous² c𝟛ᴺ×𝟛ᴺ c𝟛ᴺ (uncurry mul)
mul-continuous≼ = ≈→≼-continuous-𝟛ᴺ 1 0 (uncurry mul) mul-continuous

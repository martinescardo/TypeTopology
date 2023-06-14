\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import Notation.Order
open import Naturals.Order

module TWA.Thesis.Chapter2.Vectors where

data Vec (A : 𝓤 ̇ ) : ℕ → 𝓤 ̇  where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

pattern [_] x = x ∷ []

head : {A : 𝓤 ̇ } {n : ℕ} → Vec A (succ n) → A
head (x ∷ _) = x

vec-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {n : ℕ}
        → (A → B) → Vec A n → Vec B n
vec-map f [] = []
vec-map f (x ∷ v) = f x ∷ vec-map f v

vec-map-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
          → {n : ℕ}
          → (f : X → Y) → (g : Y → Z)
          → (xs : Vec X n)
          → vec-map (g ∘ f) xs ＝ vec-map g (vec-map f xs)
vec-map-∼ f g [] = refl
vec-map-∼ f g (x ∷ xs) = ap (g (f x) ∷_) (vec-map-∼ f g xs)

vec-map₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
         → Vec (X → Y) n → Vec X n → Vec Y n
vec-map₂ [] [] = []
vec-map₂ (x ∷ χs) (k ∷ ks) = x k ∷ vec-map₂ χs ks

vec-satisfy : {X : 𝓤 ̇ } {n : ℕ} → (X → 𝓦 ̇ ) → Vec X n → 𝓦 ̇ 
vec-satisfy p [] = 𝟙
vec-satisfy p (x ∷ xs) = p x × vec-satisfy p xs

pairwise₂ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ} (p : X → Y → 𝓦 ̇ )
          → Vec X n → Vec Y n → 𝓦 ̇
pairwise₂ p []       []       = 𝟙
pairwise₂ p (x ∷ xs) (y ∷ ys) = p x y × pairwise₂ p xs ys

vec-map₂-∼ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {n : ℕ}
           → (f : Y → Z) (gs : Vec (X → Y) n)
           → (xs : Vec X n)
           → vec-map f (vec-map₂ gs xs)
           ＝ vec-map₂ (vec-map (f ∘_) gs) xs
vec-map₂-∼ f [] [] = refl
vec-map₂-∼ f (g ∷ gs) (x ∷ xs) = ap (f (g x) ∷_) (vec-map₂-∼ f gs xs)

pairwise₂-extend : {X : 𝓤 ̇ } {Y : 𝓥  ̇ } {Z : 𝓣  ̇ } {n : ℕ}
                 → (p₁ : X → 𝓦  ̇ )
                 → (p₂ : Y → Y → 𝓦'  ̇ )
                 → (p₃ : Z → Z → 𝓣'  ̇ )
                 → (f : X → Y → Z)
                 → (∀ x → p₁ x → ∀ i j → p₂ i j → p₃ (f x i) (f x j))
                 → (xs : Vec X n)
                 → (is : Vec Y n) (js : Vec Y n)
                 → vec-satisfy p₁ xs
                 → pairwise₂ p₂ is js
                 → pairwise₂ p₃ (vec-map₂ (vec-map f xs) is)
                                (vec-map₂ (vec-map f xs) js)
pairwise₂-extend p₁ p₂ p₃ f g [] [] [] _ x = ⋆
pairwise₂-extend p₁ p₂ p₃ f g
                 (x ∷ xs) (i ∷ is) (j ∷ js) (px , pxs) (pij , pisjs)
 = g x px i j pij , pairwise₂-extend p₁ p₂ p₃ f g xs is js pxs pisjs

vec-satisfy₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
             → (p : Y → 𝓦 ̇ )
             → (f : X → Y)
             → (∀ x → p (f x))
             → (xs : Vec X n)
             → vec-satisfy p (vec-map f xs)
vec-satisfy₁ p f Πp [] = ⋆
vec-satisfy₁ p f Πp (x ∷ xs) = Πp x , (vec-satisfy₁ p f Πp xs)

vec-satisfy-preserved-by : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                         → {n : ℕ} (xs : Vec (Y → X) n) → (ks : Vec Y n) 
                         → (p : X → 𝓦 ̇ )
                         → vec-satisfy (λ x → ∀ (n : Y) → p (x n)) xs
                         → vec-satisfy p (vec-map₂ xs ks)
vec-satisfy-preserved-by [] [] p ⋆ = ⋆
vec-satisfy-preserved-by (x ∷ xs) (k ∷ ks) p (px , pxs)
 = px k , vec-satisfy-preserved-by xs ks p pxs

_+++_ : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → X → Vec X (succ n)
[] +++ x = [ x ]
(h ∷ v) +++ x = h ∷ (v +++ x)

_!!_ : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → (k : ℕ) → k < n → X
((x ∷ v) !! zero) k<n = x
((x ∷ v) !! succ k) k<n = (v !! k) k<n

!!-helper : {X : 𝓤 ̇ } {n : ℕ} → (v : Vec X n) → (k₁ k₂ : ℕ)
          → (k₁<n : k₁ <ℕ n) (k₂<n : k₂ <ℕ n)
          → k₁ ＝ k₂
          → (v !! k₁) k₁<n ＝ (v !! k₂) k₂<n
!!-helper (x ∷ v) zero .zero k₁<n k₂<n refl = refl
!!-helper (x ∷ v) (succ k) .(succ k) k₁<n k₂<n refl
 = !!-helper v k k k₁<n k₂<n refl

!!-prop : {X : 𝓤 ̇ } (n : ℕ) → (xs : Vec X n)
        → (k₁ k₂ : ℕ) → k₁ ＝ k₂
        → (k₁<n : k₁ <ℕ n) (k₂<n : k₂ <ℕ n)
        → (xs !! k₁) k₁<n ＝ (xs !! k₂) k₂<n
!!-prop n xs k k refl k₁<n k₂<n = ap (xs !! k) (<-is-prop-valued k n k₁<n k₂<n)

fst lst : {X : 𝓤 ̇ } {n : ℕ} → Vec X (succ n) → X
fst xs = (xs !! 0) ⋆
lst {n = n} xs = (xs !! n) (<-succ n)

drop-fst drop-lst : {X : 𝓤 ̇ } {n : ℕ} → Vec X (succ n) → Vec X n
drop-fst (x ∷ xs) = xs
drop-lst (x ∷ []) = []
drop-lst (x ∷ (y ∷ xs)) = x ∷ drop-lst (y ∷ xs)

inner : {X : 𝓤 ̇ } {n : ℕ} → Vec X (succ (succ n)) → Vec X n
inner = drop-fst ∘ drop-lst

pairwise pairwise-r : {X : 𝓤 ̇ } {n : ℕ}
                    → Vec X (succ n) → (p : X → X → 𝓥 ̇ ) → 𝓥 ̇
pairwise {𝓤} {𝓥} {X} {n} v p
 = (k : ℕ) → (k<n : k <ℕ n) → (k<sn : k <ℕ succ n)
 → p ((v !! k) k<sn) ((v !! succ k) k<n)

pairwise-r {𝓤} {𝓥} {X} {n} v p
 = (k : ℕ) → (k<n : k <ℕ n) → (k<sn : k <ℕ succ n)
 → p ((v !! succ k) k<n) ((v !! k) k<sn)

sigma-witness vector-witness : {X : 𝓤 ̇ } → (p : X → X → 𝓤 ̇ ) → X → X → ℕ → 𝓤 ̇ 

sigma-witness {𝓤} {X} p x y 0
 = p x y 
sigma-witness {𝓤} {X} p x y (succ n)
 = Σ z ꞉ X , (p x z) × (sigma-witness p z y n)

vector-witness {𝓤} {X} p x y n
 = Σ xs ꞉ Vec X (succ (succ n))
 , (fst xs ＝ x)
 × (lst xs ＝ y)
 × pairwise xs p

sigma→vector-witness : {X : 𝓤 ̇ } → (p : X → X → 𝓤 ̇ ) → (x y : X) (n : ℕ)
                     → sigma-witness p x y n → vector-witness p x y n
sigma→vector-witness p x y zero η
 = xs , refl , refl , γ
 where
  xs = x ∷ [ y ]
  γ : pairwise xs p
  γ zero ⋆ ⋆ = η
sigma→vector-witness p x y (succ n) (z , η , θ)
 = xs , refl , pr₁ (pr₂ (pr₂ IH)) , γ
 where
  IH = sigma→vector-witness p z y n θ
  xs = x ∷ pr₁ IH
  γ : pairwise xs p
  γ zero k<n k<sn = transport (p x) (pr₁ (pr₂ IH) ⁻¹) η
  γ (succ k) k<n k<sn = pr₂ (pr₂ (pr₂ IH)) k k<n k<sn

vector→sigma-witness : {X : 𝓤 ̇ } → (p : X → X → 𝓤 ̇ ) → (x y : X) (n : ℕ)
                     → vector-witness p x y n → sigma-witness p x y n
vector→sigma-witness p x y zero ((x ∷ (y ∷ [])) , refl , refl , w) = w 0 ⋆ ⋆
vector→sigma-witness p x y (succ n) ((x ∷ (z ∷ xs)) , refl , t , w)
 = z , w 0 ⋆ ⋆ , vector→sigma-witness p z y n ((z ∷ xs) , refl , t , w ∘ succ)

reverse : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → Vec X n
reverse [] = []
reverse (x ∷ xs) = reverse xs +++ x

reverse' : {X : 𝓤 ̇ } {n : ℕ} → Vec X n → Vec X n
reverse' [] = []
reverse' (x ∷ []) = [ x ]
reverse' (x ∷ (y ∷ xs)) = lst (x ∷ (y ∷ xs)) ∷ reverse (drop-lst (x ∷ (y ∷ xs)))

fst-++ : {X : 𝓤 ̇ } {n : ℕ} → (x : X) (xs : Vec X (succ n))
       → fst (xs +++ x) ＝ fst xs
fst-++ {𝓤} {X} {n} x (y ∷ xs) = refl

lst-++ : {X : 𝓤 ̇ } {n : ℕ} → (x : X) (xs : Vec X n)
       → lst (xs +++ x) ＝ x
lst-++ {𝓤} {X} {0}      x []        = refl
lst-++ {𝓤} {X} {succ n} x (y ∷ xs) = lst-++ x xs

reverse-fst-becomes-lst : {X : 𝓤 ̇ } {n : ℕ} → (xs : Vec X (succ n))
                        → lst (reverse xs) ＝ fst xs
reverse-fst-becomes-lst (x ∷ xs) = lst-++ x (reverse xs)

reverse-lst-becomes-fst : {X : 𝓤 ̇ } {n : ℕ} → (xs : Vec X (succ n))
                        → fst (reverse xs) ＝ lst xs
reverse-lst-becomes-fst (x ∷ []) = refl
reverse-lst-becomes-fst (x ∷ (y ∷ xs)) = fst-++ x (reverse (y ∷ xs))
                                       ∙ reverse-lst-becomes-fst (y ∷ xs)

_−_ : (n k : ℕ) → k ≤ℕ n → ℕ
(n − zero) _ = n
(succ n − succ k) = (n − k)

−-< : (n k : ℕ) → (k≤n : k <ℕ n) → (n − succ k) k≤n <ℕ n
−-< (succ n) zero k≤n = ≤-refl n
−-< (succ (succ n)) (succ zero) k≤n = ≤-succ n
−-< (succ (succ n)) (succ (succ k)) k≤n
 = <-trans ((n − succ k) k≤n) n (succ (succ n))
     (−-< n k k≤n)
     (<-trans n (succ n) (succ (succ n))
       (<-succ n)
       (<-succ (succ n)))

drop-lst-< : {X : 𝓤 ̇ } (n k : ℕ) → (k<n : k <ℕ n) (k<sn : k <ℕ (succ n))
           → (xs : Vec X  (succ n))
           → (drop-lst xs !! k) k<n
           ＝ (         xs !! k) k<sn
drop-lst-< n zero k<n k<sn (x ∷ (y ∷ xs)) = refl
drop-lst-< (succ n) (succ k) k<n k<sn (x ∷ (y ∷ xs))
 = drop-lst-< n k k<n k<sn (y ∷ xs)

drop-fst-< : {X : 𝓤 ̇ } → (n k : ℕ) → (k<n : k <ℕ n)
           → (xs : Vec X (succ n))
           → (         xs !! succ k) k<n
           ＝ (drop-fst xs !!      k) k<n
drop-fst-< n k k<n (x ∷ xs) = refl

drop-fst-++ : {X : 𝓤 ̇ } (n : ℕ) → (xs : Vec X (succ n)) (x : X)
            → drop-fst (xs +++ x) ＝ drop-fst xs +++ x
drop-fst-++ n (y ∷ xs) x = refl

drop-lst-++ : {X : 𝓤 ̇ } (n : ℕ) → (xs : Vec X (succ n)) (x : X)
            → drop-lst (x ∷ xs) ＝ (x ∷ drop-lst xs)
drop-lst-++ n (y ∷ xs) x = refl

reverse-drop : {X : 𝓤 ̇ } (n : ℕ) → (xs : Vec X (succ n))
             → reverse (drop-lst xs) ＝ drop-fst (reverse xs)
reverse-drop zero (x ∷ []) = refl
reverse-drop (succ n) (x ∷ xs)
 = ap reverse (drop-lst-++ n xs x)
 ∙ ap (_+++ x) (reverse-drop n xs)
 ∙ drop-fst-++ n (reverse xs) x ⁻¹

reverse-minus-becomes-k : {X : 𝓤 ̇ } {n : ℕ} → (xs : Vec X n)
                        → (k : ℕ) → (k<n : k <ℕ n)
                        → (reverse xs !! k) k<n
                        ＝ (xs !! (n − succ k) k<n) (−-< n k k<n)
reverse-minus-becomes-k (x ∷ xs) 0 k<n = reverse-lst-becomes-fst (x ∷ xs)
reverse-minus-becomes-k {𝓤} {X} {succ (succ n)} (x ∷ xs) (succ k) k<n
 = drop-fst-< (succ n) k k<n (reverse xs +++ x)
 ∙ ap (λ - → (- !! k) k<n) (reverse-drop (succ n) (x ∷ xs) ⁻¹)
 ∙ reverse-minus-becomes-k {𝓤} {X} {succ n} (drop-lst (x ∷ xs)) k k<n
 ∙ drop-lst-< (succ n) ((n − k) k<n) (−-< (succ n) k k<n)
     (−-< (succ (succ n)) (succ k) k<n) (x ∷ xs) 

−-lemma : (n k : ℕ) → (k<sn : k <ℕ succ n) → (k<n : k <ℕ n)
        → (n − k) k<sn ＝ succ ((n − succ k) k<n)
−-lemma (succ n) zero k<sn k<n = refl
−-lemma (succ n) (succ k) k<sn k<n = −-lemma n k k<sn k<n

reverse-pairwise : {X : 𝓤 ̇ } {n : ℕ} → (p q : X → X → 𝓤 ̇ )
                 → ((x y : X) → p x y → q y x)
                 → (xs : Vec X (succ n))
                 → pairwise xs p
                 → pairwise (reverse xs) q
reverse-pairwise {𝓤} {X} {n} p q f xs w k k<n k<sn
 = transport (q _) (reverse-minus-becomes-k xs (succ k) k<n ⁻¹)
     (transport (λ - → (q -) _) (reverse-minus-becomes-k xs k k<sn ⁻¹)
       (f _ _ (transport (p _) (γ ⁻¹)
                 (w _ (−-< n k k<n) (−-< (succ n) (succ k) k<n)))))
 where
   γ : (xs !! (n − k) k<sn) (−-< (succ n) k k<sn)
     ＝ (xs !! succ ((n − succ k) k<n)) (−-< n k k<n)
   γ = !!-prop (succ n) xs ((n − k) k<sn) (succ ((n − succ k) k<n))
         (−-lemma n k k<sn k<n)
         (−-< (succ n) k k<sn) (−-< n k k<n)
 
vector-witness→inv : {X : 𝓤 ̇ } → (p q : X → X → 𝓤 ̇ )
                   → ((x y : X) → p x y → q y x)
                   → (x y : X) (n : ℕ)
                   → vector-witness p x y n
                   → vector-witness q y x n
vector-witness→inv p q f x y n (xs , s , t , u)
 = reverse xs
 , (reverse-lst-becomes-fst xs ∙ t)
 , (reverse-fst-becomes-lst xs ∙ s)
 , reverse-pairwise p q f xs u

sigma-witness→inv : {X : 𝓤 ̇ } → (p q : X → X → 𝓤 ̇ )
                  → ((x y : X) → p x y → q y x)
                  → (x y : X) (n : ℕ)
                  → sigma-witness p x y n
                  → sigma-witness q y x n
sigma-witness→inv p q f x y n
 = (vector→sigma-witness q y x n)
 ∘ (vector-witness→inv p q f x y n)
 ∘ (sigma→vector-witness p x y n)


\end{code}

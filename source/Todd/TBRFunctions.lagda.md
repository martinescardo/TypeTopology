```agda

{-# OPTIONS --allow-unsolved-metas #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.CanonicalMap
open import Notation.Order
open import DedekindReals.Integers.Integers
open import DedekindReals.Integers.Addition
open import DedekindReals.Integers.Order
open import DedekindReals.Integers.Multiplication
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Multiplication renaming (_*_ to _*ℕ_)
open import DedekindReals.Integers.Negation
open import UF.Base
open import UF.FunExt
open import UF.Powerset hiding (𝕋)
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Quotient
open import Naturals.Order renaming (max to maxℕ)

module Todd.TBRFunctions
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
 where

open import Todd.TBRDyadicReals pt fe pe sq
open import Todd.BelowAndAbove fe using (below-implies-below' ; _below'_ ; below'-implies-below)
open import Todd.DyadicReals pe pt fe
open import Todd.RationalsDyadic fe
open import Todd.TernaryBoehmRealsPrelude fe
open import Todd.TernaryBoehmReals pt fe pe sq hiding (ι ; _≤_≤_)
open OrderProperties DyOrPr
open DyadicProperties Dp
open PropositionalTruncation pt
```

```agda
dist : ℤ → ℤ → ℕ
dist x y = abs (x - y)

dist-ref : (x : ℤ) → dist x x ＝ 0
dist-ref = {!!}

dist-sym : (x y : ℤ) → dist x y ＝ dist y x
dist-sym = {!!}

dist-+ : (x y z : ℤ) → dist x y ＝ dist (x + z) (y + z)
dist-+ = {!!}

dist-− : (x y : ℤ) → dist x y ＝ dist (- x) (- y)
dist-− = {!!}

```


```agda
data Vec (A : 𝓤 ̇ ) : ℕ → 𝓤 ̇  where
  []  : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

vec-map : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {n : ℕ} → (A → B) → Vec A n → Vec B n
vec-map f [] = []
vec-map f (x ∷ v) = f x ∷ vec-map f v

pairwise-P : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {n : ℕ}
           → (P : X → X → Y → 𝓦 ̇ )
           → Vec X n → Vec X n → Vec Y n → 𝓤 ⊔ 𝓥 ⊔ 𝓦   ̇
pairwise-P P [] [] [] = 𝟙
pairwise-P P (a ∷ as) (b ∷ bs) (δ ∷ δs)
 = (P a b δ) × pairwise-P P as bs δs
```

```agda
_near_ : ℤ → ℤ → 𝓤₀ ̇
x near y = dist x y ≤ℕ 2

near-is-prop : (x y : ℤ) → is-prop (x near y)
near-is-prop = {!!}

dec-near-is-prop : (x y : ℤ) → is-prop (decidable (x near y))
dec-near-is-prop = {!!}

near-ref : (x : ℤ) → x near x
near-ref x = transport (_≤ 2) (dist-ref x ⁻¹) ⋆

abs-neg-eq-pos : (x : ℤ) → abs x ＝ abs (- x)
abs-neg-eq-pos (pos zero) = refl
abs-neg-eq-pos (pos (succ x)) = refl
abs-neg-eq-pos (negsucc x) = refl

near-sym : (x y : ℤ) → x near y → y near x
near-sym x y p = transport (_≤ 2) (dist-sym x y) p

near-¬-sym : (x y : ℤ) → ¬ (x near y) → ¬ (y near x)
near-¬-sym x y f p = f (transport (_≤ 2) (dist-sym y x) p)

near-decidable : (x y : ℤ) → decidable (x near y)
near-decidable x y = ≤-decidable (abs (x −ℤ y)) 2

open import CoNaturals.GenericConvergentSequence
-- open import CoNaturals.CoNaturals fe

psc'' : (x y : 𝕋) → ((n : ℤ) → decidable ((pr₁ x n) near (pr₁ y n)) → 𝟚)
psc'' x y n (inl _) = ₁
psc'' x y n (inr _) = ₀

psc' : (x y : 𝕋) → (ℤ → 𝟚)
psc' x y n = psc'' x y n (near-decidable (pr₁ x n) (pr₁ y n))

psc'-conv : (x y : 𝕋) → (n : ℤ) → (pr₁ x n) near (pr₁ y n) → psc' x y n ＝ ₁
psc'-conv x y n p = ap (psc'' x y n)
                      (dec-near-is-prop (pr₁ x n) (pr₁ y n)
                        (≤-decidable (abs (pr₁ x n + (- pr₁ y n))) 2) (inl p))

psc'-¬-conv : (x y : 𝕋) → (n : ℤ) → ¬ ((pr₁ x n) near (pr₁ y n)) → psc' x y n ＝ ₀
psc'-¬-conv x y n f = ap (psc'' x y n)
                        (dec-near-is-prop (pr₁ x n) (pr₁ y n)
                          (≤-decidable (abs (pr₁ x n + (- pr₁ y n))) 2) (inr f))

psc'-eic : (x : 𝕋) → (n : ℤ) → psc' x x n ＝ ₁
psc'-eic x n = psc'-conv x x n (near-ref (pr₁ x n))

psc'-ice : (x y : 𝕋) → (n : ℤ) → psc' x y n ＝ ₁ → ⟦ x ⟧ ＝ ⟦ y ⟧
psc'-ice x y n p = {!!} -- should be

psc'-sym : (x y : 𝕋) → (n : ℤ) → psc' x y n ＝ psc' y x n
psc'-sym x y n = Cases (near-decidable (pr₁ x n) (pr₁ y n))
                   (λ  xny → psc'-conv   x y n  xny ∙ psc'-conv   y x n (near-sym   (pr₁ x n) (pr₁ y n)  xny) ⁻¹)
                   (λ ¬xny → psc'-¬-conv x y n ¬xny ∙ psc'-¬-conv y x n (near-¬-sym (pr₁ x n) (pr₁ y n) ¬xny) ⁻¹)

psc'-dsc₁ : (x y : 𝕋) → (n : ℤ) → psc' x y n ＝ ₁ → psc' x y (predℤ n) ＝ ₁
psc'-dsc₁ x y n p = {!!} -- yes because distance between bricks gets smaller going up

psc'-dsc₀ : (x y : 𝕋) → (n : ℤ) → psc' x y n ＝ ₀ → psc' x y (succℤ n) ＝ ₀
psc'-dsc₀ x y n p = {!!} -- yes because distance between bricks gets bigger going down

psc'-pse : (x y z : 𝕋) → (n : ℤ) → psc' x y n ＝ ₁ → psc' y z n ＝ ₁ → psc' x z ((predℤ ∘ predℤ) n) ＝ ₁
psc'-pse x y z n = {!!} -- yes, max distance between x/y = 4, then 3, then 2

psc-with-starting-point' : (x y : 𝕋) → ℤ → (ℕ → 𝟚)
psc-with-starting-point' x y s k = psc' x y (s +pos k)

psc-with-starting-point : (x y : 𝕋) → ℤ → ℕ∞
psc-with-starting-point x y s = psc-with-starting-point' x y s
                              , λ i → {!psc'-dsc!}

continuous : {n : ℕ} → (Vec 𝕋 n → 𝕋) → 𝓤₀ ̇
continuous {n} f = (xs ys : Vec 𝕋 n)
                 → (ε : ℤ)
                 → Σ δs ꞉ Vec ℤ n
                 , (pairwise-P (λ x y δ → (pr₁ x δ) near (pr₁ y δ)) xs ys δs
                 → (pr₁ (f xs) ε) near (pr₁ (f ys) ε))

continuous-psc' : {n : ℕ} → (Vec 𝕋 n → 𝕋) → 𝓤₀ ̇
continuous-psc' {n} f = (xs ys : Vec 𝕋 n)
                      → (ε : ℤ)
                      → Σ δs ꞉ Vec ℤ n
                      , (pairwise-P (λ x y δ → psc' x y δ ＝ ₁) xs ys δs
                      → psc' (f xs) (f ys) ε ＝ ₁)
```

```agda
record FunctionCollection (n : ℕ) : 𝓤₁ ̇  where
 field
  F  : Vec ℝ-d n → ℝ-d
  F* : Vec 𝕋   n → 𝕋
  γ  : (xs : Vec 𝕋 n) → F (vec-map ⟦_⟧ xs) ＝ ⟦ (F* xs) ⟧
  I  : Vec (ℤ × ℤ) n → ℤ × ℤ
  ζ  : continuous F*

Constant : (r : ℝ-d) (x : 𝕋) → (ℤ × ℤ) → r ＝ ⟦ x ⟧ → FunctionCollection 0
FunctionCollection.F  (Constant r x (k , i) γ) [] = r
FunctionCollection.F* (Constant r x (k , i) γ) [] = x
FunctionCollection.γ  (Constant r x (k , i) γ) [] = γ
FunctionCollection.I  (Constant r x (k , i) γ) [] = k , i
FunctionCollection.ζ  (Constant r x (k , i) γ) [] [] ε = [] , λ _ → near-ref (pr₁ x ε)

make : {n : ℕ} → (Vec (ℤ × ℕ) n → ℤ × ℕ) → Vec ℤ[1/2] n → ℤ[1/2]
make f ds = normalise (pr₁ ki , (pos ∘ pr₂) ki) where
  ki : ℤ × ℕ
  ki = f (vec-map pr₁ ds)

minℕ : ℕ → ℕ → ℕ
minℕ 0 m = 0
minℕ (succ n) 0 = 0
minℕ (succ n) (succ m) = succ (minℕ n m)

_−ℕ_ : ℕ → ℕ → ℕ
n −ℕ zero = n
zero −ℕ succ m = 0
succ n −ℕ succ m = n −ℕ m

codeℕ→codeℤ : ℤ × ℕ → ℤ × ℤ
codeℕ→codeℤ (a , b) = a , pos b

codeℤ→codeℕ : ℤ × ℤ → ℤ × ℕ
codeℤ→codeℕ = pr₁ ∘ normalise

add-codeℕ : Vec (ℤ × ℕ) 2 → ℤ × ℕ
add-codeℕ ((a , b) ∷ ((c , d) ∷ []))
 = ((pos ∘ 2^) (d −ℕ minℕ b d) * a)
 + ((pos ∘ 2^) (b −ℕ minℕ b d) * c)
 , maxℕ b d

fun-codeℕ→codeℤ : {n : ℕ} → (Vec (ℤ × ℕ) n → ℤ × ℕ) → Vec (ℤ × ℤ) n → ℤ × ℤ
fun-codeℕ→codeℤ f = codeℕ→codeℤ ∘ f ∘ vec-map codeℤ→codeℕ

add-codeℤ : Vec (ℤ × ℤ) 2 → ℤ × ℤ
add-codeℤ = fun-codeℕ→codeℤ add-codeℕ

add-dyad : Vec ℤ[1/2] 2 → ℤ[1/2]
add-dyad = make add-codeℕ

Neg : FunctionCollection 1
FunctionCollection.F  Neg (r ∷ []) = ℝd- r
FunctionCollection.F* Neg (x ∷ []) = 𝕋-   x
FunctionCollection.γ  Neg (x ∷ []) = tbr-negation-agrees x ⁻¹
FunctionCollection.I  Neg ((k , i) ∷ []) = (predℤ (predℤ (- k)) , i)
FunctionCollection.ζ  Neg (x ∷ []) (y ∷ []) ε
 = (ε ∷ []) , (λ (xεnyε , _)
 → transport (_≤ 2) (η (pr₁ x ε) (pr₁ y ε)) xεnyε)
 where
   η : ∀ a b → dist a b ＝ dist ((- a) +negsucc 1) ((- b) +negsucc 1)
   η a b = dist-− a b ∙ dist-+ (- a) (- b) (negsucc 1)

Add : FunctionCollection 2
FunctionCollection.F  Add (r ∷ (s ∷ [])) = r ℝd+ s
FunctionCollection.F* Add (x ∷ (y ∷ [])) = x 𝕋+ y
FunctionCollection.γ  Add (x ∷ (y ∷ [])) = {!!}
FunctionCollection.I  Add = add-codeℤ
FunctionCollection.ζ  Add = {!!}

open FunctionCollection

vec-map-＝ : {n : ℕ} → {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
          → (f : Y → Z) (g : X → Y)
          → (v : Vec X n) → vec-map (f ∘ g) v ＝ vec-map f (vec-map g v)
vec-map-＝ f g [] = refl
vec-map-＝ f g (x ∷ v) = ap ((f ∘ g) x ∷_) (vec-map-＝ f g v)

vec-map-＝2 : {n : ℕ} → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
           → (f g : X → Y)
           → f ∼ g
           → (v : Vec X n) → vec-map f v ＝ vec-map g v
vec-map-＝2 f g i [] = refl
vec-map-＝2 f g i (x ∷ v) = ap (_∷ vec-map f v) (i x)
                         ∙ ap (g x ∷_) (vec-map-＝2 f g i v)

-- continuous (f : (ℕ → X) → (ℕ → Y)) ≔ (α β : ℕ → X) → (ε : ℤ)
--                              → Σ δ ꞉ ℤ , ((α ≈ β) δ → (f α) ≈ (f β) ε)

-- continuous (f : 𝕋 × 𝕋 → 𝕋) ≔ ((x₁ , y₁) (x₂ , y₂) : 𝕋 × 𝕋) → (ε : ℤ)
--                            → Σ (δx , δy) ꞉ ℤ × ℤ , ((pr₁ x₁ δx ＝ pr₁ x₂ δx) × (pr₁ y₁ δy ＝ pr₁ y₂ δy) 
--                                                  →  pr₁ (f (x₁ , y₁)) ε ＝ pr₁ (f (x₂ , y₂)) ε)

-- ∀ (x₁ , y₁) (x₂ , y₂) ε → δx ≔ ε +pos 2, δy ≔ ε +pos 2 → (x₁ + y₁) ε ＝ (x₂ + y₂) ε

--                λ x₀..xₙ → f(x₀ ... xₙ)         → [λ y₀..yₘ → g₀(y₀...yₘ) ... λ y₀..yₘ → gₙ(y₀...yₘ)]
--                                     → λ y₀..yₘ → f(g₀(y₀...yₘ).....gₙ(y₀..yₘ))
Map : {n m : ℕ} → FunctionCollection n → Vec (FunctionCollection m) n → FunctionCollection m
F  (Map f v) as = F  f (vec-map (λ g → F  g as) v)
F* (Map f v) as = F* f (vec-map (λ g → F* g as) v)
I  (Map f v) as = I  f (vec-map (λ g → I  g as) v)
γ  (Map f v) as = ap (F f)
                 (vec-map-＝2
                    (λ g → F g (vec-map ⟦_⟧ as))
                    (⟦_⟧ ∘ (λ g → F* g as))
                    (λ i → γ i as)
                    v
                ∙ vec-map-＝ ⟦_⟧ (λ g → F* g as) v)
                ∙ γ f (vec-map (λ g → F* g as) v)
ζ (Map {n} {m} f v) as bs ε = {!!} , (λ p → pr₂ IH {!!})
  where
    IH = ζ f (vec-map (λ g → F* g as) v) (vec-map (λ g → F* g bs) v) ε

-- if x δ = y δ then f x ε = f y ε

-- if g1(x) δ1 = g1(y) δ1 and g2(x) δ2 = g2(y) δ2 then f (g1(x) , g2(x)) ε = f (g1(y) , g2(y)) ε
-- if x δ'1 = y δ'1 then g1(x) δ1 = g1(y) δ1
-- if x δ'2 = y δ'2 then g2(x) δ2 = g2(y) δ2

-- need extra condition that states as long as x = y at the max precision then everything works
-- but does this hold for these functions?1

{-
ζ (Map f v) [] [] ε = [] , (λ _ → refl)
ζ (Map f [])      (a ∷ as) (b ∷ bs) ε = many ε , (λ _ → refl)
ζ (Map f (g ∷ v)) (a ∷ as) (b ∷ bs) ε
 = (hd (pr₁ fst) ∷ {!!})
 , λ (e₁ , e₂) → ap (λ - → (pr₁ -) ε) {!!}
 where
   fst = ζ g (a ∷ as) (b ∷ bs) ε
   rst = {!!}
-}
AddFuns : {n : ℕ} → FunctionCollection n → FunctionCollection n → FunctionCollection n
AddFuns f g = Map Add (f ∷ (g ∷ []))

```

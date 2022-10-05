
```agda
{-# OPTIONS --allow-unsolved-metas --exact-split --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Notation.CanonicalMap
open import Notation.Order
open import DedekindReals.Integers.Integers
open import DedekindReals.Integers.Addition
open import DedekindReals.Integers.Negation
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Quotient
open import UF.Powerset hiding (𝕋)

module Todd.BuildingBlocks
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
 where

open import Todd.RationalsDyadic fe
open import Todd.DyadicReals pe pt fe
open import Todd.TBRFunctions pt fe pe sq
open import Todd.TernaryBoehmReals pt fe pe sq hiding (ι ; _≤_≤_)
open import Todd.TBRDyadicReals pt fe pe sq
open PropositionalTruncation pt

open OrderProperties DyOrPr
open DyadicProperties Dp

head : {A : 𝓤 ̇} {n  : ℕ} → Vec A (succ n) → A
head (a ∷ _) = a

tail : {A : 𝓤 ̇} {n  : ℕ} → Vec A (succ n) → Vec A n
tail (_ ∷ as) = as

zip : {A : 𝓤 ̇} {n : ℕ} → Vec A n × Vec A n → Vec (A × A) n 
zip ([]     , [])     = []
zip (a ∷ as , b ∷ bs) = (a , b) ∷ zip (as , bs)

get-left get-right : {A : 𝓤 ̇} {n : ℕ} → Vec (A × A) n → Vec A n
get-left []            = []
get-left ((a , b) ∷ V) = a ∷ get-left V
get-right []            = []
get-right ((a , b) ∷ V) = b ∷ get-right V

unzip : {A : 𝓤 ̇} {n : ℕ} → Vec (A × A) n  → Vec A n × Vec A n
unzip V = (get-left V) , (get-right V)

zip-unzip : {A : 𝓤 ̇} {n : ℕ} → (v : Vec (A × A) n) → zip (unzip v) ＝ v
zip-unzip {𝓤} {A} {0} []                  = refl
zip-unzip {𝓤} {A} {succ n} ((a , b) ∷ vs) = ap ((a , b) ∷_) (zip-unzip vs)

pairwise-P' : {X : 𝓤 ̇} {Y : 𝓥 ̇} {n : ℕ} → (P : X → Y → 𝓦 ̇) → Vec X n → Vec Y n → 𝓦 ̇
pairwise-P' P [] []             = 𝟙 
pairwise-P' {𝓤} {𝓥} {𝓦} {X} {Y} P (a ∷ as) (b ∷ bs) = P a b × pairwise-P' { 𝓤 } { 𝓥 } { 𝓦 } { X } { Y } P as bs

_Vecℤ[1/2]<_ _Vecℤ[1/2]≤_ : {n : ℕ} → Vec ℤ[1/2] n → Vec ℤ[1/2] n → 𝓤₀ ̇
_Vecℤ[1/2]<_ = pairwise-P' _<ℤ[1/2]_ 
_Vecℤ[1/2]≤_ = pairwise-P' _≤ℤ[1/2]_

dyadic-real-lemma : {n : ℕ} → (as bs : Vec ℤ[1/2] n) (x : Vec ℝ-d n)
                     → pairwise-P' (λ a x → a < x) as x
                     → pairwise-P' (λ b x → x < b) bs x
                     → pairwise-P' (λ (a , b) x → a < x × x < b) (zip (as , bs)) x
dyadic-real-lemma {0}      [] [] [] as<x x<bs = ⋆
dyadic-real-lemma {succ n} (a ∷ as) (b ∷ bs) (x ∷ xs)  (a<x , as<xs) (x<b , xs<bs) = (a<x , x<b) , (dyadic-real-lemma {n} as bs xs as<xs xs<bs)

dyadic-real-lemma' : {n : ℕ}
                   → (asbs : Vec (ℤ[1/2] × ℤ[1/2]) n) (x : Vec ℤ[1/2] n)
                   → (pairwise-P' { 𝓤₀ } { 𝓤₁ } (λ (a , b) x → a < x × x < b) asbs (vec-map ι x))
                   → (get-left asbs Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ get-right asbs)
dyadic-real-lemma' {0}      [] []  a<x<b = ⋆ , ⋆
dyadic-real-lemma' {succ n} ((a , b) ∷ asbs) (x ∷ xs) ((a<x , x<b) , as<xs<bs) = let (p₁ , p₂) = dyadic-real-lemma' asbs xs as<xs<bs in (<-is-≤ℤ[1/2] a x a<x , p₁) , (<-is-≤ℤ[1/2] x b x<b , p₂)

vec-∈L-< : {n : ℕ} → (as : Vec ℤ[1/2] n)
                   → (x  : Vec ℤ[1/2] n)
                   → pairwise-P' (λ a x → a < x) as x
                   → pairwise-P' (λ a x → a ∈ lower-cut-of x) as (vec-map ι x)
vec-∈L-< {0}      [] [] p = ⋆
vec-∈L-< {succ n} (a ∷ as) (x ∷ xs) (a<x , as<xs) = a<x , vec-∈L-< as xs as<xs

vec-∈R-< : {n : ℕ} → (bs : Vec ℤ[1/2] n)
                   → (x  : Vec ℤ[1/2] n)
                   → pairwise-P' (λ b x → x < b) bs x
                   → pairwise-P' (λ b x → b ∈ upper-cut-of x) bs (vec-map ι x)
vec-∈R-< {0}      [] [] p = ⋆
vec-∈R-< {succ n} (b ∷ bs) (x ∷ xs) (x<b , xs<bs) = x<b , (vec-∈R-< bs xs xs<bs)

vec-∈R-<-reorder : {n : ℕ} → (bs xs : Vec ℤ[1/2] n)
                 → xs Vecℤ[1/2]< bs
                 → pairwise-P' (λ b x → x <ℤ[1/2] b) bs xs
vec-∈R-<-reorder {0}      [] [] xs<bs = ⋆
vec-∈R-<-reorder {succ n} (b ∷ bs) (x ∷ xs) (x<b , xs<bs) = x<b , (vec-∈R-<-reorder bs xs xs<bs)

generate-asbs : {n : ℕ} (v : Vec ℝ-d n) → ∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) n , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v
generate-asbs {0}      []       = ∣ [] , ⋆ ∣
generate-asbs {succ n} (v ∷ vs) = do (asbs , as<xs<bs) ← generate-asbs vs
                                     (a , a<x) ← inhabited-from-real-L v
                                     (b , x<b) ← inhabited-from-real-R v
                                     ∣ ((a , b) ∷ asbs) , ((a<x , x<b) , as<xs<bs) ∣
                                    
open import Naturals.Order renaming (max to ℕmax)

ℕmin : ℕ → ℕ → ℕ
ℕmin 0 n               = 0
ℕmin (succ m) 0        = 0
ℕmin (succ m) (succ n) = succ (ℕmin m n)

ℤmax : ℤ → ℤ → ℤ
ℤmax (pos x) (pos y)         = pos (ℕmax x y)
ℤmax (pos x) (negsucc y)     = pos x
ℤmax (negsucc x) (pos y)     = pos y
ℤmax (negsucc x) (negsucc y) = negsucc (ℕmin x y)

record Collection (n : ℕ) : {!!} ̇ where
 field
  D : Vec ℤ[1/2] (succ n) → ℤ[1/2]
  L R : Vec (ℤ[1/2] × ℤ[1/2]) (succ n) → ℤ[1/2]
  Condition-1a : (a c x d b : Vec ℤ[1/2] (succ n))
               → (a Vecℤ[1/2]≤ c) × (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d) × (d Vecℤ[1/2]≤ b)
               → (L (zip (a , b)) ≤ℤ[1/2] L (zip (c , d)))
  Condition-1b : (c x d : Vec ℤ[1/2] (succ n))
               → (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d)             
               → (L (zip (c , d)) ≤ℤ[1/2] D x)
  Condition-1c : (c x d : Vec ℤ[1/2] (succ n))
               → (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d)              
               → (D x ≤ℤ[1/2] R (zip (c , d)))
  Condition-1d : (a c x d b : Vec ℤ[1/2] (succ n))
               → (a Vecℤ[1/2]≤ c) × (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d) × (d Vecℤ[1/2]≤ b)              
               → (R (zip (c , d)) ≤ℤ[1/2] R (zip (a , d)))
               
  Condition-2 : (x : Vec ℤ[1/2] (succ n)) → (ε : ℤ[1/2]) → (0<ε : 0ℤ[1/2] <ℤ[1/2] ε) → Σ (a , b) ꞉ Vec ℤ[1/2] (succ n) × Vec ℤ[1/2] (succ n) , (a Vecℤ[1/2]< x) × (x Vecℤ[1/2]< b) × Bℤ[1/2] (L (zip (a , b))) (D x) ε 0<ε
  Condition-3 : (x : Vec ℤ[1/2] (succ n)) → (ε : ℤ[1/2]) → (0<ε : 0ℤ[1/2] <ℤ[1/2] ε) → Σ (a , b) ꞉ Vec ℤ[1/2] (succ n) × Vec ℤ[1/2] (succ n) , (a Vecℤ[1/2]< x) × (x Vecℤ[1/2]< b) × Bℤ[1/2] (R (zip (a , b))) (D x) ε 0<ε
  
 F : Vec ℝ-d (succ n) → ℝ-d
 F v = (Lc , Rc) , inhabited-l , inhabited-r , rounded-l , {!!} , is-disjoint , is-located
  where
   Lc Rc : 𝓟 ℤ[1/2] 
   Lc p = (∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , (pairwise-P' (λ (a , b) x → a < x × x < b) asbs v) × p < L asbs) , ∃-is-prop
   Rc q = (∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , (pairwise-P' (λ (a , b) x → a < x × x < b) asbs v) × R asbs < q) , ∃-is-prop
   
   inhabited-l : inhabited-left Lc
   inhabited-l = ∥∥-functor I (generate-asbs v) 
    where
     I : Σ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v
       → Σ p ꞉ ℤ[1/2] , ∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v × p < L asbs
     I (asbs , a<x<b) = (L asbs ℤ[1/2]- 1ℤ[1/2]) , ∣ asbs , a<x<b , {!L asbs - 1 < L asbs!} ∣

   inhabited-r : inhabited-right Rc
   inhabited-r = ∥∥-functor I (generate-asbs v)
    where
     I : Σ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v
       → Σ q ꞉ ℤ[1/2] , ∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v × R asbs < q
     I (asbs , a<x<b) = (R asbs ℤ[1/2]+ 1ℤ[1/2]) , ∣ asbs , a<x<b , {!R < R + 1!} ∣

   rounded-l : rounded-left Lc
   rounded-l p = ltr , rtl
    where
     ltr : ∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v × p < L asbs
         → ∃ p' ꞉ ℤ[1/2] , p < p' × (∃ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs v × p' < L asbs)
     ltr tasbs = do
                (asbs , as<xs<bs) ← tasbs
                {!!}
     rtl : {!!}
     rtl = {!!} --just density/minus1

   is-disjoint : disjoint Lc Rc
   is-disjoint p q (p<x , x<q) = {!!}
   -- p < Lab
   --       Rab' < q

   -- Lab ≤ Dx ≤ Rab
   is-located : located Lc Rc
   is-located p q p<q = {!!}
   -- 0<q-p → 

 L' R' : Vec (ℤ × ℤ) (succ n) → ℤ × ℤ
 L' = {!!}
 R' = {!!}

 F* : Vec 𝕋 (succ n) → 𝕋
 F* x = {!!} 

 dyadic-function-equiv-to-real : (x : Vec ℤ[1/2] (succ n)) → ι (D x) ＝ F (vec-map ι x)
 dyadic-function-equiv-to-real x = ℝ-d-equality-from-left-cut ltr rtl
  where
   ltr : (p : ℤ[1/2]) → p ∈ lower-cut-of (ι (D x)) → p ∈ lower-cut-of (F (vec-map ι x))
   ltr p p<Dx = by-condition-3 (Condition-2 x ε 0<ε)
    where
     ε : ℤ[1/2] 
     ε = ℤ[1/2]-abs (p ℤ[1/2]- D x)
     0<ε : 0ℤ[1/2] <ℤ[1/2] ε
     0<ε = {!!} -- positive since p<Dx
     by-condition-3 : Σ (a , b) ꞉ Vec ℤ[1/2] (succ n) × Vec ℤ[1/2] (succ n) , (a Vecℤ[1/2]< x) × (x Vecℤ[1/2]< b) × Bℤ[1/2] (L (zip (a , b))) (D x) ε 0<ε
                    → p ∈ lower-cut-of (F (vec-map ι x))
     by-condition-3 ((a , b) , a<x , x<b , distance-proof) = ∣ (zip (a , b)) , V , p<Lab ∣
      where
       I : 0ℤ[1/2] ≤ (D x ℤ[1/2]- L (zip (a , b)))
       I = {!since L ≤ D!}
       II : 0ℤ[1/2] ≤ (D x ℤ[1/2]- p)
       II = {!Since p ≤ D!}
       III : (D x ℤ[1/2]- L (zip (a , b))) < (D x ℤ[1/2]- p)
       III = {!using I, II, and distance-proof!}
       IV : (ℤ[1/2]- L (zip (a , b))) < (ℤ[1/2]- p)
       IV = {!from III!}
       p<Lab : p < L (zip (a , b))
       p<Lab = <-swap' (L (zip (a , b))) p IV
       V : pairwise-P' (λ (a , b) x → a < x × x < b) (zip (a , b)) (vec-map ι x)
       V = dyadic-real-lemma a b (vec-map ι x) (vec-∈L-< a x a<x) (vec-∈R-< b x (vec-∈R-<-reorder b x x<b))
        
   rtl : (p : ℤ[1/2]) → p ∈ lower-cut-of (F (vec-map ι x)) → p ∈ lower-cut-of (ι (D x))
   rtl p p<Fx = ∥∥-rec (∈-is-prop (lower-cut-of (ι (D x))) p) I p<Fx
    where
     I : Σ asbs ꞉ Vec (ℤ[1/2] × ℤ[1/2]) (succ n) , pairwise-P' (λ (a , b) x → a < x × x < b) asbs (vec-map ι x) × p < L asbs → p < D x
     I (asbs , a<x<b , p<Lab) = ℤ[1/2]<-≤ p (L asbs) (D x) p<Lab (transport (λ - → (L -) ≤ℤ[1/2] D x) (zip-unzip asbs) II)
      where
       II : L (zip (unzip asbs)) ≤ℤ[1/2] D x
       II = Condition-1b (get-left asbs) x (get-right asbs) (dyadic-real-lemma' asbs x a<x<b)

 ternary-boehm-function-equiv-to-real : (α : Vec 𝕋 (succ n)) → ⟦ F* α ⟧ ＝ F (vec-map ⟦_⟧ α)
 ternary-boehm-function-equiv-to-real = {!!}

neg-D : Vec ℤ[1/2] 1 → ℤ[1/2]
neg-D (x ∷ []) = ℤ[1/2]- x

neg-L : Vec (ℤ[1/2] × ℤ[1/2]) 1 → ℤ[1/2]
neg-L ((a , b) ∷ []) = ℤ[1/2]- b

neg-R : Vec (ℤ[1/2] × ℤ[1/2]) 1 → ℤ[1/2]
neg-R ((a , b) ∷ []) = ℤ[1/2]- a

neg-Condition-1a : (a c x d b : Vec ℤ[1/2] 1)
                 → (a Vecℤ[1/2]≤ c) × (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d) × (d Vecℤ[1/2]≤ b)
                 → (neg-L (zip (a , b)) ≤ℤ[1/2] neg-L (zip (c , d)))
neg-Condition-1a (a ∷ []) (c ∷ []) (x ∷ []) (d ∷ []) (b ∷ []) (a≤c , c≤x , x≤d , (d≤b , ⋆)) = ≤-swap d b d≤b

neg-Condition-1b : (c x d : Vec ℤ[1/2] 1)
                 → (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d)             
                 → (neg-L (zip (c , d)) ≤ℤ[1/2] neg-D x)
neg-Condition-1b (c ∷ []) (x ∷ []) (d ∷ []) (c≤x , (x≤d , ⋆)) = ≤-swap x d x≤d

neg-Condition-1c : (c x d : Vec ℤ[1/2] 1)
                 → (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d)              
                 → (neg-D x ≤ℤ[1/2] neg-R (zip (c , d)))
neg-Condition-1c (c ∷ []) (x ∷ []) (d ∷ []) ((c≤x , ⋆) , x≤d) = ≤-swap c x c≤x

neg-Condition-1d : (a c x d b : Vec ℤ[1/2] 1)
                 → (a Vecℤ[1/2]≤ c) × (c Vecℤ[1/2]≤ x) × (x Vecℤ[1/2]≤ d) × (d Vecℤ[1/2]≤ b)              
                 → (neg-R (zip (c , d)) ≤ℤ[1/2] neg-R (zip (a , d)))
neg-Condition-1d (a ∷ []) (c ∷ []) (x ∷ []) (d ∷ []) (b ∷ []) ((a≤c , ⋆) , c≤x , x≤d , d≤b) = ≤-swap a c a≤c
 
neg-Condition-2 : (x : Vec ℤ[1/2] 1) → (ε : ℤ[1/2]) → (0<ε : 0ℤ[1/2] <ℤ[1/2] ε)
                → Σ (a , b) ꞉ Vec ℤ[1/2] 1 × Vec ℤ[1/2] 1 , (a Vecℤ[1/2]< x) × (x Vecℤ[1/2]< b) × Bℤ[1/2] (neg-L (zip (a , b))) (neg-D x) ε 0<ε
neg-Condition-2 (x ∷ []) ε 0<ε with (no-min x) 
... | (a , a<x) with dense x (x ℤ[1/2]+ ε) (ℤ[1/2]<-+ x ε 0<ε)
... | (b , x<b , b<x+ε) = ((a ∷ []) , (b ∷ [])) , ((a<x , ⋆) , (x<b , ⋆) , goal)
 where
  l₁ : (b ℤ[1/2]- x) < ε
  l₁ = <-swap-consequence b x ε b<x+ε
  l₂ : metric b x < ε
  l₂ = transport (_< ε) (ℤ[1/2]-pos-abs x b x<b) l₁
  goal : metric (ℤ[1/2]- b) (ℤ[1/2]- x) < ε
  goal = ℤ[1/2]-metric-neg b x ε 0<ε l₂

neg-Condition-3 : (x : Vec ℤ[1/2] 1) → (ε : ℤ[1/2]) → (0<ε : 0ℤ[1/2] <ℤ[1/2] ε)
                → Σ (a , b) ꞉ Vec ℤ[1/2] 1 × Vec ℤ[1/2] 1 , (a Vecℤ[1/2]< x) × (x Vecℤ[1/2]< b) × Bℤ[1/2] (neg-R (zip (a , b))) (neg-D x) ε 0<ε
neg-Condition-3 (x ∷ []) ε 0<ε with no-max x
... | (b , x<b) with dense (x ℤ[1/2]- ε) x (ℤ[1/2]<-neg x ε 0<ε)
... | (a , x-ε<a , a<x) = ((a ∷ []) , (b ∷ [])) , (a<x , ⋆) , (x<b , ⋆) , goal
 where 
  l₁ : x < (a ℤ[1/2]+ ε)
  l₁ = ℤ[1/2]<-neg' x ε a x-ε<a
  l₂ : (x ℤ[1/2]- a) < ε
  l₂ = ℤ[1/2]<-+' x a ε l₁
  l₃ : ℤ[1/2]-abs (x ℤ[1/2]- a) < ε
  l₃ = transport (_< ε) (ℤ[1/2]-pos-abs a x a<x) l₂
  l₄ : Bℤ[1/2] a x ε 0<ε
  l₄ = ℤ[1/2]-metric-comm x a ε 0<ε l₃
  goal : (metric (ℤ[1/2]- a) (ℤ[1/2]- x)) < ε
  goal = ℤ[1/2]-metric-neg a x ε 0<ε l₄

negation-collection : Collection 0
negation-collection = record
                        { D = neg-D
                        ; L = neg-L
                        ; R = neg-R
                        ; Condition-1a = neg-Condition-1a
                        ; Condition-1b = neg-Condition-1b
                        ; Condition-1c = neg-Condition-1c
                        ; Condition-1d = neg-Condition-1d
                        ; Condition-2 = neg-Condition-2
                        ; Condition-3 = neg-Condition-3
                        }

open Collection

tbr- : 𝕋 → 𝕋
tbr- x = F* negation-collection (x ∷ [])


```

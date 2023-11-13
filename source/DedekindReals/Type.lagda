Andrew Sneap, March 2021
Updated March 2022

In this file I define the Dedekind reals, and prove that the rationals
are embedded in the reals.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Integers.Type
open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Order
open import Rationals.Type
open import UF.Base
open import UF.FunExt
open import UF.Powerset
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties

module DedekindReals.Type
         (fe : Fun-Ext)
         (pe : Prop-Ext)
         (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

inhabited-left : (L : 𝓟 ℚ) → 𝓤₀ ̇
inhabited-left L = (∃ p ꞉ ℚ , p ∈ L)

inhabited-right : (R : 𝓟 ℚ) → 𝓤₀ ̇
inhabited-right R = (∃ q ꞉ ℚ , q ∈ R)

rounded-left : (L : 𝓟 ℚ) → 𝓤₀ ̇
rounded-left L = (x : ℚ) → (x ∈ L ↔ (∃ p ꞉ ℚ , (x < p) × p ∈ L))

rounded-right : (R : 𝓟 ℚ) → 𝓤₀ ̇
rounded-right R = (x : ℚ) → x ∈ R ↔ (∃ q ꞉ ℚ , (q < x) × q ∈ R)

disjoint : (L R : 𝓟 ℚ) → 𝓤₀ ̇
disjoint L R = (p q : ℚ) → p ∈ L × q ∈ R → p < q

located : (L R : 𝓟 ℚ) → 𝓤₀ ̇
located L R = (p q : ℚ) → p < q → p ∈ L ∨ q ∈ R

isCut : (L R : 𝓟 ℚ) → 𝓤₀ ̇
isCut L R = inhabited-left L
          × inhabited-right R
          × rounded-left L
          × rounded-right R
          × disjoint L R
          × located L R

ℝ : 𝓤₁ ̇
ℝ = Σ (L , R) ꞉ 𝓟 ℚ × 𝓟 ℚ , isCut L R

subset-of-ℚ-is-set : is-set (𝓟 ℚ)
subset-of-ℚ-is-set = powersets-are-sets fe pe

inhabited-left-is-prop : (L : 𝓟 ℚ) → is-prop (inhabited-left L)
inhabited-left-is-prop L = ∃-is-prop

inhabited-right-is-prop : (R : 𝓟 ℚ) → is-prop (inhabited-right R)
inhabited-right-is-prop R = ∃-is-prop

rounded-left-a : (L : 𝓟 ℚ) → rounded-left L → (x y : ℚ) → x ≤ y → y ∈ L → x ∈ L
rounded-left-a L r x y l y-L = II (ℚ≤-split x y l)
 where
  I : (∃ p ꞉ ℚ , (x < p) × p ∈ L) → x ∈ L
  I = pr₂ (r x)
  II : (x < y) ∔ (x ＝ y) → x ∈ L
  II (inl l) = I ∣ y , (l , y-L) ∣
  II (inr r) = transport (_∈ L) (r ⁻¹) y-L

rounded-left-b : (L : 𝓟 ℚ) → rounded-left L → (x : ℚ) → x ∈ L → (∃ p ꞉ ℚ , (x < p) × p ∈ L)
rounded-left-b L r x x-L = (pr₁ (r x)) x-L

rounded-left-c : (L : 𝓟 ℚ) → rounded-left L → (x y : ℚ) → x < y → y ∈ L → x ∈ L
rounded-left-c L r x y l yL = pr₂ (r x) ∣ y , (l , yL) ∣

rounded-right-a : (R : 𝓟 ℚ) → rounded-right R → (x y : ℚ) → x ≤ y → x ∈ R → y ∈ R
rounded-right-a R r x y l x-R = II (ℚ≤-split x y l)
 where
  I : (∃ p ꞉ ℚ , (p < y) × p ∈ R) → y ∈ R
  I = pr₂ (r y)
  II : (x < y) ∔ (x ＝ y) → y ∈ R
  II (inl r) = I ∣ x , (r , x-R) ∣
  II (inr r) = transport (_∈ R) r x-R

rounded-right-b : (R : 𝓟 ℚ) → rounded-right R → (x : ℚ) → x ∈ R → (∃ q ꞉ ℚ , (q < x) × q ∈ R)
rounded-right-b R r x x-R = (pr₁ (r x)) x-R

rounded-right-c : (R : 𝓟 ℚ) → rounded-right R → (x y : ℚ) → x < y → x ∈ R → y ∈ R
rounded-right-c R r x y l xR = pr₂ (r y) ∣ x , (l , xR) ∣

rounded-left-is-prop : (L : 𝓟 ℚ) → is-prop (rounded-left L)
rounded-left-is-prop L = Π-is-prop fe δ
 where
  δ : (x : ℚ) → is-prop (x ∈ L ↔ (∃ p ꞉ ℚ , (x < p) × p ∈ L))
  δ x = ×-is-prop (Π-is-prop fe (λ _ → ∃-is-prop)) (Π-is-prop fe (λ _ → ∈-is-prop L x))

rounded-right-is-prop : (R : 𝓟 ℚ) → is-prop (rounded-right R)
rounded-right-is-prop R = Π-is-prop fe δ
 where
  δ : (x : ℚ) → is-prop (x ∈ R ↔ (∃ q ꞉ ℚ , (q < x) × q ∈ R))
  δ x = ×-is-prop (Π-is-prop fe (λ _ → ∃-is-prop)) (Π-is-prop fe (λ _ → ∈-is-prop R x))

disjoint-is-prop : (L R : 𝓟 ℚ) → is-prop (disjoint L R)
disjoint-is-prop L R = Π₃-is-prop fe (λ x y _ → ℚ<-is-prop x y)

located-is-prop : (L R : 𝓟 ℚ) → is-prop (located L R)
located-is-prop L R = Π₃-is-prop fe (λ _ _ _ → ∨-is-prop)


isCut-is-prop : (L R : 𝓟 ℚ) → is-prop (isCut L R)
isCut-is-prop L R = ×-is-prop (inhabited-left-is-prop L)
                   (×-is-prop (inhabited-right-is-prop R)
                   (×-is-prop (rounded-left-is-prop L)
                   (×-is-prop (rounded-right-is-prop R)
                   (×-is-prop (disjoint-is-prop L R)
                              (located-is-prop L R)))))

ℝ-is-set : is-set ℝ
ℝ-is-set = Σ-is-set (×-is-set subset-of-ℚ-is-set subset-of-ℚ-is-set)
            λ (L , R) → props-are-sets (isCut-is-prop L R)

lower-cut-of : ℝ → 𝓟 ℚ
lower-cut-of ((L , R) , _) = L

upper-cut-of : ℝ → 𝓟 ℚ
upper-cut-of ((L , R) , _) = R

in-lower-cut : ℚ → ℝ → 𝓤₀ ̇
in-lower-cut q ((L , R) , _) = q ∈ L

in-upper-cut : ℚ → ℝ → 𝓤₀ ̇
in-upper-cut q ((L , R) , _) = q ∈ R

ℝ-locatedness : (((L , R) , _) : ℝ) → (p q : ℚ) → p < q → p ∈ L ∨ q ∈ R
ℝ-locatedness ((L , R) , _ , _ , _ , _ , _ , located-y) = located-y

inhabited-from-real-L : (((L , R) , i) : ℝ) → inhabited-left L
inhabited-from-real-L ((L , R) , inhabited-L , _) = inhabited-L

inhabited-from-real-R : (((L , R) , i) : ℝ) → inhabited-left R
inhabited-from-real-R ((L , R) , _ , inhabited-R , _) = inhabited-R

rounded-from-real-L : (((L , R) , i) : ℝ) → rounded-left L
rounded-from-real-L ((L , R) , _ , _ , rounded-L , _) = rounded-L

rounded-from-real-R : (((L , R) , i) : ℝ) → rounded-right R
rounded-from-real-R ((L , R) , _ , _ , _ , rounded-R , _) = rounded-R

disjoint-from-real : (((L , R) , i) : ℝ) → disjoint L R
disjoint-from-real ((L , R) , _ , _ , _ , _ , disjoint , _) = disjoint

ℚ-rounded-left₁ : (y : ℚ) (x : ℚ) → x < y → Σ p ꞉ ℚ , (x < p < y)
ℚ-rounded-left₁ y x l = ℚ-dense x y l

ℚ-rounded-left₂ : (y : ℚ) (x : ℚ) → Σ p ꞉ ℚ , (x < p < y) → x < y
ℚ-rounded-left₂ y x (p , l₁ , l₂) = ℚ<-trans x p y l₁ l₂

ℚ-rounded-right₁ : (y : ℚ) (x : ℚ) → y < x → Σ q ꞉ ℚ , (q < x) × (y < q)
ℚ-rounded-right₁ y x l = I (ℚ-dense y x l)
 where
  I : Σ q ꞉ ℚ , (y < q) × (q < x)
    → Σ q ꞉ ℚ , (q < x) × (y < q)
  I (q , l₁ , l₂) = q , l₂ , l₁

ℚ-rounded-right₂ : (y : ℚ) (x : ℚ) → Σ q ꞉ ℚ , (q < x) × (y < q) → y < x
ℚ-rounded-right₂ y x (q , l₁ , l₂) = ℚ<-trans y q x l₂ l₁

open import Notation.Order

_ℚ<ℝ_  : ℚ → ℝ → 𝓤₀ ̇
p ℚ<ℝ x = p ∈ lower-cut-of x

_ℝ<ℚ_  : ℝ → ℚ → 𝓤₀ ̇
x ℝ<ℚ q = q ∈ upper-cut-of x

instance
 Strict-Order-ℚ-ℝ : Strict-Order ℚ ℝ
 _<_ {{Strict-Order-ℚ-ℝ}} = _ℚ<ℝ_

 Strict-Order-ℝ-ℚ : Strict-Order ℝ ℚ
 _<_ {{Strict-Order-ℝ-ℚ}} = _ℝ<ℚ_

 Strict-Order-Chain-ℚ-ℝ-ℚ : Strict-Order-Chain ℚ ℝ ℚ _<_ _<_
 _<_<_ {{Strict-Order-Chain-ℚ-ℝ-ℚ}} p q r = (p < q) × (q < r)

 Strict-Order-Chain-ℚ-ℚ-ℝ : Strict-Order-Chain ℚ ℚ ℝ _<_ _<_
 _<_<_ {{Strict-Order-Chain-ℚ-ℚ-ℝ}} p q r = (p < q) × (q < r)

 Strict-Order-Chain-ℝ-ℚ-ℚ : Strict-Order-Chain ℝ ℚ ℚ _<_ _<_
 _<_<_ {{Strict-Order-Chain-ℝ-ℚ-ℚ}} p q r = (p < q) × (q < r)

 Strict-Order-Chain-ℝ-ℚ-ℝ : Strict-Order-Chain ℝ ℚ ℝ _<_ _<_
 _<_<_ {{Strict-Order-Chain-ℝ-ℚ-ℝ}} p q r = (p < q) × (q < r)

ℚ<-not-itself-from-ℝ : (p : ℚ) → (x : ℝ) → ¬ (p < x < p)
ℚ<-not-itself-from-ℝ p x (l₁ , l₂) = ℚ<-irrefl p (disjoint-from-real x p p (l₁ , l₂))

embedding-ℚ-to-ℝ : ℚ → ℝ
embedding-ℚ-to-ℝ x = (L , R) , inhabited-left'
                             , inhabited-right'
                             , rounded-left'
                             , rounded-right'
                             , disjoint'
                             , located'
 where
  L R : 𝓟 ℚ
  L p = p < x , ℚ<-is-prop p x
  R q = x < q , ℚ<-is-prop x q

  inhabited-left' : ∃ p ꞉ ℚ , p < x
  inhabited-left' = ∣ ℚ-no-least-element x ∣

  inhabited-right' : ∃ q ꞉ ℚ , x < q
  inhabited-right' = ∣ ℚ-no-max-element x ∣

  rounded-left' :  (p : ℚ) → (p ∈ L ↔ (∃ p' ꞉ ℚ , p < p' < x))
  rounded-left' p = α , β
   where
    α : p < x →  (∃ p' ꞉ ℚ , p < p' < x)
    α l = ∣ ℚ-dense p x l ∣

    β :  (∃ p' ꞉ ℚ , p < p' < x → p < x)
    β l = ∥∥-rec (ℚ<-is-prop p x) δ l
     where
      δ : Σ p' ꞉ ℚ , p < p' < x → p < x
      δ (p' , a , b) = ℚ<-trans p p' x a b

  rounded-right' : (q : ℚ) → q > x ↔ (∃ q' ꞉ ℚ , (q' < q) × q' > x)
  rounded-right' q = α , β
   where
    α : q > x → ∃ q' ꞉ ℚ , (q' < q) × q' > x
    α r = ∣ δ (ℚ-dense x q r) ∣
     where
      δ : (Σ q' ꞉ ℚ , (x < q') × (q' < q)) → Σ q' ꞉ ℚ , (q' < q) × q' > x
      δ (q' , a , b) = q' , b , a

    β : ∃ q' ꞉ ℚ , (q' < q) × q' > x → q > x
    β r = ∥∥-rec (ℚ<-is-prop x q) δ r
     where
      δ : Σ q' ꞉ ℚ , (q' < q) × q' > x → x < q
      δ (q' , a , b) = ℚ<-trans x q' q b a

  disjoint' : (p q : ℚ) → p < x < q → p < q
  disjoint' p q (l , r) = ℚ<-trans p x q l r

  located' : (p q : ℚ) → p < q → (p < x) ∨ (x < q)
  located' p q l = ∣ located-property p q x l ∣

instance
 canonical-map-ℚ-to-ℝ : Canonical-Map ℚ ℝ
 ι {{canonical-map-ℚ-to-ℝ}} = embedding-ℚ-to-ℝ

ℤ-to-ℝ : ℤ → ℝ
ℤ-to-ℝ z = ι (ι z)

ℕ-to-ℝ : ℕ → ℝ
ℕ-to-ℝ n = ι (ι {{ canonical-map-ℕ-to-ℚ }} n)

instance
 canonical-map-ℤ-to-ℝ : Canonical-Map ℤ ℝ
 ι {{canonical-map-ℤ-to-ℝ}} = ℤ-to-ℝ

 canonical-map-ℕ-to-ℝ : Canonical-Map ℕ ℝ
 ι {{canonical-map-ℕ-to-ℝ}} = ℕ-to-ℝ

0ℝ : ℝ
0ℝ = ι 0ℚ

1ℝ : ℝ
1ℝ = ι 1ℚ

1/2ℝ : ℝ
1/2ℝ = ι 1/2

ℝ-equality : (((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) : ℝ)
           → (Lx ＝ Ly)
           → (Rx ＝ Ry)
           → ((Lx , Rx) , isCutx) ＝ ((Ly , Ry) , isCuty)

ℝ-equality ((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) e₁  e₂ = to-subtype-＝ (λ (L , R) → isCut-is-prop L R) (to-×-＝' (e₁ , e₂))

ℝ-equality' : (((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) : ℝ)
           → (Lx ⊆ Ly)
           → (Ly ⊆ Lx)
           → (Rx ⊆ Ry)
           → (Ry ⊆ Rx)
           → ((Lx , Rx) , isCutx) ＝ ((Ly , Ry) , isCuty)
ℝ-equality' x y a b c d = ℝ-equality x y (subset-extensionality pe fe a b) (subset-extensionality pe fe c d)

ℝ-left-cut-equal-gives-right-cut-equal : (((Lx , Rx) , _) ((Ly , Ry) , _) : ℝ)
                                       → Lx ＝ Ly
                                       → Rx ＝ Ry
ℝ-left-cut-equal-gives-right-cut-equal ((Lx , Rx) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) ((Ly , Ry) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y) left-cut-equal = I left-subsets
 where
  left-subsets : (Lx ⊆ Ly) × (Ly ⊆ Lx)
  left-subsets = ⊆-refl-consequence Lx Ly left-cut-equal
  I : (Lx ⊆ Ly) × (Ly ⊆ Lx) → Rx ＝ Ry
  I (Lx⊆Ly , Ly⊆Lx) = subset-extensionality pe fe Rx⊆Ry Ry⊆Rx
   where
    Rx⊆Ry : Rx ⊆ Ry
    Rx⊆Ry q q-Rx = ∥∥-rec q-Ry-is-prop II obtain-q'
     where
      q-Ry-is-prop : is-prop (q ∈ Ry)
      q-Ry-is-prop = ∈-is-prop Ry q
      obtain-q' : ∃ q' ꞉ ℚ , (q' < q) × q' ∈ Rx
      obtain-q' = (pr₁ (rounded-right-x q)) q-Rx
      II : (Σ q' ꞉ ℚ , (q' < q) × q' ∈ Rx) → q ∈ Ry
      II (q' , (q'<q , q'-Rx)) = ∥∥-rec q-Ry-is-prop III use-located
       where
        use-located : q' ∈ Ly ∨ q ∈ Ry
        use-located = located-y q' q q'<q
        III : q' ∈ Ly ∔ q ∈ Ry → q ∈ Ry
        III (inl q'-Ly) = 𝟘-elim (ℚ<-irrefl q' from-above)
         where
          get-contradiction : q' ∈ Lx
          get-contradiction = Ly⊆Lx q' q'-Ly
          from-above : q' < q'
          from-above = disjoint-x q' q' (get-contradiction , q'-Rx)
        III (inr q'-Ry) = q'-Ry
    Ry⊆Rx : Ry ⊆ Rx
    Ry⊆Rx q q-Ry = ∥∥-rec q-Rx-is-prop II obtain-q'
     where
      q-Rx-is-prop : is-prop (q ∈ Rx)
      q-Rx-is-prop = ∈-is-prop Rx q
      obtain-q' : ∃ q' ꞉ ℚ , (q' < q) × q' ∈ Ry
      obtain-q' = (pr₁ (rounded-right-y q)) q-Ry
      II : Σ q' ꞉ ℚ , (q' < q) × q' ∈ Ry → q ∈ Rx
      II (q' , (q'<q , q'-Ry))  = ∥∥-rec q-Rx-is-prop III use-located
       where
        use-located : q' ∈ Lx ∨ q ∈ Rx
        use-located = located-x q' q q'<q
        III : q' ∈ Lx ∔ q ∈ Rx → q ∈ Rx
        III (inl q'-Lx) = 𝟘-elim (ℚ<-irrefl q' from-above)
         where
          get-contradiction : q' ∈ Ly
          get-contradiction = Lx⊆Ly q' q'-Lx
          from-above : q' < q'
          from-above = disjoint-y q' q' (get-contradiction , q'-Ry)
        III (inr q-Rx) = q-Rx

ℝ-equality-from-left-cut : (((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) : ℝ)
                         → Lx ＝ Ly
                         → ((Lx , Rx) , isCutx) ＝ ((Ly , Ry) , isCuty)
ℝ-equality-from-left-cut x y left-cut-equal = ℝ-equality x y left-cut-equal right-cut-equal
 where
  right-cut-equal : pr₂ (pr₁ x) ＝ pr₂ (pr₁ y)
  right-cut-equal = ℝ-left-cut-equal-gives-right-cut-equal x y left-cut-equal

ℝ-equality-from-left-cut' : (((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) : ℝ)
                          → Lx ⊆ Ly
                          → Ly ⊆ Lx
                          → ((Lx , Rx) , isCutx) ＝ ((Ly , Ry) , isCuty)
ℝ-equality-from-left-cut' x y s t = ℝ-equality-from-left-cut x y (subset-extensionality pe fe s t)

rounded-left-d : (x : ℝ) → (p : ℚ) → p < x → ∃ q ꞉ ℚ , p < q < x
rounded-left-d x@((L , _) , _ , _ , rl , _) = rounded-left-b L rl

use-rounded-real-L : (x : ℝ) (p q : ℚ) → p < q → q < x → p < x
use-rounded-real-L x@((L , _) , _ , _ , rl , _) = rounded-left-c L rl

use-rounded-real-L' : (x : ℝ) (p q : ℚ) → p ≤ q → q < x → p < x
use-rounded-real-L' x@((L , _) , _ , _ , rl , _) = rounded-left-a L rl

use-rounded-real-R : (x : ℝ) (p q : ℚ) → p < q → x < p → x < q
use-rounded-real-R x@((_ , R) , _ , _ , _ , rr , _) = rounded-right-c R rr

use-rounded-real-R' : (x : ℝ) (p q : ℚ) → p ≤ q → x < p → x < q
use-rounded-real-R' x@((_ , R) , _ , _ , _ , rr , _) = rounded-right-a R rr

disjoint-from-real' : (x : ℝ) → (p q : ℚ) → (p < x) × (x < q) → p ≤ q
disjoint-from-real' x p q (l₁ , l₂) = γ
 where
  I : p < q
  I = disjoint-from-real x p q (l₁ , l₂)

  γ : p ≤ q
  γ = ℚ<-coarser-than-≤ p q I

type-of-locator-for-reals : 𝓤₁ ̇
type-of-locator-for-reals = (x : ℝ) → (p q : ℚ) → (p < x) ∔ (x < q)

\end{code}

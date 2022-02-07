Andrew Sneap


\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import OrderNotation --TypeTopology
open import UF-Base --TypeTopology
open import UF-FunExt -- TypeTopology
open import UF-PropTrunc -- TypeTopology
open import UF-Powerset -- TypeTopology
open import UF-Retracts --TypeTopology
open import UF-Subsingletons --TypeTopology
open import UF-Subsingletons-FunExt --TypeTopology
-- open import UF-Univalence --TypeTopology

open import Rationals
open import RationalsOrder 

module DedekindReals
         (pe : Prop-Ext)
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
       where

open PropositionalTruncation pt

ℚ-subset-of-propositions : 𝓤₁ ̇
ℚ-subset-of-propositions = 𝓟 ℚ

ℚ-subset-of-propositions-is-set : is-set ℚ-subset-of-propositions
ℚ-subset-of-propositions-is-set = powersets-are-sets fe pe

inhabited-left : (L : ℚ-subset-of-propositions) → 𝓤₀ ̇
inhabited-left L = (∃ p ꞉ ℚ , p ∈ L) 

inhabited-right : (R : ℚ-subset-of-propositions) → 𝓤₀ ̇
inhabited-right R = (∃ q ꞉ ℚ , q ∈ R)

inhabited-left-is-prop : (L : ℚ-subset-of-propositions) → is-prop (inhabited-left L)
inhabited-left-is-prop L = ∃-is-prop

inhabited-right-is-prop : (R : ℚ-subset-of-propositions) → is-prop (inhabited-right R)
inhabited-right-is-prop R = ∃-is-prop

rounded-left : (L : ℚ-subset-of-propositions) → 𝓤₀ ̇
rounded-left L = (x : ℚ) → (x ∈ L ⇔ (∃ p ꞉ ℚ , (x < p) × p ∈ L))

rounded-left-a : (L : ℚ-subset-of-propositions) → rounded-left L → (x y : ℚ) → x ≤ y → y ∈ L → x ∈ L
rounded-left-a L r x y l y-L = II (ℚ≤-split fe x y l)
 where
  I : (∃ p ꞉ ℚ , (x < p) × p ∈ L) → x ∈ L
  I = pr₂ (r x)
  II : (x < y) ∔ (x ≡ y) → x ∈ L
  II (inl l) = I ∣ y , (l , y-L) ∣
  II (inr r) = transport (_∈ L) (r ⁻¹) y-L

rounded-right : (R : ℚ-subset-of-propositions) → 𝓤₀ ̇
rounded-right R = (x : ℚ) → x ∈ R ⇔ (∃ q ꞉ ℚ , (q < x) × q ∈ R)

rounded-right-a : (R : ℚ-subset-of-propositions) → rounded-right R → (x y : ℚ) → x ≤ y → x ∈ R → y ∈ R
rounded-right-a R r x y l x-R = II (ℚ≤-split fe x y l)
 where
  I : (∃ p ꞉ ℚ , (p < y) × p ∈ R) → y ∈ R 
  I = pr₂ (r y)
  II : (x < y) ∔ (x ≡ y) → y ∈ R
  II (inl r) = I ∣ x , (r , x-R) ∣
  II (inr r) = transport (_∈ R) r x-R

rounded-left-is-prop : (L : ℚ-subset-of-propositions) → is-prop (rounded-left L)
rounded-left-is-prop L = Π-is-prop fe δ
 where
  δ : (x : ℚ) → is-prop (x ∈ L ⇔ (∃ p ꞉ ℚ , (x < p) × p ∈ L))
  δ x = ×-is-prop (Π-is-prop fe (λ _ → ∃-is-prop)) (Π-is-prop fe (λ _ → ∈-is-prop L x))

rounded-right-is-prop : (R : ℚ-subset-of-propositions) → is-prop (rounded-right R)
rounded-right-is-prop R = Π-is-prop fe δ
 where
  δ : (x : ℚ) → is-prop (x ∈ R ⇔ (∃ q ꞉ ℚ , (q < x) × q ∈ R))
  δ x = ×-is-prop (Π-is-prop fe (λ _ → ∃-is-prop)) (Π-is-prop fe (λ _ → ∈-is-prop R x))

disjoint : (L R : ℚ-subset-of-propositions) → 𝓤₀ ̇
disjoint L R = (p q : ℚ) → p ∈ L × q ∈ R → p < q

disjoint-is-prop : (L R : ℚ-subset-of-propositions) → is-prop (disjoint L R)
disjoint-is-prop L R = Π₃-is-prop fe (λ x y _ → ℚ<-is-prop x y)

located : (L R : ℚ-subset-of-propositions) → 𝓤₀ ̇
located L R = (p q : ℚ) → p < q → p ∈ L ∨ q ∈ R

located-is-prop : (L R : ℚ-subset-of-propositions) → is-prop (located L R)
located-is-prop L R = Π₃-is-prop fe (λ _ _ _ → ∨-is-prop)

isCut : (L R : ℚ-subset-of-propositions) → 𝓤₀ ̇
isCut L R = inhabited-left L
          × inhabited-right R
          × rounded-left L
          × rounded-right R
          × disjoint L R
          × located L R

isCut-is-prop : (L R : ℚ-subset-of-propositions) → is-prop (isCut L R)
isCut-is-prop L R = ×-is-prop (inhabited-left-is-prop L)
                   (×-is-prop (inhabited-right-is-prop R)
                   (×-is-prop (rounded-left-is-prop L)
                   (×-is-prop (rounded-right-is-prop R)
                   (×-is-prop (disjoint-is-prop L R)
                              (located-is-prop L R)))))

ℝ : 𝓤₁ ̇
ℝ = Σ (L , R) ꞉ ℚ-subset-of-propositions × ℚ-subset-of-propositions , isCut L R

ℝ-is-set : is-set ℝ
ℝ-is-set = Σ-is-set (×-is-set ℚ-subset-of-propositions-is-set ℚ-subset-of-propositions-is-set) λ (L , R) → props-are-sets (isCut-is-prop L R)

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

  inhabited-left' : ∃ p ꞉ ℚ , p ∈ L
  inhabited-left' = ∣ ℚ-no-least-element x ∣ 

  inhabited-right' : ∃ q ꞉ ℚ , q ∈ R
  inhabited-right' = ∣ ℚ-no-max-element x ∣

  rounded-left' :  (p : ℚ) → (p ∈ L ⇔ (∃ p' ꞉ ℚ , (p < p') × p' ∈ L))
  rounded-left' p = α , β
   where
    α : p ∈ L →  (∃ p' ꞉ ℚ , (p < p') × p' ∈ L)
    α l = ∣ ℚ-dense fe p x l ∣

    β :  (∃ p' ꞉ ℚ , (p < p') × p' ∈ L) → p ∈ L
    β l = ∥∥-rec (ℚ<-is-prop p x) δ l
     where
      δ : Σ p' ꞉ ℚ , (p < p') × p' ∈ L → p < x
      δ (p' , a , b) = ℚ<-trans p p' x a b

  rounded-right' : (q : ℚ) → q ∈ R ⇔ (∃ q' ꞉ ℚ , (q' < q) × q' ∈ R)
  rounded-right' q = α , β
   where
    α : q ∈ R → ∃ q' ꞉ ℚ , (q' < q) × q' ∈ R
    α r = ∣ δ (ℚ-dense fe x q r) ∣
     where
      δ : (Σ q' ꞉ ℚ , (x < q') × (q' < q)) → Σ q' ꞉ ℚ , (q' < q) × q' ∈ R
      δ (q' , a , b) = q' , b , a

    β : ∃ q' ꞉ ℚ , (q' < q) × q' ∈ R → q ∈ R
    β r = ∥∥-rec (ℚ<-is-prop x q) δ r
     where
      δ : Σ q' ꞉ ℚ , (q' < q) × q' ∈ R → x < q
      δ (q' , a , b) = ℚ<-trans x q' q b a

  disjoint' : (p q : ℚ) → p ∈ L × q ∈ R → p < q
  disjoint' p q (l , r) = ℚ<-trans p x q l r

  located' : (p q : ℚ) → p < q → p ∈ L ∨ q ∈ R
  located' p q l = ∣ located-property fe p q x l ∣

0ℝ : ℝ
0ℝ = embedding-ℚ-to-ℝ 0ℚ

1ℝ : ℝ
1ℝ = embedding-ℚ-to-ℝ 1ℚ

ℝ-equality : (((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) : ℝ)
           → (Lx ≡ Ly)
           → (Rx ≡ Ry)
           → ((Lx , Rx) , isCutx) ≡ ((Ly , Ry) , isCuty)
ℝ-equality ((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) e₁  e₂ = to-subtype-≡ (λ (L , R) → isCut-is-prop L R) (to-×-≡' (e₁ , e₂))

ℝ-equality' : (((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) : ℝ)
           → (Lx ⊆ Ly)
           → (Ly ⊆ Lx)
           → (Rx ⊆ Ry)
           → (Ry ⊆ Rx)
           → ((Lx , Rx) , isCutx) ≡ ((Ly , Ry) , isCuty)
ℝ-equality' x y a b c d = ℝ-equality x y (subset-extensionality pe fe a b) (subset-extensionality pe fe c d)

ℝ-left-cut-equal-gives-right-cut-equal : (((Lx , Rx) , _) ((Ly , Ry) , _) : ℝ) → Lx ≡ Ly → Rx ≡ Ry
ℝ-left-cut-equal-gives-right-cut-equal ((Lx , Rx) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) ((Ly , Ry) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y) left-cut-equal = I left-subsets
 where
  left-subsets : (Lx ⊆ Ly) × (Ly ⊆ Lx)
  left-subsets = ⊆-refl-consequence Lx Ly left-cut-equal
  I : (Lx ⊆ Ly) × (Ly ⊆ Lx) → Rx ≡ Ry
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
        III (inl q'-Ly) = 𝟘-elim (ℚ<-not-itself q' from-above)
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
        III (inl q'-Lx) = 𝟘-elim (ℚ<-not-itself q' from-above)
         where
          get-contradiction : q' ∈ Ly
          get-contradiction = Lx⊆Ly q' q'-Lx
          from-above : q' < q'
          from-above = disjoint-y q' q' (get-contradiction , q'-Ry) 
        III (inr q-Rx) = q-Rx

ℝ-equality-from-left-cut : (((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) : ℝ) → Lx ≡ Ly → ((Lx , Rx) , isCutx) ≡ ((Ly , Ry) , isCuty)
ℝ-equality-from-left-cut x y left-cut-equal = ℝ-equality x y left-cut-equal right-cut-equal
 where
  right-cut-equal : pr₂ (pr₁ x) ≡ pr₂ (pr₁ y)
  right-cut-equal = ℝ-left-cut-equal-gives-right-cut-equal x y left-cut-equal

ℝ-equality-from-left-cut' : (((Lx , Rx) , isCutx) ((Ly , Ry) , isCuty) : ℝ) → Lx ⊆ Ly → Ly ⊆ Lx → ((Lx , Rx) , isCutx) ≡ ((Ly , Ry) , isCuty)
ℝ-equality-from-left-cut' x y s t = ℝ-equality-from-left-cut x y (subset-extensionality pe fe s t)

lower-cut-of : ℝ → ℚ-subset-of-propositions
lower-cut-of ((L , R) , _) = L

upper-cut-of : ℝ → ℚ-subset-of-propositions
upper-cut-of ((L , R) , _) = R

in-lower-cut : ℚ → ℝ → 𝓤₀ ̇
in-lower-cut q ((L , R) , _) = q ∈ L

in-upper-cut : ℚ → ℝ → 𝓤₀ ̇
in-upper-cut q ((L , R) , _) = q ∈ R

located-from-real : (((L , R) , _) : ℝ) → (p q : ℚ) → p < q → p ∈ L ∨ q ∈ R
located-from-real ((L , R) , _ , _ , _ , _ , _ , located-y) = located-y 



\end{code}

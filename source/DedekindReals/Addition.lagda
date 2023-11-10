Andrew Sneap, February-April 2021
Updated March 2022

In this file, I define directly addition of the Dedekind reals, and
show that the Reals are a group with respect to addition.

\begin{code}
{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.Base
open import UF.FunExt
open import UF.Subsingletons
open import UF.PropTrunc
open import Notation.Order

open import UF.Powerset
open import DedekindReals.Properties
open import Rationals.Type
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Order

module DedekindReals.Addition
         (fe : Fun-Ext)
         (pe : Prop-Ext)
         (pt : propositional-truncations-exist)
       where

open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open PropositionalTruncation pt

_+_ : ℝ → ℝ → ℝ
((L-x , R-x) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x) + ((L-y , R-y) , inhabited-left-y , inhabited-right-y , rounded-left-y , rounded-right-y , disjoint-y , located-y) =
 (L-z , R-z) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z
 where
  x : ℝ
  x = ((L-x , R-x) , inhabited-left-x , inhabited-right-x , rounded-left-x , rounded-right-x , disjoint-x , located-x)

  L-z R-z : 𝓟 ℚ
  L-z p = (∃ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (p ＝ r ℚ+ s)) , ∃-is-prop
  R-z q = (∃ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × (q ＝ r ℚ+ s)) , ∃-is-prop

  inhabited-left-z : ∃ q ꞉ ℚ , q ∈ L-z
  inhabited-left-z = ∥∥-rec ∃-is-prop δ (binary-choice inhabited-left-x inhabited-left-y)
   where
    δ : (Σ p ꞉ ℚ , p ∈ L-x) × (Σ q ꞉ ℚ , q ∈ L-y) → ∃ z ꞉ ℚ , z ∈ L-z
    δ ((p , l-x) , q , l-y) = ∣ (p ℚ+ q) , (∣ (p , q) , l-x , l-y , refl ∣) ∣

  inhabited-right-z : ∃ q ꞉ ℚ , q ∈ R-z
  inhabited-right-z = ∥∥-rec ∃-is-prop δ (binary-choice inhabited-right-x inhabited-right-y)
   where
    δ : (Σ p ꞉ ℚ , p ∈ R-x) × (Σ q ꞉ ℚ , q ∈ R-y) → ∃ z ꞉ ℚ , z ∈ R-z
    δ ((p , r-x) , q , r-y) = ∣ (p ℚ+ q) , (∣ (p , q) , (r-x , r-y , refl) ∣) ∣

  ψ : (z r t s : ℚ) → t ＝ r ℚ+ s → z ＝ ((r ℚ+ (z ℚ- t)) ℚ+ s)
  ψ z r t s e = z                                               ＝⟨ ℚ-zero-left-neutral z ⁻¹ ⟩
                (0ℚ ℚ+ z)                                       ＝⟨ ap (_ℚ+ z) (ℚ-inverse-sum-to-zero r ⁻¹) ⟩
                ((r ℚ- r)) ℚ+ z                                 ＝⟨ (ℚ+-assoc r (ℚ- r) z) ⟩
                (r ℚ+ ((ℚ- r) ℚ+ z))                            ＝⟨ ℚ-zero-right-neutral (r ℚ+ ((ℚ- r) ℚ+ z)) ⁻¹ ⟩
                (r ℚ+ ((ℚ- r) ℚ+ z)) ℚ+ 0ℚ                      ＝⟨ ap₂ _ℚ+_ (ap (r ℚ+_) (ℚ+-comm (ℚ- r) z)) (ℚ-inverse-sum-to-zero' s ⁻¹) ⟩
                (r ℚ+ (z ℚ- r)) ℚ+ ((ℚ- s) ℚ+ s)                ＝⟨ ℚ+-assoc (r ℚ+ (z ℚ+ (ℚ- r))) (ℚ- s) s ⁻¹ ⟩
                ((r ℚ+ (z ℚ+ (ℚ- r))) ℚ+ (ℚ- s)) ℚ+ s           ＝⟨ ap (_ℚ+ s) (ℚ+-assoc r (z ℚ+ (ℚ- r)) (ℚ- s)) ⟩
                (r ℚ+ ((z ℚ+ (ℚ- r)) ℚ+ (ℚ- s))) ℚ+ s           ＝⟨ ap (λ - → (r ℚ+ -) ℚ+ s) (ℚ+-assoc z (ℚ- r) (ℚ- s)) ⟩
                (r ℚ+ (z ℚ+ ((ℚ- r) ℚ+ (ℚ- s)))) ℚ+ s           ＝⟨ ap (λ - → (r ℚ+ (z ℚ+ -)) ℚ+ s) (ℚ-minus-dist r s) ⟩
                (r ℚ+ (z ℚ+ (ℚ- (r ℚ+ s)))) ℚ+ s                ＝⟨ ap ((λ - → (r ℚ+ (z ℚ+ (ℚ- -))) ℚ+ s)) (e ⁻¹) ⟩
                (r ℚ+ (z ℚ+ (ℚ- t))) ℚ+ s                       ∎

  rounded-left-z : (z : ℚ) → (z ∈ L-z ↔ (∃ t ꞉ ℚ , (z < t) × t ∈ L-z))
  rounded-left-z z = I , II
   where
    I : z ∈ L-z → ∃ t ꞉ ℚ , (z < t) × t ∈ L-z
    I zLz = ∥∥-rec ∃-is-prop δ zLz
     where
      δ : Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (z ＝ r ℚ+ s) → ∃ t ꞉ ℚ , (z < t) × t ∈ L-z
      δ ((r , s) , rLx , sLy , e) = γ (rounded-left-b L-x rounded-left-x r rLx) (rounded-left-b L-y rounded-left-y s sLy)
       where
        γ : (∃ p ꞉ ℚ , r < p × p ∈ L-x) → (∃ q ꞉ ℚ , s < q × q ∈ L-y) → ∃ t ꞉ ℚ , z < t × t ∈ L-z
        γ f g = ζ (binary-choice f g)
         where
          ζ : ∥ (Σ p ꞉ ℚ , r < p × p ∈ L-x) × (Σ q ꞉ ℚ , s < q × q ∈ L-y) ∥ → ∃ t ꞉ ℚ , z < t × t ∈ L-z
          ζ bc = ∥∥-functor η bc
           where
            η : (Σ p ꞉ ℚ , r < p × p ∈ L-x) × (Σ q ꞉ ℚ , s < q × q ∈ L-y) → Σ t ꞉ ℚ , z < t × t ∈ L-z
            η ((p , l₁ , pLx) , q , l₂ , qLy) = (p ℚ+ q) , (II , III)
             where
              II : z <  p ℚ+ q
              II = transport (_< p ℚ+ q) (e ⁻¹) (ℚ<-adding r p s q l₁ l₂)
              III : (p ℚ+ q) ∈ L-z
              III = ∣ (p , q) , (pLx , qLy , refl) ∣

    II : ∃ t ꞉ ℚ , (z < t) × t ∈ L-z → z ∈ L-z
    II et = ∥∥-rec (∈-is-prop L-z z) δ et
     where
      δ : Σ t ꞉ ℚ , (z < t) × t ∈ L-z → z ∈ L-z
      δ (t , l , tLz) = ∥∥-functor γ tLz
       where
        γ : Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (t ＝ r ℚ+ s)
          → Σ (r' , s') ꞉ ℚ × ℚ , r' ∈ L-x × s' ∈ L-y × (z ＝ r' ℚ+ s')
        γ ((r , s) , rLx , sLy , e) = ((r ℚ+ (z ℚ- t)) , s) , III , sLy , IV
         where
          III : (r ℚ+ (z ℚ- t)) ∈ L-x
          III = rounded-left-c L-x rounded-left-x (r ℚ+ (z ℚ- t)) r (ℚ<-subtraction-preserves-order' r (z ℚ- t) (ℚ<-difference-positive' z t l) ) rLx
          IV : z ＝ r ℚ+ (z ℚ- t) ℚ+ s
          IV = ψ z r t s e

  rounded-right-z : (z : ℚ) → (z ∈ R-z) ↔ (∃ q ꞉ ℚ , ((q < z) × (q ∈ R-z)))
  rounded-right-z z = I , II
   where
    I : z ∈ R-z → ∃ q ꞉ ℚ , q < z × q ∈ R-z
    I zRz = ∥∥-rec ∃-is-prop δ zRz
     where
      δ : (Σ (r , s) ꞉ ℚ × ℚ , (r ∈ R-x) × (s ∈ R-y) × (z ＝ (r ℚ+ s))) → (∃ q ꞉ ℚ , (q < z) × q ∈ R-z)
      δ ((r , s) , rRx , sRy , e) = γ (rounded-right-b R-x rounded-right-x r rRx) (rounded-right-b R-y rounded-right-y s sRy)
       where
        γ : (∃ p ꞉ ℚ , p < r × p ∈ R-x) → (∃ q ꞉ ℚ , q < s × q ∈ R-y) → ∃ t ꞉ ℚ , t < z × t ∈ R-z
        γ f g = ζ (binary-choice f g)
         where
          ζ : ∥ (Σ p ꞉ ℚ , p < r × p ∈ R-x) × (Σ q ꞉ ℚ , q < s × q ∈ R-y) ∥ → ∃ t ꞉ ℚ , t < z × t ∈ R-z
          ζ = ∥∥-functor η
           where
            η : (Σ p ꞉ ℚ , p < r × p ∈ R-x) × (Σ q ꞉ ℚ , q < s × q ∈ R-y) → Σ t ꞉ ℚ , t < z × t ∈ R-z
            η ((p , l₁ , pRx) , q , l₂ , qRy) = p ℚ+ q , II , III
             where
              II : p ℚ+ q < z
              II = transport (p ℚ+ q <_) (e ⁻¹) (ℚ<-adding p r q s l₁ l₂)
              III : (p ℚ+ q) ∈ R-z
              III = ∣ (p , q) , pRx , qRy , refl ∣
    II : ∃ t ꞉ ℚ , (t < z) × t ∈ R-z → z ∈ R-z
    II et = ∥∥-rec (∈-is-prop R-z z) δ et
     where
      δ : Σ t ꞉ ℚ , (t < z) × t ∈ R-z → z ∈ R-z
      δ (t , l , tRz) = ∥∥-functor γ tRz
       where
        γ : Σ (r , s) ꞉ ℚ × ℚ , r ∈ R-x × s ∈ R-y × (t ＝ r ℚ+ s)
          → Σ (r' , s') ꞉ ℚ × ℚ , r' ∈ R-x × s' ∈ R-y × (z ＝ r' ℚ+ s')
        γ ((r , s) , rRx , sRy , e) = ((r ℚ+ (z ℚ- t)) , s) , III , sRy , IV
         where
          III : (r ℚ+ (z ℚ- t)) ∈ R-x
          III = rounded-right-c R-x rounded-right-x r (r ℚ+ (z ℚ- t)) (ℚ<-addition-preserves-order'' r (z ℚ- t) (ℚ<-difference-positive t z l)) rRx
          IV : z ＝ r ℚ+ (z ℚ- t) ℚ+ s
          IV = ψ z r t s e

  disjoint-z : disjoint L-z R-z
  disjoint-z p q (α , β) = ∥∥-rec (ℚ<-is-prop p q) δ (binary-choice α β)
   where
    δ : (Σ (r , s) ꞉ ℚ × ℚ , r ∈ L-x × s ∈ L-y × (p ＝ r ℚ+ s))
      × (Σ (r' , s') ꞉ ℚ × ℚ , r' ∈ R-x × s' ∈ R-y × (q ＝ r' ℚ+ s'))
      → p < q
    δ (((r , s) , l-x , l-y , e₁) , ((r' , s') , r-x , r-y , e₂)) = goal
     where
      I : r < r'
      I = disjoint-x r r' (l-x , r-x)

      II : s < s'
      II = disjoint-y s s' (l-y , r-y)

      goal : p < q
      goal = transport₂ _<_ (e₁ ⁻¹) (e₂ ⁻¹) (ℚ<-adding r r' s s' I II)

  located-z : located L-z R-z
  located-z p q l = I (ℝ-arithmetically-located' fe pe pt x ((q ℚ- p) , (ℚ<-difference-positive p q l)))
   where
    I : ∃ (e , t) ꞉ ℚ × ℚ , (e ∈ L-x × t ∈ R-x) × (0ℚ < t ℚ- e < q ℚ- p) → p ∈ L-z ∨ q ∈ R-z
    I = ∥∥-rec ∨-is-prop δ
     where
      δ : Σ (e , t) ꞉ ℚ × ℚ , (e ∈ L-x × t ∈ R-x) × (0ℚ < t ℚ- e < q ℚ- p) → p ∈ L-z ∨ q ∈ R-z
      δ ((e , t) , (eLx , tRx) , (l₁ , l₂)) = IV II III
       where
        l₃ : p ℚ- e < q ℚ- t
        l₃ = transport₂ _<_ i ii (ℚ<-addition-preserves-order (t ℚ- e) (q ℚ- p) (p ℚ- t) l₂)
         where
          i : t ℚ- e ℚ+ (p ℚ- t) ＝ p ℚ- e
          i = t ℚ- e ℚ+ (p ℚ- t)           ＝⟨ ℚ+-comm (t ℚ- e) (p ℚ- t) ⟩
              p ℚ- t ℚ+ (t ℚ- e)           ＝⟨ ℚ+-assoc p (ℚ- t) (t ℚ- e) ⟩
              p ℚ+ ((ℚ- t) ℚ+ (t ℚ- e))    ＝⟨ ap (p ℚ+_) (ℚ+-assoc (ℚ- t) t (ℚ- e) ⁻¹) ⟩
              p ℚ+ ((ℚ- t) ℚ+ t ℚ- e)      ＝⟨ ap (λ α → p ℚ+ (α ℚ- e)) (ℚ-inverse-sum-to-zero' t) ⟩
              p ℚ+ (0ℚ ℚ- e)               ＝⟨ ap (p ℚ+_) (ℚ-zero-left-neutral (ℚ- e)) ⟩
              p ℚ- e ∎
          ii : q ℚ- p ℚ+ (p ℚ- t) ＝ q ℚ- t
          ii = q ℚ- p ℚ+ (p ℚ- t)           ＝⟨ ℚ+-assoc q (ℚ- p) (p ℚ- t) ⟩
               q ℚ+ ((ℚ- p) ℚ+ (p ℚ- t))    ＝⟨ ap (q ℚ+_) (ℚ+-assoc (ℚ- p) p (ℚ- t) ⁻¹) ⟩
               q ℚ+ ((ℚ- p) ℚ+ p ℚ- t)      ＝⟨ ap (λ α → q ℚ+ (α ℚ- t)) (ℚ-inverse-sum-to-zero' p) ⟩
               q ℚ+ (0ℚ ℚ- t)               ＝⟨ ap (q ℚ+_) (ℚ-zero-left-neutral (ℚ- t)) ⟩
               q ℚ- t ∎

        II : Σ z ꞉ ℚ , (p ℚ- e < z) × (z < q ℚ- t)
        II = ℚ-dense (p ℚ- e) (q ℚ- t) l₃

        III : Σ y ꞉ ℚ , p ℚ- e < y < (pr₁ II)
        III = ℚ-dense (p ℚ- e) (pr₁ II) (pr₁ (pr₂ II))
        IV : ((y , _) : Σ y ꞉ ℚ , (p ℚ- e < y) × (y < q ℚ- t)) → Σ z ꞉ ℚ , p ℚ- e < z < y → ∥ p ∈ L-z ∔ q ∈ R-z ∥
        IV (y , l₄ , l₅) (z , l₆ , l₇) = ∥∥-functor η (located-y z y l₇)
         where
          η : z ∈ L-y ∔ y ∈ R-y → p ∈ L-z ∔ q ∈ R-z
          η (inl zLy) = inl ∣ (p ℚ- z , z) , V , zLy , VI ∣
           where
            V : (p ℚ- z) ∈ L-x
            V = rounded-left-c L-x rounded-left-x (p ℚ- z) e (ℚ<-swap' p e z l₆) eLx

            VI : p ＝ p ℚ- z ℚ+ z
            VI = p                  ＝⟨ ℚ-zero-right-neutral p ⁻¹ ⟩
                 p ℚ+ 0ℚ            ＝⟨ ap (p ℚ+_) (ℚ-inverse-sum-to-zero' z ⁻¹) ⟩
                 p ℚ+ ((ℚ- z) ℚ+ z) ＝⟨ ℚ+-assoc p (ℚ- z) z ⁻¹ ⟩
                 p ℚ- z ℚ+ z        ∎

          η (inr yRy) = inr ∣ (t , q ℚ- t) , tRx , V , VI ∣
           where
            V : (q ℚ- t) ∈ R-y
            V = rounded-right-c R-y rounded-right-y y (q ℚ- t) l₅ yRy

            VI : q ＝ t ℚ+ (q ℚ- t)
            VI = q                  ＝⟨ ℚ-zero-left-neutral q ⁻¹ ⟩
                 0ℚ ℚ+ q            ＝⟨ ap (_ℚ+ q) (ℚ-inverse-sum-to-zero t ⁻¹) ⟩
                 t ℚ+ (ℚ- t) ℚ+ q   ＝⟨ ℚ+-assoc t (ℚ- t) q ⟩
                 t ℚ+ ((ℚ- t) ℚ+ q) ＝⟨ ap (t ℚ+_) (ℚ+-comm (ℚ- t) q) ⟩
                 t ℚ+ (q ℚ- t)      ∎
{-
plus2 : ℝ → ℝ → ℝ
plus2 x y = z
 where
  L : 𝓟 ℚ
  L p = (∃ k ꞉ ℚ , (k < x) × (p ℚ- k < y)) , ∃-is-prop
  R : 𝓟 ℚ
  R q = (∃ k ꞉ ℚ , (x < k) × (y < q ℚ+ k)) , ∃-is-prop

  inhabited-left' : inhabited-left L
  inhabited-left' = ∥∥-functor I (binary-choice (inhabited-from-real-L x) (inhabited-from-real-L y))
   where
    I : (Σ k ꞉ ℚ , k < x) × (Σ p ꞉ ℚ , p < y) → Σ p ꞉ ℚ , p ∈ L
    I ((k , k<x) , p , p<y) = p ℚ+ k , ∣ k , k<x , transport (_< y) (ℚ-inverse-intro'' p k) p<y ∣

  inhabited-right' : inhabited-right R
  inhabited-right' = ∥∥-functor I (binary-choice (inhabited-from-real-R x) (inhabited-from-real-R y))
   where
    I : (Σ k ꞉ ℚ , x < k) × (Σ q ꞉ ℚ , y < q) → Σ q ꞉ ℚ , q ∈ R
    I ((k , x<k) , q , y<q) = (q ℚ- k) , ∣ k , x<k ,  transport (y <_) (ℚ-inverse-intro'''' q k) y<q  ∣

  rounded-left' : rounded-left L
  rounded-left' = {!!}

  rounded-right' : rounded-right R
  rounded-right' = {!!}

  disjoint' : disjoint L R
  disjoint' = {!!}

  located' : located L R
  located' = {!!}

  z : ℝ
  z = (L , R) , inhabited-left' , inhabited-right' , rounded-left' , rounded-right' , disjoint' , located'
 -}

infixl 35 _+_

ℝ+-comm : ∀ x y → x + y ＝ y + x
ℝ+-comm x y = ℝ-equality-from-left-cut' (x + y) (y + x) I II
 where
  I : lower-cut-of (x + y) ⊆ lower-cut-of (y + x)
  I p p<x+y = ∥∥-functor i p<x+y
   where
    i : Σ (r , s) ꞉ ℚ × ℚ , (r < x) × (s < y) × (p ＝ r ℚ+ s)
      → Σ (r , s) ꞉ ℚ × ℚ , (r < y) × (s < x) × (p ＝ r ℚ+ s)
    i ((r , s) , rLx , sLy , e) = (s , r) , (sLy , rLx , (e ∙ ℚ+-comm r s))
  II : lower-cut-of (y + x) ⊆ lower-cut-of (x + y)
  II q x+y<q = ∥∥-functor i x+y<q
   where
    i : Σ (r , s) ꞉ ℚ × ℚ , (r < y) × (s < x) × (q ＝ r ℚ+ s)
      → Σ (r , s) ꞉ ℚ × ℚ , (r < x) × (s < y) × (q ＝ r ℚ+ s)
    i ((r , s) , rLy , sLx , e) = (s , r) , (sLx , rLy , (e ∙ ℚ+-comm r s))

ℝ-zero-left-neutral : (x : ℝ) → 0ℝ + x ＝ x
ℝ-zero-left-neutral x = ℝ-equality-from-left-cut' (0ℝ + x) x I II
 where
  I : lower-cut-of (0ℝ + x) ⊆ lower-cut-of x
  I p 0+x<x = ∥∥-rec (∈-is-prop (lower-cut-of x) p) i 0+x<x
   where
    i : Σ (r , s) ꞉ ℚ × ℚ , (r < 0ℝ) × (s < x) × (p ＝ r ℚ+ s) → p < x
    i ((r , s) , r<0 , s<x , e) = rounded-left-c (lower-cut-of x) (rounded-from-real-L x) p s iv s<x
     where
      ii : p ℚ+ r < p
      ii = ℚ<-subtraction-preserves-order' p r r<0
      iii : p ℚ+ r < r ℚ+ s
      iii = transport (p ℚ+ r <_) e ii
      iv : p < s
      iv = transport₂ _<_ v vi (ℚ<-addition-preserves-order (p ℚ+ r) (r ℚ+ s) (ℚ- r) iii )
       where
        v : p ℚ+ r ℚ- r ＝ p
        v = ℚ+-assoc p r (ℚ- r) ∙ ℚ-inverse-intro p r ⁻¹
        vi : r ℚ+ s ℚ- r ＝ s
        vi = r ℚ+ s ℚ- r   ＝⟨ ap (_ℚ- r) (ℚ+-comm r s) ⟩
             s ℚ+ r ℚ- r   ＝⟨ ℚ+-assoc s r (ℚ- r) ⟩
             s ℚ+ (r ℚ- r) ＝⟨ ℚ-inverse-intro s r ⁻¹ ⟩
             s ∎
  II : lower-cut-of x ⊆ lower-cut-of (0ℝ + x)
  II q q<x = ∥∥-functor i by-rounded-x
   where
    by-rounded-x : ∃ q' ꞉ ℚ , q < q' < x
    by-rounded-x = rounded-left-b (lower-cut-of x) (rounded-from-real-L x) q q<x
    i : Σ q' ꞉ ℚ , q < q' < x → Σ (r , s) ꞉ ℚ × ℚ , (r < 0ℝ) × (s < x) × (q ＝ r ℚ+ s)
    i (q' , l , q'Lx) = (q ℚ- q' , q') , iii , q'Lx , ii
     where
      ii : q ＝ q ℚ- q' ℚ+ q'
      ii = q                    ＝⟨ ℚ-inverse-intro q q' ⟩
           q ℚ+ (q' ℚ- q')      ＝⟨ ap (q ℚ+_) (ℚ+-comm q' (ℚ- q')) ⟩
           q ℚ+ ((ℚ- q') ℚ+ q') ＝⟨ ℚ+-assoc q (ℚ- q') q' ⁻¹ ⟩
           q ℚ- q' ℚ+ q' ∎

      iii : q ℚ- q' < 0ℚ
      iii = transport (q ℚ- q' <_) iv (ℚ<-addition-preserves-order q q' (ℚ- q') l)
       where
        iv : q' ℚ- q' ＝ 0ℚ
        iv = ℚ-inverse-sum-to-zero q'

ℝ-zero-right-neutral : (x : ℝ) → x + 0ℝ ＝ x
ℝ-zero-right-neutral x = ℝ+-comm x 0ℝ ∙ ℝ-zero-left-neutral x

ℝ+-assoc : ∀ x y z → x + y + z ＝ x + (y + z)
ℝ+-assoc x y z = ℝ-equality-from-left-cut' _ _ ltr rtl
 where
  ltr : lower-cut-of (x + y + z) ⊆ lower-cut-of (x + (y + z))
  ltr p p<x+y+z = ∥∥-rec ∃-is-prop I p<x+y+z
   where
    I : Σ (a  , b) ꞉ ℚ × ℚ , (a  < (x + y)) × (b < z)        × (p ＝ a ℚ+ b)
      → ∃ (r  , s) ꞉ ℚ × ℚ , (r  < x)       × (s < (y + z))  × (p ＝ r ℚ+ s)
    I ((a , b) , a<x+y , b<z , e) = ∥∥-rec ∃-is-prop II a<x+y
     where
      II : Σ (c , d) ꞉ ℚ × ℚ , (c < x) × (d < y)        × (a ＝ c ℚ+ d)
         → ∃ (r , s) ꞉ ℚ × ℚ , (r < x) × (s < (y + z))  × (p ＝ r ℚ+ s)
      II ((c , d) , c<x , d<y , e') = ∣ (c , (b ℚ+ d)) , c<x , III , i ∣
       where
        i : p ＝ c ℚ+ (b ℚ+ d)
        i = p             ＝⟨ e ⟩
            a ℚ+ b        ＝⟨ ap (_ℚ+ b) e' ⟩
            c ℚ+ d ℚ+ b   ＝⟨ ℚ+-assoc c d b ⟩
            c ℚ+ (d ℚ+ b) ＝⟨ ap (c ℚ+_) (ℚ+-comm d b) ⟩
            c ℚ+ (b ℚ+ d) ∎

        III : (b ℚ+ d) < (y + z)
        III = ∣ (d , b) , (d<y , b<z , ℚ+-comm b d) ∣
  rtl :  lower-cut-of (x + (y + z)) ⊆ lower-cut-of (x + y + z)
  rtl p p<x+y+z-r = ∥∥-rec ∃-is-prop I p<x+y+z-r
   where
    I : Σ (a  , b) ꞉ ℚ × ℚ , (a  < x)        × (b < (y + z))  × (p ＝ a ℚ+ b)
      → ∃ (r  , s) ꞉ ℚ × ℚ , (r  < (x + y))  × (s < z)        × (p ＝ r ℚ+ s)
    I ((a , b) , a<x , b<y+z , e) = ∥∥-rec ∃-is-prop II b<y+z
     where
      II : Σ (c , d) ꞉ ℚ × ℚ , (c < y)       × (d < z)  × (b ＝ c ℚ+ d)
         → ∃ (r , s) ꞉ ℚ × ℚ , (r < (x + y)) × (s < z)  × (p ＝ r ℚ+ s)
      II ((c , d) , c<y , d<z , e') = ∣ ((a ℚ+ c) , d) , III , d<z , i ∣
       where
        i : p ＝ a ℚ+ c ℚ+ d
        i = e ∙ (ap (a ℚ+_) e' ∙ ℚ+-assoc a c d ⁻¹)
        III : (a ℚ+ c) < (x + y)
        III = ∣ (a , c) , a<x , c<y , refl ∣

open import Rationals.Multiplication renaming (_*_ to _ℚ*_)

-_ : ℝ → ℝ
-_ x = (L , R) , inhabited-left-z , inhabited-right-z , rounded-left-z , rounded-right-z , disjoint-z , located-z
 where
  L : 𝓟 ℚ
  L p = (∃ r ꞉ ℚ , r > x × (p ＝ ℚ- r)) , ∃-is-prop
  R : 𝓟 ℚ
  R q = (∃ r ꞉ ℚ , r < x × (q ＝ ℚ- r)) , ∃-is-prop

  inhabited-left-z : inhabited-left L
  inhabited-left-z = ∥∥-rec ∃-is-prop I (binary-choice (inhabited-from-real-L x) (inhabited-from-real-R x))
   where
    I : (Σ a ꞉ ℚ , a < x) × (Σ b ꞉ ℚ , b > x) → ∃ p ꞉ ℚ , p ∈ L
    I ((a , a<x) , b ,  x<b) = ∥∥-functor II (ℝ-locatedness x (ℚ- b) (ℚ- a) (ℚ<-swap a b (disjoint-from-real x a b (a<x , x<b))))
     where
      II : ((ℚ- b) < x) ∔ (ℚ- a) > x → Σ p ꞉ ℚ , p ∈ L
      II (inl z) = (ℚ- b) , ∣ b , x<b , refl ∣
      II (inr z) = a      , ∣ ℚ- a , z , ℚ-minus-minus a ∣

  inhabited-right-z : inhabited-right R
  inhabited-right-z = ∥∥-rec ∃-is-prop I (binary-choice (inhabited-from-real-L x) (inhabited-from-real-R x))
   where
    I : (Σ a ꞉ ℚ , a < x) × (Σ b ꞉ ℚ , b > x) → ∃ q ꞉ ℚ , q ∈ R
    I ((a , a<x) , b , x<b) = ∥∥-functor II (ℝ-locatedness x (ℚ- b) (ℚ- a) (ℚ<-swap a b (disjoint-from-real x a b (a<x , x<b))))
     where
      II : ((ℚ- b) < x) ∔ (ℚ- a) > x → Σ q ꞉ ℚ , q ∈ R
      II (inl z) = b      , ∣ ℚ- b , z , (ℚ-minus-minus b) ∣
      II (inr z) = (ℚ- a) , ∣ a , (a<x , refl) ∣

  rounded-left-z : rounded-left L
  rounded-left-z p = ltr , rtl
   where
    ltr : p ∈ L → ∃ p' ꞉ ℚ , p < p' × p' ∈ L
    ltr p<x = ∥∥-rec ∃-is-prop I p<x
     where
      I : Σ r ꞉ ℚ , r > x × (p ＝ ℚ- r) → ∃ p' ꞉ ℚ , p < p' × p' ∈ L
      I (r , x<r , e) = ∥∥-functor III II
       where
        II : ∃ r' ꞉ ℚ , r' < r × r' > x
        II = rounded-right-b (upper-cut-of x) (rounded-from-real-R x) r x<r
        III : Σ r' ꞉ ℚ , r' < r × r' > x → Σ p' ꞉ ℚ , p < p' × p' ∈ L
        III (r' , l , r'<x) = ℚ- r' , transport (_< ℚ- r') (e ⁻¹) (ℚ<-swap r' r l) , ∣ r' , r'<x , refl ∣

    rtl : ∃ p' ꞉ ℚ , p < p' × p' ∈ L → p ∈ L
    rtl exists-p' = ∥∥-rec ∃-is-prop I exists-p'
     where
      I : Σ p' ꞉ ℚ , p < p' × p' ∈ L → ∃ r ꞉ ℚ , r > x × (p ＝ ℚ- r)
      I (p' , l , p<-x) = ∥∥-functor II p<-x
       where
        II : Σ r ꞉ ℚ , r > x × (p' ＝ ℚ- r) →  Σ r ꞉ ℚ , r > x × (p ＝ ℚ- r)
        II (r , x<r , e) = (ℚ- p) , (III , (ℚ-minus-minus p))
         where
          III : (ℚ- p) > x
          III = rounded-right-c (upper-cut-of x) (rounded-from-real-R x) (ℚ- p') (ℚ- p) (ℚ<-swap p p' l) (transport (_> x) i x<r)
           where
            i : r ＝ ℚ- p'
            i = ℚ-minus-minus r ∙ ap ℚ-_ e ⁻¹

  rounded-right-z : rounded-right R
  rounded-right-z q = ltr , rtl
   where
    ltr : q ∈ R → ∃ q' ꞉ ℚ , q' < q × q' ∈ R
    ltr x<q = ∥∥-rec ∃-is-prop I x<q
     where
      I : Σ r ꞉ ℚ , r < x × (q ＝ ℚ- r) → ∃ q' ꞉ ℚ , q' < q × q' ∈ R
      I (r , r<x , e) = ∥∥-functor III II
       where
        II : ∃ r' ꞉ ℚ , r < r' < x
        II = rounded-left-b (lower-cut-of x) (rounded-from-real-L x) r r<x
        III : (Σ r' ꞉ ℚ , r < r' < x) → Σ q' ꞉ ℚ , q' < q × q' ∈ R
        III (r' , l , x<r') = ℚ- r' , (transport (ℚ- r' <_) (e ⁻¹) (ℚ<-swap r r' l) , ∣ r' , x<r' , refl ∣)
    rtl : ∃ q' ꞉ ℚ , q' < q × q' ∈ R → q ∈ R
    rtl exists-q' = ∥∥-rec ∃-is-prop I exists-q'
     where
      I : Σ q' ꞉ ℚ , q' < q × q' ∈ R → ∃ r ꞉ ℚ , r < x × (q ＝ ℚ- r)
      I (q' , l , -x<q') = ∥∥-functor II -x<q'
       where
        II : Σ r ꞉ ℚ , r < x × (q' ＝ ℚ- r) →  Σ r ꞉ ℚ , r < x × (q ＝ ℚ- r)
        II (r , r<x , e) = (ℚ- q) , (III , (ℚ-minus-minus q))
         where
          III : (ℚ- q) < x
          III = rounded-left-c  (lower-cut-of x) (rounded-from-real-L x) (ℚ- q) r (transport ((ℚ- q) <_) i (ℚ<-swap q' q l)) r<x
           where
           i : ℚ- q' ＝ r
           i = ap ℚ-_ e ∙ ℚ-minus-minus r ⁻¹

  disjoint-z : disjoint L R
  disjoint-z p q (p<x , x<q) = ∥∥-rec (ℚ<-is-prop p q) I (binary-choice p<x x<q)
   where
    I : (Σ p' ꞉ ℚ , p' > x × (p ＝ ℚ- p')) × (Σ q' ꞉ ℚ , q' < x × (q ＝ ℚ- q'))
      → p < q
    I ((p' , p'<x , e) , q' , x<q' , e') = transport₂ _<_ (e ⁻¹) (e' ⁻¹) (ℚ<-swap q' p' II)
     where
      II : q' < p'
      II = disjoint-from-real x q' p' (x<q' , p'<x)

  located-z : located L R
  located-z p q p<q = ∥∥-functor I (ℝ-locatedness x (ℚ- q) (ℚ- p) (ℚ<-swap p q p<q))
   where
    I : (ℚ- q) < x ∔ (ℚ- p) > x → p ∈ L ∔ q ∈ R
    I (inl -q<x) = inr ∣ (ℚ- q) , -q<x , ℚ-minus-minus q ∣
    I (inr x<-p) = inl ∣ (ℚ- p) , x<-p , ℚ-minus-minus p ∣

_-_ : ℝ → ℝ → ℝ
x - y = x + (- y)

ℝ+-inverse-exists : ∀ x → Σ x' ꞉ ℝ , x + x' ＝ 0ℝ
ℝ+-inverse-exists x = (- x) , ℝ-equality-from-left-cut' (x - x) 0ℝ ltr rtl
 where
  ltr : lower-cut-of (x - x) ⊆ lower-cut-of 0ℝ
  ltr p p<x-x = ∥∥-rec (∈-is-prop (lower-cut-of 0ℝ) p) I p<x-x
   where
    I : Σ (r , s) ꞉ ℚ × ℚ , (r < x) × (s < (- x)) × (p ＝ r ℚ+ s)
      → p < 0ℝ
    I ((r , s) , r<x , s<-x , e) = ∥∥-rec (∈-is-prop (lower-cut-of 0ℝ) p) II s<-x
     where
      II : Σ k ꞉ ℚ , k > x × (s ＝ ℚ- k) → p < 0ℝ
      II (k , x<k , e') = III (ℚ-trichotomous p 0ℚ)
       where
        r<k : r < k
        r<k = disjoint-from-real x r k (r<x , x<k)
        e'' : p ＝ r ℚ- k
        e'' = e ∙ ap (r ℚ+_) e'
        III : (p < 0ℚ) ∔ (p ＝ 0ℚ) ∔ (0ℚ < p) → p < 0ℝ
        III (inl p<0)       = p<0
        III (inr (inl p＝0)) = 𝟘-elim (ℚ<-irrefl k (transport (_< k) i r<k))
         where
          i : r ＝ k
          i = r                  ＝⟨ ℚ-inverse-intro r k ⟩
              r ℚ+ (k ℚ- k)      ＝⟨ ap (r ℚ+_) (ℚ+-comm k (ℚ- k)) ⟩
              r ℚ+ ((ℚ- k) ℚ+ k) ＝⟨ ℚ+-assoc r (ℚ- k) k ⁻¹ ⟩
              r ℚ- k ℚ+ k        ＝⟨ ap (_ℚ+ k) e'' ⁻¹ ⟩
              p ℚ+ k             ＝⟨ ap (_ℚ+ k) p＝0 ⟩
              0ℚ ℚ+ k            ＝⟨ ℚ-zero-left-neutral k ⟩
              k ∎
        III (inr (inr 0<p)) = 𝟘-elim (ℚ<-irrefl k (ℚ<-trans k r k k<r r<k))
         where
          i : 0ℚ < r ℚ- k
          i = transport (0ℚ <_) e'' 0<p
          k<r : k < r
          k<r = transport₂ _<_ iii iv (ℚ<-addition-preserves-order 0ℚ (r ℚ- k) k i)
           where
            iii : 0ℚ ℚ+ k ＝ k
            iii = ℚ-zero-left-neutral k
            iv : r ℚ- k ℚ+ k ＝ r
            iv = r ℚ- k ℚ+ k          ＝⟨ ℚ+-assoc r (ℚ- k) k  ⟩
                 r ℚ+ ((ℚ- k) ℚ+ k)   ＝⟨ ap (r ℚ+_) (ℚ+-comm (ℚ- k) k) ⟩
                 r ℚ+ (k ℚ- k)        ＝⟨ ℚ-inverse-intro r k ⁻¹ ⟩
                 r ∎

  rtl : lower-cut-of 0ℝ ⊆ lower-cut-of (x - x)
  rtl p p<0 = ∥∥-rec (∈-is-prop (lower-cut-of (x - x)) p) II I
   where
    I : ∃ (a , b) ꞉ ℚ × ℚ , (a < x < b) × (0ℚ < b ℚ- a < ℚ- p)
    I = ℝ-arithmetically-located' fe pe pt x ((ℚ- p) , (ℚ<-swap p 0ℚ p<0))
    II : Σ (a , b) ꞉ ℚ × ℚ , (a < x < b) × (0ℚ < b ℚ- a < ℚ- p) → p < (x - x)
    II ((a , b) , (a<x , x<b) , (0<b-a , b-a<-p)) = ∣ (a , p ℚ- a) , a<x , ∣ (a ℚ- p) , (i , ii) ∣ , iii ∣
     where
      i : (a ℚ- p) > x
      i = rounded-right-c (upper-cut-of x) (rounded-from-real-R x) b (a ℚ- p) (transport₂ _<_ α β (ℚ<-addition-preserves-order (b ℚ- a) (ℚ- p) a b-a<-p)) x<b
       where
        α : b ℚ- a ℚ+ a ＝ b
        α = b ℚ- a ℚ+ a          ＝⟨ ℚ+-assoc b (ℚ- a) a ⟩
            b ℚ+ ((ℚ- a) ℚ+ a)   ＝⟨ ap (b ℚ+_) (ℚ+-comm (ℚ- a) a) ⟩
            b ℚ+ (a ℚ- a)        ＝⟨ ℚ-inverse-intro b a ⁻¹ ⟩
            b ∎
        β : (ℚ- p) ℚ+ a ＝ a ℚ- p
        β = ℚ+-comm (ℚ- p) a
      ii : p ℚ- a ＝ ℚ- (a ℚ- p)
      ii = p ℚ- a                ＝⟨ ℚ+-comm p (ℚ- a) ⟩
           (ℚ- a) ℚ+ p           ＝⟨ ap ((ℚ- a) ℚ+_) (ℚ-minus-minus p) ⟩
           (ℚ- a) ℚ+ (ℚ- (ℚ- p)) ＝⟨ ℚ-minus-dist a (ℚ- p) ⟩
           ℚ- (a ℚ- p) ∎
      iii : p ＝ a ℚ+ (p ℚ- a)
      iii = p                ＝⟨ ℚ-inverse-intro p a ⟩
            p ℚ+ (a ℚ- a)    ＝⟨ ℚ+-assoc p a (ℚ- a) ⁻¹ ⟩
            p ℚ+ a ℚ+ (ℚ- a) ＝⟨ ap (_ℚ- a) (ℚ+-comm p a) ⟩
            a ℚ+ p ℚ- a      ＝⟨ ℚ+-assoc a p (ℚ- a) ⟩
            a ℚ+ (p ℚ- a) ∎

{-
ℝ<-addition-preserves-order : ∀ x y z → x < y → x + z < y + z
ℝ<-addition-preserves-order x y z l = ∥∥-rec ∃-is-prop I l
 where
  I : Σ k ꞉ ℚ , k > x × k < y
    → ∃ v ꞉ ℚ , v > (x + z) × v < (y + z)
  I (k , x<k , k<y) = ∥∥-rec ∃-is-prop IV (binary-choice II III)
   where
    II : ∃ c ꞉ ℚ , c < k × c > x
    II = rounded-right-b (upper-cut-of x) (rounded-from-real-R x) k x<k
    III : ∃ d ꞉ ℚ , k < d × d < y
    III = rounded-left-b (lower-cut-of y) (rounded-from-real-L y) k k<y
    IV : ((Σ c ꞉ ℚ , c < k × c > x) × (Σ d ꞉ ℚ , k < d × d < y))
       → ∃ v ꞉ ℚ , v > (x + z) × v < (y + z)
    IV ((c , l₁ , c<x) , d , l₂ , d<y) = V (ℝ-arithmetically-located pt pe z (d ℚ- c) (ℚ<-difference-positive c d (ℚ<-trans c k d l₁ l₂)))
     where
      V : (∃ (a , b) ꞉ ℚ × ℚ , a < z × b > z × 0ℚ < b ℚ- a × b ℚ- a < d ℚ- c)
        → ∃ v ꞉ ℚ , v > (x + z) × v < (y + z)
      V = ∥∥-functor VI
       where
        VI : Σ (a , b) ꞉ ℚ × ℚ , a < z × b > z × 0ℚ < b ℚ- a × b ℚ- a < d ℚ- c
           → Σ v ꞉ ℚ , v > (x + z) × v < (y + z)
        VI ((a , b) , a<z , z<b , l₃ , l₄) = a ℚ+ b ℚ- k , VII , VIII ----- a + b - k maybe
         where
          VII : (a ℚ+ b ℚ- k) > (x + z)
          VII = ∣ ({!!} , {!!}) , ({!!} , ({!!} , {!!})) ∣
          VIII : (a ℚ+ b ℚ- k) < (y + z)
          VIII = {!!}

ℝ<-addition-preserves-order' : ∀ x y z → x < y → x + z < y + z
ℝ<-addition-preserves-order' x y z l = ∥∥-rec ∃-is-prop I l
 where
  I : Σ k ꞉ ℚ , x < k     × k < y
    → ∃ v ꞉ ℚ , x + z < v × v < y + z
  I (k , x<k , k<y) = {!!}
-}

ℝ+-inverse-exists' : (x : ℝ) → Σ x' ꞉ ℝ , (x' + x ＝ 0ℝ) × (x + x' ＝ 0ℝ)
ℝ+-inverse-exists' x = I (ℝ+-inverse-exists x)
 where
  I : (Σ x' ꞉ ℝ , (x + x' ＝ 0ℝ)) → Σ x' ꞉ ℝ , (x' + x ＝ 0ℝ) × (x + x' ＝ 0ℝ)
  I (x' , e) = x' , ((ℝ+-comm x' x ∙ e) , e)

open import Groups.Type

ℝ-additive-group : Group-structure ℝ
ℝ-additive-group = _+_ , (ℝ-is-set , ℝ+-assoc , 0ℝ , ℝ-zero-left-neutral , ℝ-zero-right-neutral , ℝ+-inverse-exists')

\end{code}
}

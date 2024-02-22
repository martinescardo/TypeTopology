```agda
{-# OPTIONS --exact-split --without-K --safe  #-}

open import MLTT.Spartan
open import Notation.CanonicalMap
open import Notation.Order
open import UF.FunExt
open import UF.PropTrunc
open import UF.Powerset
open import UF.Subsingletons

open import TWA.Thesis.AndrewSneap.DyadicRationals
open import TWA.Thesis.Chapter5.Integers

module TWA.Thesis.AndrewSneap.DyadicReals
  (pe : PropExt)
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (dy : Dyadics)
 where

 open PropositionalTruncation pt
 open Dyadics dy
 open import UF.Subsingletons-FunExt
```

This file defines Dedekind reals using Dyadic Rationals.

The code is this file is based upon the work in the lagda file, in most cases
simply changing ℚ to ℤ[1/2] is all that is necessary.

http://math.andrej.com/wp-content/uploads/2008/08/abstract-cca2008.pdf

"The rationals may be replaced by any dense Archimedean subring of R with
decidable order", and as in "Efficient Computation with Dedekind Reals" we
implement Dedekind reals using dyadic rationals.


The definition of the reals follows, by first defining the four properties that
a real satisfies.

```agda
 inhabited-left : (L : 𝓟 ℤ[1/2]) → 𝓤₀ ̇
 inhabited-left L = ∃ p ꞉ ℤ[1/2] , p ∈ L

 inhabited-right : (R : 𝓟 ℤ[1/2]) → 𝓤₀ ̇
 inhabited-right R = ∃ q ꞉ ℤ[1/2] , q ∈ R

 rounded-left : (L : 𝓟 ℤ[1/2]) → 𝓤₀ ̇
 rounded-left L = (x : ℤ[1/2]) → (x ∈ L ↔ (∃ p ꞉ ℤ[1/2] , (x < p) × p ∈ L))

 rounded-right : (R : 𝓟 ℤ[1/2]) → 𝓤₀ ̇
 rounded-right R = (x : ℤ[1/2]) → x ∈ R ↔ (∃ q ꞉ ℤ[1/2] , (q < x) × q ∈ R)

 disjoint : (L R : 𝓟 ℤ[1/2]) → 𝓤₀ ̇
 disjoint L R = (p q : ℤ[1/2]) → p ∈ L × q ∈ R → p < q

 located : (L R : 𝓟 ℤ[1/2]) → 𝓤₀ ̇
 located L R = (p q : ℤ[1/2]) → p < q → p ∈ L ∨ q ∈ R

 isCut : (L R : 𝓟 ℤ[1/2]) → 𝓤₀ ̇
 isCut L R = inhabited-left L
           × inhabited-right R
           × rounded-left L
           × rounded-right R
           × disjoint L R
           × located L R

 ℝ-d : 𝓤₁  ̇
 ℝ-d = Σ (L , R) ꞉ 𝓟 ℤ[1/2] × 𝓟 ℤ[1/2] , isCut L R
```

Now we can introduce notation to obtain specific cuts, or refer to a rational
inhabiting a cut. This is useful for readability purposes.

```agda
 lower-cut-of : ℝ-d → 𝓟 ℤ[1/2]
 lower-cut-of ((L , R) , _) = L

 upper-cut-of : ℝ-d → 𝓟 ℤ[1/2]
 upper-cut-of ((L , R) , _) = R

 in-lower-cut : ℤ[1/2] → ℝ-d → 𝓤₀ ̇
 in-lower-cut q ((L , R) , _) = q ∈ L

 in-upper-cut : ℤ[1/2] → ℝ-d → 𝓤₀ ̇
 in-upper-cut q ((L , R) , _) = q ∈ R

 inhabited-from-real-L : (x : ℝ-d) → inhabited-left (lower-cut-of x)
 inhabited-from-real-L
  ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located)
  = inhab-L

 inhabited-from-real-R : (x : ℝ-d) → inhabited-right (upper-cut-of x)
 inhabited-from-real-R
  ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located)
  = inhab-R

 rounded-from-real-L1 : (x : ℝ-d) → (k : ℤ[1/2]) → k ∈ lower-cut-of x
                      → ∃ p ꞉ ℤ[1/2] , k < p × p ∈ lower-cut-of x
 rounded-from-real-L1
  ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located) k
  = pr₁ (rounded-L k)

 rounded-from-real-L2 : (x : ℝ-d) → (k : ℤ[1/2])
                      → ∃ p ꞉ ℤ[1/2] , k < p × p ∈ lower-cut-of x
                      → k ∈ lower-cut-of x
 rounded-from-real-L2
  ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located) k
  = pr₂ (rounded-L k)

 rounded-from-real-R1 : (x : ℝ-d) → (k : ℤ[1/2]) → k ∈ upper-cut-of x
                      → ∃ q ꞉ ℤ[1/2] , q < k × q ∈ upper-cut-of x
 rounded-from-real-R1
  ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located) k
  = pr₁ (rounded-R k)

 rounded-from-real-R2 : (x : ℝ-d) → (k : ℤ[1/2])
                      → ∃ q ꞉ ℤ[1/2] , q < k × q ∈ upper-cut-of x
                      → k ∈ upper-cut-of x
 rounded-from-real-R2
  ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located) k
  = pr₂ (rounded-R k)

 located-from-real : (x : ℝ-d) → (p q : ℤ[1/2])
                   → p < q → p ∈ lower-cut-of x ∨ q ∈ upper-cut-of x
 located-from-real
  ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located)
  = located
 
 instance
  Strict-Order-ℤ[1/2]-ℝ-d : Strict-Order ℤ[1/2] ℝ-d
  _<_ {{Strict-Order-ℤ[1/2]-ℝ-d}} = in-lower-cut

  Strict-Order-ℝ-d-ℤ[1/2] : Strict-Order ℝ-d ℤ[1/2]
  _<_ {{Strict-Order-ℝ-d-ℤ[1/2]}} = λ y q → in-upper-cut q y
```

We now define negation and addition from the operations on dyadic rationals.

 ℝd- : ℝ-d → ℝ-d
 ℝd- x = (L , R) , {!!}
  where
   L R : 𝓟 ℤ[1/2]
   L p = x < (ℤ[1/2]- p) , ∈-is-prop (upper-cut-of x) (ℤ[1/2]- p) 
   R q = (ℤ[1/2]- q) < x , ∈-is-prop (lower-cut-of x) (ℤ[1/2]- q) 

 _ℝd+_ : ℝ-d → ℝ-d → ℝ-d
 x ℝd+ y = (L , R) , {!!}
  where
   L R : 𝓟 ℤ[1/2]
   L p = (∃ (r , s) ꞉ ℤ[1/2] × ℤ[1/2]
                    , r ∈ lower-cut-of x × s ∈ lower-cut-of y
                    × (p ＝ r ℤ[1/2]+ s))
       , ∃-is-prop
   R q = (∃ (r , s) ꞉ ℤ[1/2] × ℤ[1/2]
                    , r ∈ upper-cut-of x × s ∈ upper-cut-of y
                    × (q ＝ r ℤ[1/2]+ s)) , ∃-is-prop

Order and equality:

```agda
 _ℝ-d≤_ : ℝ-d → ℝ-d → 𝓤₀  ̇
 _ℝ-d≤_ x y = (r : ℤ[1/2])
         → r ∈ lower-cut-of x
         → r ∈ lower-cut-of y

 isCut-is-prop : (L R : 𝓟 ℤ[1/2]) → is-prop (isCut L R)
 isCut-is-prop L R
  = ×₆-is-prop ∃-is-prop ∃-is-prop
      (Π-is-prop (fe _ _) (λ _ → ×-is-prop (Π-is-prop (fe _ _) (λ _ → ∃-is-prop))
                                           (Π-is-prop (fe _ _) (λ _ → ∈-is-prop L _))))
      (Π-is-prop (fe _ _) (λ _ → ×-is-prop (Π-is-prop (fe _ _) (λ _ → ∃-is-prop))
                                           (Π-is-prop (fe _ _) (λ _ → ∈-is-prop R _))))
      (Π-is-prop (fe _ _) (λ p → Π-is-prop (fe _ _)
                          (λ q → Π-is-prop (fe _ _) (λ _ → <ℤ[1/2]-is-prop p q))))
      (Π-is-prop (fe _ _) (λ _ → Π-is-prop (fe _ _)
                          (λ _ → Π-is-prop (fe _ _) (λ _ → ∨-is-prop))))

 same-cuts-gives-equality : (x@((Lx , Rx) , _) y@((Ly , Ry) , _) : ℝ-d)
                          → Lx ⊆ Ly → Ly ⊆ Lx
                          → Rx ⊆ Ry → Ry ⊆ Rx
                          → Id x y
 same-cuts-gives-equality ((Lx , Rx) , _) ((Ly , Ry) , _) f g h i
  = to-subtype-＝ (λ (L , R) → isCut-is-prop L R)
       (ap (_, Rx) (subset-extensionality (pe _) (fe _ _) f g)
      ∙ ap (Ly ,_) (subset-extensionality (pe _) (fe _ _) h i))
```

From dyadic:

 ℤ[1/2]-to-ℝ-d : ℤ[1/2] → ℝ-d
 ℤ[1/2]-to-ℝ-d x = (L , R) , {!!}
  where
   L R : 𝓟 ℤ[1/2]
   L p = p ≤ x , ≤ℤ[1/2]-is-prop p x
   R q = x ≤ q , ≤ℤ[1/2]-is-prop x q


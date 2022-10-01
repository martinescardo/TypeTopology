This file defines Dedekind reals using Dyadic Rationals.

The code is this file is based upon the work in the DedekindReals.lagda file, in most cases simply changing ℚ to ℤ[1/2] is all that is necessary.

http://math.andrej.com/wp-content/uploads/2008/08/abstract-cca2008.pdf

"The rationals may be replaced by any dense Archimedean subring of R with decidable order", and as in "Efficient Computation with Dedekind Reals" we implement Dedekind reals using dyadic rationals.

```agda

{-# OPTIONS --allow-unsolved-metas #-}

open import MLTT.Spartan renaming (_+_ to _∔_)

open import Notation.CanonicalMap
open import Notation.Order
open import UF.FunExt
open import UF.PropTrunc
open import UF.Powerset
open import UF.Subsingletons

module Todd.DyadicReals
  (pe : PropExt)
  (pt : propositional-truncations-exist)
  (fe : FunExt)
 where

 open PropositionalTruncation pt
 open import Todd.RationalsDyadic fe

```

The definition of the reals follows, by first defining the 4 properties that a real satisfies.

```agda

 inhabited-left : (L : 𝓟 ℤ[1/2]) → 𝓤₀ ̇
 inhabited-left L = ∃ p ꞉ ℤ[1/2] , p ∈ L

 inhabited-right : (R : 𝓟 ℤ[1/2]) → 𝓤₀ ̇
 inhabited-right R = ∃ q ꞉ ℤ[1/2] , q ∈ R

 rounded-left : (L : 𝓟 ℤ[1/2]) → 𝓤₀ ̇
 rounded-left L = (x : ℤ[1/2]) → (x ∈ L ⇔ (∃ p ꞉ ℤ[1/2] , (x < p) × p ∈ L))

 rounded-right : (R : 𝓟 ℤ[1/2]) → 𝓤₀ ̇
 rounded-right R = (x : ℤ[1/2]) → x ∈ R ⇔ (∃ q ꞉ ℤ[1/2] , (q < x) × q ∈ R)

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

Now we can introduce notation to obtain specific cuts, or refer to a
rational inhabiting a cut. This is useful for readability purposes.

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
 inhabited-from-real-L ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located) = inhab-L

 inhabited-from-real-R : (x : ℝ-d) → inhabited-right (upper-cut-of x)
 inhabited-from-real-R ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located) = inhab-R

 rounded-from-real-L1 : (x : ℝ-d) → (k : ℤ[1/2]) → k ∈ lower-cut-of x → ∃ p ꞉ ℤ[1/2] , k < p × p ∈ lower-cut-of x
 rounded-from-real-L1 ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located) k = pr₁ (rounded-L k)

 rounded-from-real-L2 : (x : ℝ-d) → (k : ℤ[1/2]) → ∃ p ꞉ ℤ[1/2] , k < p × p ∈ lower-cut-of x → k ∈ lower-cut-of x
 rounded-from-real-L2 ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located) k = pr₂ (rounded-L k)

 rounded-from-real-R1 : (x : ℝ-d) → (k : ℤ[1/2]) → k ∈ upper-cut-of x → ∃ q ꞉ ℤ[1/2] , q < k × q ∈ upper-cut-of x
 rounded-from-real-R1 ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located) k = pr₁ (rounded-R k)

 rounded-from-real-R2 : (x : ℝ-d) → (k : ℤ[1/2]) → ∃ q ꞉ ℤ[1/2] , q < k × q ∈ upper-cut-of x → k ∈ upper-cut-of x
 rounded-from-real-R2 ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located) k = pr₂ (rounded-R k)

 located-from-real : (x : ℝ-d) → (p q : ℤ[1/2]) → p < q → p ∈ lower-cut-of x ∨ q ∈ upper-cut-of x
 located-from-real ((L , R) , inhab-L , inhab-R , rounded-L , rounded-R , disjoint , located) = located
 
 instance
  Strict-Order-ℤ[1/2]-ℝ-d : Strict-Order ℤ[1/2] ℝ-d
  _<_ {{Strict-Order-ℤ[1/2]-ℝ-d}} = in-lower-cut

  Strict-Order-ℝ-d-ℤ[1/2] : Strict-Order ℝ-d ℤ[1/2]
  _<_ {{Strict-Order-ℝ-d-ℤ[1/2]}} = λ y q → in-upper-cut q y

```
The following proofs are incomplete, but can be completed easily by
modelling the proofs in the DedekindReals.lagda file which uses usual
rationals.

```agda

 ℝ-d-left-cut-equal-gives-right-cut-equal : (x y : ℝ-d)
                                          → lower-cut-of x ＝ lower-cut-of y
                                          → upper-cut-of x ＝ upper-cut-of y
 ℝ-d-left-cut-equal-gives-right-cut-equal x y lx＝ly with ⊆-refl-consequence (lower-cut-of x) (lower-cut-of y) lx＝ly 
 ... | (lx⊆ly , ly⊆lx) = subset-extensionality (pe 𝓤₀) (fe 𝓤₀ 𝓤₁) rx⊆ry {!ry⊆rx!}
  where
   rx⊆ry : upper-cut-of x ⊆ upper-cut-of y
   rx⊆ry q q∈Rx = ∥∥-rec (∈-is-prop (upper-cut-of y) q) I (rounded-from-real-R1 x q q∈Rx)
    where
     I : Σ k ꞉ ℤ[1/2] , k < q × k ∈ upper-cut-of x → q ∈ upper-cut-of y
     I (k , (k<q , x<k)) = ∥∥-rec (∈-is-prop (upper-cut-of y) q) II (located-from-real y k q k<q)
      where
       II : k ∈ lower-cut-of y ∔ q ∈ upper-cut-of y → q ∈ upper-cut-of y
       II (inl k<y) = 𝟘-elim {!ℤ[1/2]<-not-itself!}
       II (inr y<q) = {!!}



 ℝ-d-equality-from-left-cut : {x y : ℝ-d}
                            → lower-cut-of x ⊆ lower-cut-of y
                            → lower-cut-of y ⊆ lower-cut-of x
                            → x ＝ y
 ℝ-d-equality-from-left-cut { x } { y } Lx⊆Ly Ly⊆Lx = {!!}

 embedding-ℤ[1/2]-to-ℝ-d : ℤ[1/2] → ℝ-d
 embedding-ℤ[1/2]-to-ℝ-d z = (L , R) , {!!}
  where
   L : 𝓟 ℤ[1/2]
   L p = p < z , <ℤ[1/2]-is-prop p z
   R : 𝓟 ℤ[1/2]
   R q = z < q , <ℤ[1/2]-is-prop z q

 instance
  canonical-map-ℤ[1/2]-to-ℝ-d : Canonical-Map ℤ[1/2] ℝ-d
  ι {{canonical-map-ℤ[1/2]-to-ℝ-d}} = embedding-ℤ[1/2]-to-ℝ-d

```

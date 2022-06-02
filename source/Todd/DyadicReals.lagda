This files defines Dedekind reals using Dyadic Rationals.

\begin{code}

{-# OPTIONS --allow-unsolved-metas #-}

open import SpartanMLTT renaming (_+_ to _∔_)

open import CanonicalMapNotation
open import OrderNotation
open import UF-FunExt
open import UF-PropTrunc
open import UF-Powerset

module Todd.DyadicReals
  (pt : propositional-truncations-exist)
  (fe : FunExt)
 where

 open PropositionalTruncation pt
 open import Todd.RationalsDyadic fe

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

 lower-cut-of : ℝ-d → 𝓟 ℤ[1/2]
 lower-cut-of ((L , R) , _) = L

 upper-cut-of : ℝ-d → 𝓟 ℤ[1/2]
 upper-cut-of ((L , R) , _) = R

 in-lower-cut : ℤ[1/2] → ℝ-d → 𝓤₀ ̇
 in-lower-cut q ((L , R) , _) = q ∈ L

 in-upper-cut : ℤ[1/2] → ℝ-d → 𝓤₀ ̇
 in-upper-cut q ((L , R) , _) = q ∈ R

 ℝ-d-equality-from-left-cut : {x y : ℝ-d}
                            → lower-cut-of x ⊆ lower-cut-of y
                            → lower-cut-of y ⊆ lower-cut-of x
                            → x ≡ y
 ℝ-d-equality-from-left-cut { x } { y } Lx⊆Ly Ly⊆Lx = {!!}

 instance
  Strict-Order-ℤ[1/2]-ℝ-d : Strict-Order ℤ[1/2] ℝ-d
  _<_ {{Strict-Order-ℤ[1/2]-ℝ-d}} = in-lower-cut

  Strict-Order-ℝ-d-ℤ[1/2] : Strict-Order ℝ-d ℤ[1/2]
  _<_ {{Strict-Order-ℝ-d-ℤ[1/2]}} = λ y q → in-upper-cut q y

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

\end{code}

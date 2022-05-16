
\begin{code}

{-# OPTIONS --allow-unsolved-metas #-}

open import SpartanMLTT renaming (_+_ to _∔_)
open import IntegersB
open import IntegersAddition
open import IntegersOrder
open import Todd.TernaryBoehmDef
open import UF-FunExt
open import UF-Powerset
open import UF-PropTrunc
open import UF-Subsingletons

module Todd.TernaryBoehmDyadicReals
  (pt : propositional-truncations-exist)
  (fe : FunExt) 
 where

open import Todd.RationalsDyadic fe

\end{code}

First, we define the properties of the dyadic rationals which we may wish to use.

\begin{code}

record DyadicProperties : 𝓤₁ ̇ where
 field
  _ℤ[1/2]+_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]+-comm  : commutative _ℤ[1/2]+_
  ℤ[1/2]+-assoc : associative _ℤ[1/2]+_
  ℤ[1/2]-       : ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]+-inv   : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x ℤ[1/2]+ y) ≡ 0ℤ[1/2]
  _ℤ[1/2]*_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]-comm   : commutative _ℤ[1/2]*_
  ℤ[1/2]-assoc  : associative _ℤ[1/2]*_
  _<_           : ℤ[1/2] → ℤ[1/2] → 𝓤₀ ̇

open PropositionalTruncation pt
module _
  (DyPr : DyadicProperties)
 where

 open DyadicProperties DyPr

\end{code}

Now, we introduce the reals defined using dyadic rationals. Dyadic
rationals are dense, so should be a good foundation for the reals, and
correlate well with the ternary Boehm reals.

\begin{code}

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
 
 brick_on-level_ : ℤ → ℤ → ℤ[1/2] × ℤ[1/2]
 brick k on-level n = (normalise (k , predℤ n)) , (normalise (k + pos 2 , predℤ n))

 encoding_at-level_ : 𝕂 → ℤ → ℤ[1/2] × ℤ[1/2]
 encoding (x , _) at-level n = brick (x n) on-level n

 open import IntegersOrder
 open import IntegersMultiplication
 
  -- Could use alternative definition here, but since (a < b) ⇔ (2ᵃ < 2ᵇ), we can be simple
  
 _≤ℤ[1/2]_ _<ℤ[1/2]_ : ℤ[1/2] → ℤ[1/2] → 𝓤₀ ̇ 
 ((x , n) , _) ≤ℤ[1/2] ((y , m) , _) = (x * pos m) ≤ℤ (y * pos n)
 ((x , n) , _) <ℤ[1/2] ((y , m) , _) = (x * pos m) <ℤ (y * pos n)

 ≤ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x ≤ℤ[1/2] y)
 ≤ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _) = ℤ≤-is-prop (x * pos b) (y * pos a)

 <ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x <ℤ[1/2] y)
 <ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _) = ℤ<-is-prop (x * pos b) (y * pos a)

 _⊂_ : ℤ[1/2] × ℤ[1/2] → ℤ[1/2] × ℤ[1/2] → 𝓤₀ ̇ 
 (a , b) ⊂ (c , d) = ((c ≤ℤ[1/2] a) × (d <ℤ[1/2] b))
                   ∔ ((c <ℤ[1/2] a) × (d ≤ℤ[1/2] b))

 encoding-structural : (x : 𝕂) → (n : ℤ)
                     → (encoding x at-level (succℤ n)) ⊂ (encoding x at-level n)
 encoding-structural (x , b) n = {!!}

 ⟦_⟧ : 𝕂 → ℝ-d
 ⟦ x , b ⟧ = (L , R) , {!!}
  where
   L R : 𝓟 ℤ[1/2]
   L ((k , n) , _) = {!!} , {!!} -- ? (k , n) <ℤ[1/2] pr₁ (encoding ? at-level ?)
   R ((k , n) , _) = ({!!} <ℤ {!!}) , ℤ<-is-prop {!!} {!!} -- pr₂ (encoding x at-level n) <ℤ (k , n)
 
\end{code}


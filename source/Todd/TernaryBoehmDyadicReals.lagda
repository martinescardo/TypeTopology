
\begin{code}

{-# OPTIONS --allow-unsolved-metas #-}

open import SpartanMLTT renaming (_+_ to _∔_)
open import OrderNotation
open import IntegersB
open import IntegersAddition
open import IntegersOrder
open import IntegersMultiplication
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


  -- Could use alternative definition here, but since (a < b) ⇔ (2ᵃ < 2ᵇ), we can be simple
  
_≤ℤ[1/2]_ _<ℤ[1/2]_ : ℤ[1/2] → ℤ[1/2] → 𝓤₀ ̇ 
((x , n) , _) ≤ℤ[1/2] ((y , m) , _) = (x * pos m) ≤ℤ (y * pos n)
((x , n) , _) <ℤ[1/2] ((y , m) , _) = (x * pos m) <ℤ (y * pos n)

instance
 Order-ℤ[1/2]-ℤ[1/2] : Order ℤ[1/2] ℤ[1/2]
 _≤_ {{Order-ℤ[1/2]-ℤ[1/2]}} = _≤ℤ[1/2]_

instance
 Strict-Order-ℤ[1/2]-ℤ[1/2] : Strict-Order ℤ[1/2] ℤ[1/2]
 _<_ {{Strict-Order-ℤ[1/2]-ℤ[1/2]}} = _<ℤ[1/2]_

≤ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x ≤ℤ[1/2] y)
≤ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _) = ℤ≤-is-prop (x * pos b) (y * pos a)

<ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x <ℤ[1/2] y)
<ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _) = ℤ<-is-prop (x * pos b) (y * pos a)

record OrderProperties : 𝓤₀ ̇ where
 field
  no-min : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x < y)
  no-max : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (y < x)
  dense  : (x y : ℤ[1/2]) → Σ k ꞉ ℤ[1/2] , x < k × (k < y)

open PropositionalTruncation pt
module _
  (DyPr : DyadicProperties)
  (DyOrPr : OrderProperties)
 where

 open DyadicProperties DyPr
 open OrderProperties DyOrPr

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

 _⊂_ : ℤ[1/2] × ℤ[1/2] → ℤ[1/2] × ℤ[1/2] → 𝓤₀ ̇ 
 (a , b) ⊂ (c , d) = ((c ≤ a) × (d < b))
                   ∔ ((c < a) × (d ≤ b))

-- encoding-structural : (x : 𝕂) → (n : ℤ)
--                     → (encoding x at-level (succℤ n)) ⊂ (encoding x at-level n)
-- encoding-structural (x , b) n = {!!}
 
 ⟦_⟧ : 𝕂 → ℝ-d
 ⟦ x , b ⟧ = (L , R) , inhabited-L , {!!}
  where
   L R : 𝓟 ℤ[1/2]
   L ((k , n) , lt) = let (l , r) = encoding (x , b) at-level pos (succ n)
                      in (((k , n) , lt) < l) , <ℤ[1/2]-is-prop ((k , n) , lt) l
   R ((k , n) , lt) = let (l , r) = encoding (x , b) at-level pos (succ n)
                      in (r < ((k , n) , lt)) , <ℤ[1/2]-is-prop r (((k , n) , lt))
   inhabited-L : inhabited-left L
   inhabited-L = let (l , r) = encoding (x , b) at-level pos (succ 0)
                 in let (y , y<l) = no-min l
                    in ∣ y , {!!} ∣ 
   inhabited-R : inhabited-right R
   inhabited-R = {!!}
 
\end{code}


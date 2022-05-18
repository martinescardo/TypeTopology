

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

First, we define the properties of the dyadic rationals which we may
wish to use. These are postulated for now, but are all commonly
accepted results that can be proved in the future.

\begin{code}

record DyadicProperties : 𝓤₁ ̇ where
 field
  _ℤ[1/2]+_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]+-comm  : commutative _ℤ[1/2]+_
  ℤ[1/2]+-assoc : associative _ℤ[1/2]+_
  ℤ[1/2]-_       : ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]+-inv   : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x ℤ[1/2]+ y) ≡ 0ℤ[1/2]
  _ℤ[1/2]*_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]-comm   : commutative _ℤ[1/2]*_
  ℤ[1/2]-assoc  : associative _ℤ[1/2]*_

 infix 20  ℤ[1/2]-_
 infixl 19 _ℤ[1/2]-_

 _ℤ[1/2]-_ : (p q : ℤ[1/2]) → ℤ[1/2]
 p ℤ[1/2]- q = p ℤ[1/2]+ (ℤ[1/2]- q)


  -- Could use alternative definition here, but since (a < b) ⇔ (2ᵃ < 2ᵇ), we can be simple
  
_≤ℤ[1/2]_ _<ℤ[1/2]_ : ℤ[1/2] → ℤ[1/2] → 𝓤₀ ̇ 
((x , n) , _) ≤ℤ[1/2] ((y , m) , _) = (x * pos m) ≤ℤ (y * pos n)
((x , n) , _) <ℤ[1/2] ((y , m) , _) = (x * pos m) <ℤ (y * pos n)

\end{code}

Define order notation so '<' and '≤' may be overloaded, and reduce
clutter in code. Also, proofs that order relations are propositions
follow easily from ℤ-order.

\begin{code}

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

\end{code}

We also want results about order. For now, they can be safely
postulate, but can be proved in the future.

\begin{code}

record OrderProperties : 𝓤₀ ̇ where
 field
  trans  : (x y z : ℤ[1/2]) → x < y → y < z → x < z
  no-min : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (y < x)
  no-max : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x < y)
  dense  : (x y : ℤ[1/2]) → Σ k ꞉ ℤ[1/2] , x < k × (k < y)

 trans₂ : (w x y z : ℤ[1/2]) → w < x → x < y → y < z → w < z
 trans₂ w x y z w<x x<y y<z = trans w x z w<x (trans x y z x<y y<z)

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

\end{code}

The following defines machinery to obtain the interval representation
of a Ternary Boehm object at each layer n.

\begin{code}

 brick_on-level_ : ℤ → ℤ → ℤ[1/2] × ℤ[1/2]
 brick k on-level n = (normalise (k , predℤ n)) , (normalise (succℤ (succℤ k) , predℤ n))

 encoding_at-level_ : 𝕂 → ℤ → ℤ[1/2] × ℤ[1/2]
 encoding (x , _) at-level n = brick (x n) on-level n

 difference-positive : (x y : ℤ[1/2]) → x < y → 0ℤ[1/2] < (y ℤ[1/2]- x)
 difference-positive = {!!}

 disjoint-lemma : ((x , b) : 𝕂) → (i j : ℤ)
                → pr₁ (encoding x , b at-level x i) < pr₂ (encoding x , b at-level x j)
 disjoint-lemma = {!!}

 located-lemma₁ : (p q l r : ℤ[1/2]) → (r ℤ[1/2]- l) < (q ℤ[1/2]- p)
                → p < l ∔ r < q
 located-lemma₁ = {!!}

 located-lemma₂ : ((x , b) : 𝕂) → (p : ℤ[1/2]) → 0ℤ[1/2] < p
                → ∃ k ꞉ ℤ , ((pr₂ (encoding x , b at-level x k)) ℤ[1/2]- (pr₁ (encoding x , b at-level x k))) < p
 located-lemma₂ = {!!}

 _⊂_ : ℤ[1/2] × ℤ[1/2] → ℤ[1/2] × ℤ[1/2] → 𝓤₀ ̇ 
 (a , b) ⊂ (c , d) = ((c ≤ a) × (d < b))
                   ∔ ((c < a) × (d ≤ b))

-- encoding-structural : (x : 𝕂) → (n : ℤ)
--                     → (encoding x at-level (succℤ n)) ⊂ (encoding x at-level n)
-- encoding-structural (x , b) n = {!!}

\end{code}

A dyadic rational p is on the left of the dyadic real K if there
exists some level k for which the rational is below the left side of
the interval of K on level k.  Similarly, q is on the right of K if
there exists a level k for which the rational is above the right side
of the interval of K on level k.

Left inhabitedness follows easily by identifying the left interval of
some layer of k. Choose 0 for simplicity.  Right inhabitedness follows
similarly.

Roundedness follows easily from denseness of ℤ[1/2], and transtivity of order.

Disjointedness is more difficult, and relies on a lemma which says
that the left side of any brick in the sequence defined by a Ternary
Boehm Real is smaller the the right side of any brick in the sequence.

Locatedness is fairly trivial since the intervals defined by the TBR
get smaller on higher levels, and it easy to locate intervals of
different sizes.

\begin{code}

 ⟦_⟧ : 𝕂 → ℝ-d --yadic
 ⟦ x , b ⟧ = (L , R) , inhabited-L , inhabited-R , rounded-L , rounded-R , is-disjoint , is-located
  where
   L R : 𝓟 ℤ[1/2]
   L p = (∃ k ꞉ ℤ , p < pr₁ (encoding x , b at-level x k)) , ∃-is-prop
   R q = (∃ k ꞉ ℤ , pr₂ (encoding x , b at-level x k) < q) , ∃-is-prop
   
   inhabited-L : inhabited-left L
   inhabited-L = let (l , l-is-pred) = no-min (pr₁ (encoding x , b at-level x (pos 0)))
                 in ∣ l , ∣ pos 0 , l-is-pred ∣ ∣
   inhabited-R : inhabited-right R
   inhabited-R = let (r , r-is-succ) =  no-max (pr₂ (encoding x , b at-level x (pos 0)))
                 in ∣ r , ∣ pos 0 , r-is-succ ∣ ∣

   rounded-L : rounded-left L
   rounded-L p = left-implication , right-implication
    where  
     left-implication : ∃ k ꞉ ℤ , p < pr₁ (encoding x , b at-level x k)
                      → ∃ z ꞉ ℤ[1/2] , p < z × (∃ k' ꞉ ℤ , z < pr₁ (encoding x , b at-level x k'))
     left-implication  = ∥∥-functor I
      where
       I : Σ k ꞉ ℤ , p < pr₁ (encoding x , b at-level x k)
         → Σ z ꞉ ℤ[1/2] , p < z × (∃ k' ꞉ ℤ , z < pr₁ (encoding x , b at-level x k'))
       I (k , p<l) = let (m , p<m , m<l) = dense p (pr₁ (encoding x , b at-level x k))
                     in m , p<m , ∣ k , m<l ∣
     right-implication : ∃ z ꞉ ℤ[1/2] , p < z × (∃ k' ꞉ ℤ , z < pr₁ (encoding x , b at-level x k'))
                       → ∃ k ꞉ ℤ , p < pr₁ (encoding x , b at-level x k)
     right-implication = ∥∥-rec ∃-is-prop I
      where
       I : Σ z ꞉ ℤ[1/2] , p < z × (∃ k' ꞉ ℤ , z < pr₁ (encoding x , b at-level x k'))
         → ∃ k ꞉ ℤ , p < pr₁ (encoding x , b at-level x k)
       I (z , p<z , z<l) = ∥∥-functor II z<l
        where
         II : Σ k' ꞉ ℤ , z < pr₁ (encoding x , b at-level x k')
            → Σ k ꞉ ℤ , p < pr₁ (encoding x , b at-level x k)
         II (k , z<l) = k , trans p z (pr₁ (encoding x , b at-level x k)) p<z z<l 

   rounded-R : rounded-right R
   rounded-R q = left-implication , right-implication
    where
     left-implication : ∃ k ꞉ ℤ , pr₂ (encoding x , b at-level x k) < q
                      → ∃ z ꞉ ℤ[1/2] , z < q × (∃ k' ꞉ ℤ , pr₂ (encoding x , b at-level x k') < z)
     left-implication = ∥∥-functor I
      where
       I : Σ k ꞉ ℤ , pr₂ (encoding x , b at-level x k) < q
         → Σ z ꞉ ℤ[1/2] , z < q × (∃ k' ꞉ ℤ , pr₂ (encoding x , b at-level x k') < z)
       I (k , r<z) = let (m , r<m , m<q) = dense (pr₂ (encoding x , b at-level x k)) q
                     in m , m<q , ∣ k , r<m ∣
     right-implication : ∃ z ꞉ ℤ[1/2] , z < q × (∃ k' ꞉ ℤ , pr₂ (encoding x , b at-level x k') < z)
                       → ∃ k ꞉ ℤ , pr₂ (encoding x , b at-level x k) < q 
     right-implication = ∥∥-rec ∃-is-prop I
      where
       I : Σ z ꞉ ℤ[1/2] , z < q × (∃ k' ꞉ ℤ , pr₂ (encoding x , b at-level x k') < z)
         → ∃ k ꞉ ℤ , pr₂ (encoding x , b at-level x k) < q
       I (z , z<q , r<z) = ∥∥-functor II r<z
        where
         II : Σ k' ꞉ ℤ , pr₂ (encoding x , b at-level x k') < z
            → Σ k ꞉ ℤ , pr₂ (encoding x , b at-level x k) < q
         II (k , r<z) = k , trans (pr₂ (encoding x , b at-level x k)) z q r<z z<q
      
   is-disjoint : disjoint L R
   is-disjoint p q (p<l , r<q) = I (binary-choice p<l r<q)
    where
     I : ∥ (Σ k ꞉ ℤ , p < pr₁ (encoding x , b at-level x k))
         × (Σ k' ꞉ ℤ , pr₂ (encoding x , b at-level x k') < q) ∥
       → p < q
     I = ∥∥-rec (<ℤ[1/2]-is-prop p q) II
      where
       II : (Σ k ꞉ ℤ , p < pr₁ (encoding x , b at-level x k))
          × (Σ k' ꞉ ℤ , pr₂ (encoding x , b at-level x k') < q)
          → p < q
       II ((k , p<l) , k' , r<q) = trans₂ p l r q p<l l<r r<q
        where
         l = pr₁ (encoding x , b at-level x k)
         r = pr₂ (encoding x , b at-level x k')
         l<r = disjoint-lemma (x , b) k k'

   is-located : located L R
   is-located p q p<q = ∥∥-rec ∨-is-prop I (located-lemma₂ (x , b) (q ℤ[1/2]- p) (difference-positive p q p<q))
    where
     I : Σ k ꞉ ℤ , ((pr₂ (encoding x , b at-level x k)) ℤ[1/2]- (pr₁ (encoding x , b at-level x k))) < (q ℤ[1/2]- p)
       → (L p holds) ∨ (R q holds)
     I (k , less) with located-lemma₁ p q (pr₁ (encoding x , b at-level x k)) (pr₂ (encoding x , b at-level x k)) less
     ... | inl p<l = ∣ inl ∣ k , p<l ∣ ∣
     ... | inr r<q = ∣ inr ∣ k , r<q ∣ ∣
                        
  
\end{code}


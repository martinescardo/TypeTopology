This file proves that the ternary Boehm reals are embedded in the
Dedekind reals defined using subsets of dyadic rationals.

\begin{code}

{-# OPTIONS --allow-unsolved-metas #-}

open import SpartanMLTT renaming (_+_ to _∔_)
open import CanonicalMapNotation
open import OrderNotation
open import IntegersB
open import IntegersAddition
open import IntegersOrder
open import IntegersMultiplication
open import IntegersNegation
open import UF-FunExt
open import UF-Powerset hiding (𝕋)
open import UF-PropTrunc
open import UF-Subsingletons

module Todd.TernaryBoehmDyadicReals
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
 where

open import Todd.RationalsDyadic fe
open import Todd.TernaryBoehmReals fe pe hiding (ι)

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
  ℤ[1/2]-_      : ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]+-inv   : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x ℤ[1/2]+ y) ≡ 0ℤ[1/2]
  _ℤ[1/2]*_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]-comm   : commutative _ℤ[1/2]*_
  ℤ[1/2]-assoc  : associative _ℤ[1/2]*_
  ℤ[1/2]-negation-involutive : (x : ℤ[1/2]) → x ≡ ℤ[1/2]- (ℤ[1/2]- x)
  
 infix 20  ℤ[1/2]-_
 infixl 19 _ℤ[1/2]-_

 _ℤ[1/2]-_ : (p q : ℤ[1/2]) → ℤ[1/2]
 p ℤ[1/2]- q = p ℤ[1/2]+ (ℤ[1/2]- q)

  -- Could use alternative definition here, but since (a < b) ⇔ (2ᵃ < 2ᵇ), we can be simple
  -- Perhaps we could prove this later
  
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

\end{code}

The following defines machinery to obtain the interval representation
of a Ternary Boehm object at each layer n.

\begin{code}

 brick_on-level_ : ℤ → ℤ → ℤ[1/2] × ℤ[1/2]
 brick k on-level n = (normalise (k , n)) , (normalise (succℤ (succℤ k) , n))

 encoding_at-level_ : 𝕋 → ℤ → ℤ[1/2] × ℤ[1/2]
 encoding (x , _) at-level n = brick (x n) on-level n

 li ri : 𝕋 → ℤ → ℤ[1/2]
 li t n = pr₁ (encoding t at-level n)
 ri t n = pr₂ (encoding t at-level n)

 difference-positive : (x y : ℤ[1/2]) → x < y → 0ℤ[1/2] < (y ℤ[1/2]- x)
 difference-positive = {!!}

 disjoint-lemma : ((x , b) : 𝕋) → (i j : ℤ)
                 → li (x , b) i < ri (x , b) j
 disjoint-lemma = {!!}

 located-lemma₁ : (p q l r : ℤ[1/2]) → (r ℤ[1/2]- l) < (q ℤ[1/2]- p)
                → p < l ∔ r < q
 located-lemma₁ = {!!}

 located-lemma₂ : ((x , b) : 𝕋) → (p : ℤ[1/2]) → 0ℤ[1/2] < p
                → ∃ k ꞉ ℤ , ((ri (x , b) k) ℤ[1/2]- (li (x , b) k)) < p
 located-lemma₂ = {!!}

 _⊂_ : ℤ[1/2] × ℤ[1/2] → ℤ[1/2] × ℤ[1/2] → 𝓤₀ ̇ 
 (a , b) ⊂ (c , d) = ((c ≤ a) × (d < b))
                   ∔ ((c < a) × (d ≤ b))

-- encoding-structural : (x : 𝕋) → (n : ℤ)
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

 ⟦_⟧ : 𝕋 → ℝ-d
 ⟦ x , b ⟧ = (L , R) , inhabited-L , inhabited-R , rounded-L , rounded-R , is-disjoint , is-located
  where
   L R : 𝓟 ℤ[1/2]
   L p = (∃ k ꞉ ℤ , p < li (x , b) k) , ∃-is-prop
   R q = (∃ k ꞉ ℤ , ri (x , b) k < q) , ∃-is-prop
   
   inhabited-L : inhabited-left L
   inhabited-L = let (m , m<l) = no-min (li (x , b) (pos 0))
                 in ∣ m , ∣ (pos 0) , m<l ∣ ∣
   inhabited-R : inhabited-right R
   inhabited-R = let (m , r<m) = no-max (ri (x , b) (pos 0))
                 in ∣ m , ∣ pos 0 , r<m ∣  ∣

   rounded-L : rounded-left L
   rounded-L p = left-implication , right-implication
    where  
     left-implication : ∃ k ꞉ ℤ , p < li (x , b) k
                      → ∃ z ꞉ ℤ[1/2] , p < z × (∃ k' ꞉ ℤ , z < li (x , b) k')
     left-implication  = ∥∥-functor I
      where
       I : Σ k ꞉ ℤ , p < li (x , b) k
         → Σ z ꞉ ℤ[1/2] , p < z × (∃ k' ꞉ ℤ , z < li (x , b) k')
       I (k , p<l) = let (m , p<m , m<l) = dense p (li (x , b) k)
                     in m , p<m , ∣ k , m<l ∣
     right-implication : ∃ z ꞉ ℤ[1/2] , p < z × (∃ k' ꞉ ℤ , z < li (x , b) k')
                       → ∃ k ꞉ ℤ , p < li (x , b) k
     right-implication = ∥∥-rec ∃-is-prop I
      where
       I : Σ z ꞉ ℤ[1/2] , p < z × (∃ k' ꞉ ℤ , z < li (x , b) k')
         → ∃ k ꞉ ℤ , p < li (x , b) k
       I (z , p<z , z<l) = ∥∥-functor II z<l
        where
         II : Σ k' ꞉ ℤ , z < li (x , b) k'
            → Σ k ꞉ ℤ , p < li (x , b) k
         II (k , z<l) = k , trans p z (li (x , b) k) p<z z<l 

   rounded-R : rounded-right R
   rounded-R q = left-implication , right-implication
    where
     left-implication : ∃ k ꞉ ℤ , ri (x , b) k < q
                      → ∃ z ꞉ ℤ[1/2] , z < q × (∃ k' ꞉ ℤ , ri (x , b) k' < z)
     left-implication = ∥∥-functor I
      where
       I : Σ k ꞉ ℤ , ri (x , b) k < q
         → Σ z ꞉ ℤ[1/2] , z < q × (∃ k' ꞉ ℤ , ri (x , b) k' < z)
       I (k , r<z) = let (m , r<m , m<q) = dense (ri (x , b) k) q
                     in m , m<q , ∣ k , r<m ∣
     right-implication : ∃ z ꞉ ℤ[1/2] , z < q × (∃ k' ꞉ ℤ , ri (x , b) k' < z)
                       → ∃ k ꞉ ℤ , ri (x , b) k < q 
     right-implication = ∥∥-rec ∃-is-prop I
      where
       I : Σ z ꞉ ℤ[1/2] , z < q × (∃ k' ꞉ ℤ , ri (x , b) k' < z)
         → ∃ k ꞉ ℤ , ri (x , b) k < q
       I (z , z<q , r<z) = ∥∥-functor II r<z
        where
         II : Σ k' ꞉ ℤ , ri (x , b) k' < z
            → Σ k ꞉ ℤ , ri (x , b) k < q
         II (k , r<z) = k , trans (ri (x , b) k) z q r<z z<q
      
   is-disjoint : disjoint L R
   is-disjoint p q (p<l , r<q) = I (binary-choice p<l r<q)
    where
     I : ∥ (Σ k ꞉ ℤ , p < li (x , b) k)
         × (Σ k' ꞉ ℤ , ri (x , b) k' < q) ∥
       → p < q
     I = ∥∥-rec (<ℤ[1/2]-is-prop p q) II
      where
       II : (Σ k ꞉ ℤ , p < li (x , b) k)
          × (Σ k' ꞉ ℤ , ri (x , b) k' < q)
          → p < q
       II ((k , p<l) , k' , r<q) = trans₂ p l r q p<l l<r r<q
        where
         l = li (x , b) k
         r = ri (x , b) k'
         l<r = disjoint-lemma (x , b) k k'

   is-located : located L R
   is-located p q p<q = ∥∥-rec ∨-is-prop I (located-lemma₂ (x , b) (q ℤ[1/2]- p) (difference-positive p q p<q))
    where
     I : Σ k ꞉ ℤ , ((ri (x , b) k) ℤ[1/2]- (li (x , b) k)) < (q ℤ[1/2]- p)
       → (L p holds) ∨ (R q holds)
     I (k , less) with located-lemma₁ p q (li (x , b) k) (ri (x , b) k) less
     ... | inl p<l = ∣ inl ∣ k , p<l ∣ ∣
     ... | inr r<q = ∣ inr ∣ k , r<q ∣ ∣
                        
\end{code}
map : ℤ[1/2] → 𝕋
map = {!!} -- use function called 'build-via' in TernaryBoehmReals.lagda.md

proof : ((k , p) : ℤ[1/2])
      → let x = map (k , p) in
        (i : ℤ) → i > p → pr₁ (encoding x at-level i) ≡ (k , p) 
proof = {!!}

ι : ℤ[1/2] → ℝ
ι = {!!}

want to prove that (x : ℤ[1/2]) → ⟦ map x ⟧ ≡ ι x

\begin{code}

 layer : ℤ[1/2] → ℕ
 layer ((_ , n) , _) = n
 
 map : ℤ[1/2] → 𝕋
 map ((k , δ) , _) = build-via (k , pos δ)

 proof : (z : ℤ[1/2]) → (i : ℤ) → pos (layer z) < i → li (map z) i ≡ z
 proof ((k , δ) , ϕ) i l = {!!}

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

Now, we define negation, addition and multiplication of ternary Boehm reals.

 𝕀− : (ℤ × ℤ) → (ℤ × ℤ)
 𝕀− (k , p) = ( − k − 2 , p)

 𝕋− : 𝕋 → 𝕋
 𝕋− (x , b) = (λ n → 𝕀− (x n , n)) . {!!}
 
\begin{code}

 𝕋- : 𝕋 → 𝕋
 𝕋- (x , b) = (λ n → predℤ (predℤ (- x n))) , below-proof
  where
   below-proof : (δ : ℤ) → predℤ (predℤ (- x (succℤ δ))) below predℤ (predℤ (- x δ))
   below-proof δ = {!!}
 
 _𝕋+_ : 𝕋 → 𝕋 → 𝕋
 (x , b) 𝕋+ (y , b') = {!!}

 _𝕋*_ : 𝕋 → 𝕋 → 𝕋
 (x , b) 𝕋* (y , b') = {!!}

\end{code}

We also require the same operations for Dyadic Reals.

\begin{code}

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
   L p = (∃ (r , s) ꞉ ℤ[1/2] × ℤ[1/2] , r ∈ lower-cut-of x × s ∈ lower-cut-of y × (p ≡ r ℤ[1/2]+ s)) , ∃-is-prop
   R q = (∃ (r , s) ꞉ ℤ[1/2] × ℤ[1/2] , r ∈ upper-cut-of x × s ∈ upper-cut-of y × (q ≡ r ℤ[1/2]+ s)) , ∃-is-prop

 _ℝd*_ : ℝ-d → ℝ-d → ℝ-d
 x ℝd* y = {!!}

\end{code}

The result we are now interested in is proving that these operations
on TBR and Dedekind reals correlate.

\begin{code}

 ℤ[1/2]<-swap : (x y : ℤ[1/2]) → x < y ⇔ (ℤ[1/2]- y) < (ℤ[1/2]- x)
 ℤ[1/2]<-swap = {!!}

 open import UF-Base

 {-
 negation-commutes-lemma₁ : (k : 𝕋) → (n : ℤ)
                          → pr₂ (encoding k at-level n) ≡ (ℤ[1/2]- pr₁ (encoding 𝕋- k at-level n))
 negation-commutes-lemma₁ = {!!}

 negation-commutes-lemma₂ : (k : 𝕋) → (n : ℤ)
                          → ℤ[1/2]- (pr₂ (encoding k at-level n)) ≡ pr₁ (encoding 𝕋- k at-level n)
 negation-commutes-lemma₂ = {!!}
 
 negation-commutes : (x : 𝕋) → ⟦ 𝕋- x ⟧ ≡ ℝd- ⟦ x ⟧
 negation-commutes z = ℝ-d-equality-from-left-cut Ll⊆Lr Lr⊆Ll
  where
   Ll⊆Lr : lower-cut-of ⟦ 𝕋- z ⟧ ⊆ lower-cut-of (ℝd- ⟦ z ⟧)
   Ll⊆Lr p = ∥∥-functor I
    where
     I : Σ n ꞉ ℤ , p < pr₁ (encoding 𝕋- z at-level n)
       → Σ n ꞉ ℤ , pr₂ (encoding z at-level n) < (ℤ[1/2]- p)
     I (n , p<l) = let (left-imp , right-imp) = ℤ[1/2]<-swap p (pr₁ (encoding 𝕋- z at-level n))
                   in n , transport (_< (ℤ[1/2]- p)) II (left-imp p<l)
      where
       II : ℤ[1/2]- pr₁ (encoding 𝕋- z at-level n) ≡ pr₂ (encoding z at-level n)
       II = negation-commutes-lemma₁ z n ⁻¹                 
 
   Lr⊆Ll : lower-cut-of (ℝd- ⟦ z ⟧) ⊆ lower-cut-of ⟦ 𝕋- z ⟧
   Lr⊆Ll p = ∥∥-functor I
    where
     I : Σ n ꞉ ℤ , pr₂ (encoding z at-level n) < (ℤ[1/2]- p)
       → Σ n ꞉ ℤ , p < pr₁ (encoding 𝕋- z at-level n)
     I (n , r<-p) = let (left-imp , right-imp) = ℤ[1/2]<-swap (pr₂ (encoding z at-level n)) (ℤ[1/2]- p)
                    in n , (transport₂ _<_ (ℤ[1/2]-negation-involutive p ⁻¹) II (left-imp r<-p))
      where
       II : ℤ[1/2]- (pr₂ (encoding z at-level n)) ≡ pr₁ (encoding 𝕋- z at-level n)
       II = negation-commutes-lemma₂ z n
 
 
 addition-commutes : (x y : 𝕋) → ⟦ x 𝕋+ y ⟧ ≡ (⟦ x ⟧ ℝd+ ⟦ y ⟧)
 addition-commutes x y = ℝ-d-equality-from-left-cut Ll⊆Lr Lr⊆Ll
  where
   Ll⊆Lr : lower-cut-of ⟦ x 𝕋+ y ⟧ ⊆ lower-cut-of (⟦ x ⟧ ℝd+ ⟦ y ⟧)
   Ll⊆Lr p = ∥∥-functor I
    where
     I : Σ n ꞉ ℤ , (p < li (x 𝕋+ y) n)
       → Σ (r , s) ꞉ ℤ[1/2] × ℤ[1/2] , r < ⟦ x ⟧ × s < ⟦ y ⟧ × (p ≡ r ℤ[1/2]+ s)
     I (n , p<x+y) = {!!}

   Lr⊆Ll : lower-cut-of (⟦ x ⟧ ℝd+ ⟦ y ⟧) ⊆ lower-cut-of ⟦ x 𝕋+ y ⟧
   Lr⊆Ll p p∈x'+y' = ∥∥-rec ∃-is-prop I p∈x'+y'
    where
     I : Σ (r , s) ꞉ ℤ[1/2] × ℤ[1/2] , r < ⟦ x ⟧ × s < ⟦ y ⟧ × (p ≡ r ℤ[1/2]+ s)
       → ∃ n ꞉ ℤ , (p < li (x 𝕋+ y) n)      
     I ((r , s) , r<x' , s<y' , e) = ∥∥-functor II (binary-choice r<x' s<y') 
      where
       II : (Σ k  ꞉ ℤ , r < li x k)
          × (Σ k' ꞉ ℤ , s < li y k')
          → Σ n ꞉ ℤ , (p < li (x 𝕋+ y) n) 
       II = {!!}
   
 multiplication-commutes : (x y : 𝕋) → ⟦ x 𝕋* y ⟧ ≡ (⟦ x ⟧ ℝd* ⟦ y ⟧)
 multiplication-commutes = {!!}

 -}

\end{code}




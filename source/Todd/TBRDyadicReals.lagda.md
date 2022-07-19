This file proves that the ternary Boehm reals are embedded in the
Dedekind reals defined using subsets of dyadic rationals.

```agda

{-# OPTIONS --allow-unsolved-metas #-}

open import SpartanMLTT renaming (_+_ to _∔_)
open import CanonicalMapNotation
open import OrderNotation
open import IntegersB
open import IntegersAddition
open import IntegersOrder
open import IntegersMultiplication
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import NaturalsMultiplication renaming (_*_ to _*ℕ_)
open import IntegersNegation
open import UF-Base
open import UF-FunExt
open import UF-Powerset hiding (𝕋)
open import UF-PropTrunc
open import UF-Subsingletons
open import UF-Quotient

module Todd.TBRDyadicReals
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
  (sq : set-quotients-exist)
 where

open import Todd.BelowAndAbove fe using (below-implies-below' ; _below'_ ; below'-implies-below)
open import Todd.DyadicReals pe pt fe
open import Todd.RationalsDyadic fe
open import Todd.TernaryBoehmRealsPrelude fe
open import Todd.TernaryBoehmReals pt fe pe sq hiding (ι ; _≤_≤_)

DyOrPr : OrderProperties
DyOrPr = {!!}

open OrderProperties DyOrPr
open DyadicProperties Dp
open PropositionalTruncation pt


```

The following defines machinery to obtain the interval representations
of a TBR at each layer n.

The function encoding t at-level n finds the interval representation
of a TBR at level n. For example, consider the TBR which defines the
real number 1, we have:

encoding 1𝕋 at-level (negsucc 0) = brick (pos 0) at-level (negsucc 0) = [0 , 4]
encoding 1𝕋 at-level (pos 0)     = brick (pos 1) at-level (pos 0)     = [1 , 3] 
encoding 1𝕋 at-level (pos 1)     = brick (pos 2) at-level (pos 1)     = [1 , 2]
encoding 1𝕋 at-level (pos 2)     = brick (pos 4) at-level (pos 2)     = [1 , 1.5]

We also have notation which grabs the left or right bound of an
encoding at some level.

```agda
--level 0 width 2
brick_on-level_ : ℤ → ℤ → ℤ[1/2] × ℤ[1/2]
brick k on-level n = (normalise (k , n)) , (normalise (succℤ (succℤ k) , n))

lb-of-brick_on-level_ rb-of-brick_on-level_ : ℤ → ℤ → ℤ[1/2]
lb-of-brick k on-level n = pr₁ (brick k on-level n)
rb-of-brick k on-level n = pr₂ (brick k on-level n)

encoding_at-level_ : 𝕋 → ℤ → ℤ[1/2] × ℤ[1/2]
encoding (x , _) at-level n = brick (x n) on-level n

lb rb : 𝕋 → ℤ → ℤ[1/2]
lb x n = pr₁ (encoding x at-level n)
rb x n = pr₂ (encoding x at-level n)

```
The following proofs are needed to define the injection of TBR's into
Dedekind reals. The function disjoint-lemma is the proof that for any
TBR, the left bound of the TBR is always less than the right
bound. The is true since on any specific level, the two bounds are
apart, with the left bound smaller than the right bound. On successive
levels, one or both of the bounds move closer to the other, forever or
until one of the bounds is the same as the real number defined by the
TBR. At this point this bound remains the same; it cannot change
otherwise the real number would be "chopped out" of the
interval. Hence the other point gets increasingly closer the other. A
pictorial example:

  (                                        |                                                                                        )
  (                                        |                        )
                                  (        |                        )
                                          (|                )
                                          (|        )
                                          (|    )
                                          (|  )
                                          (| )
                                          (|)

```agda

disjoint-lemma : (x : 𝕋) → (n m : ℤ) → lb x n < rb x m
disjoint-lemma x n m = {!!}

```
The function located-lemma is a simple order proof

r - l < q - p

By trichotomy, p < l or l ≤ p.

If p < l, then we are done.

If l ≤ p, then  r ≤ r + (p - l) < q, so r < q and we are done.
 

```agda

located-lemma₁ : (p q l r : ℤ[1/2]) → (r ℤ[1/2]- l) < (q ℤ[1/2]- p)
               → (p < l) ∔ (r < q)
located-lemma₁ = {!!}

```

The next lemma for located simply relies on the fact the the intervals
are successively smaller. We can always locate a TBR to an arbitrary
degree of precision.

```agda

located-lemma₂ : (t : 𝕋) → (p : ℤ[1/2]) → 0ℤ[1/2] < p
               → ∃ k ꞉ ℤ , (rb t k ℤ[1/2]- lb t k) < p
located-lemma₂ = {!!}

-- encoding-structural : (x : 𝕋) → (n : ℤ)
--                     → (encoding x at-level (succℤ n)) ⊂ (encoding x at-level n)
-- encoding-structural (x , b) n = {!!}

```

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

```agda

⟦_⟧ : 𝕋 → ℝ-d
⟦ x , b ⟧ = (L , R) , inhabited-L , inhabited-R , rounded-L , rounded-R , is-disjoint , is-located
 where
  L R : 𝓟 ℤ[1/2]
  L p = (∃ k ꞉ ℤ , p < lb (x , b) k) , ∃-is-prop
  R q = (∃ k ꞉ ℤ , rb (x , b) k < q) , ∃-is-prop

  inhabited-L : inhabited-left L
  inhabited-L = let (m , m<l) = no-min (lb (x , b) (pos 0))
                in ∣ m , ∣ (pos 0) , m<l ∣ ∣
  inhabited-R : inhabited-right R
  inhabited-R = let (m , r<m) = no-max (rb (x , b) (pos 0))
                in ∣ m , ∣ pos 0 , r<m ∣  ∣

  rounded-L : rounded-left L
  rounded-L p = left-implication , right-implication
   where  
    left-implication : ∃ k ꞉ ℤ , p < lb (x , b) k
                     → ∃ z ꞉ ℤ[1/2] , p < z × (∃ k' ꞉ ℤ , z < lb (x , b) k')
    left-implication  = ∥∥-functor I
     where
      I : Σ k ꞉ ℤ , p < lb (x , b) k
        → Σ z ꞉ ℤ[1/2] , p < z × (∃ k' ꞉ ℤ , z < lb (x , b) k')
      I (k , p<l) = let (m , p<m , m<l) = dense p (lb (x , b) k)
                    in m , p<m , ∣ k , m<l ∣
    right-implication : ∃ z ꞉ ℤ[1/2] , p < z × (∃ k' ꞉ ℤ , z < lb (x , b) k')
                      → ∃ k ꞉ ℤ , p < lb (x , b) k
    right-implication = ∥∥-rec ∃-is-prop I
     where
      I : Σ z ꞉ ℤ[1/2] , p < z × (∃ k' ꞉ ℤ , z < lb (x , b) k')
        → ∃ k ꞉ ℤ , p < lb (x , b) k
      I (z , p<z , z<l) = ∥∥-functor II z<l
       where
        II : Σ k' ꞉ ℤ , z < lb (x , b) k'
           → Σ k ꞉ ℤ , p < lb (x , b) k
        II (k , z<l) = k , trans p z (lb (x , b) k) p<z z<l 

  rounded-R : rounded-right R
  rounded-R q = left-implication , right-implication
   where
    left-implication : ∃ k ꞉ ℤ , rb (x , b) k < q
                     → ∃ z ꞉ ℤ[1/2] , z < q × (∃ k' ꞉ ℤ , rb (x , b) k' < z)
    left-implication = ∥∥-functor I
     where
      I : Σ k ꞉ ℤ , rb (x , b) k < q
        → Σ z ꞉ ℤ[1/2] , z < q × (∃ k' ꞉ ℤ , rb (x , b) k' < z)
      I (k , r<z) = let (m , r<m , m<q) = dense (rb (x , b) k) q
                    in m , m<q , ∣ k , r<m ∣
    right-implication : ∃ z ꞉ ℤ[1/2] , z < q × (∃ k' ꞉ ℤ , rb (x , b) k' < z)
                      → ∃ k ꞉ ℤ , rb (x , b) k < q 
    right-implication = ∥∥-rec ∃-is-prop I
     where
      I : Σ z ꞉ ℤ[1/2] , z < q × (∃ k' ꞉ ℤ , rb (x , b) k' < z)
        → ∃ k ꞉ ℤ , rb (x , b) k < q
      I (z , z<q , r<z) = ∥∥-functor II r<z
       where
        II : Σ k' ꞉ ℤ , rb (x , b) k' < z
           → Σ k ꞉ ℤ , rb (x , b) k < q
        II (k , r<z) = k , trans (rb (x , b) k) z q r<z z<q

  is-disjoint : disjoint L R
  is-disjoint p q (p<l , r<q) = I (binary-choice p<l r<q)
   where
    I : ∥ (Σ k ꞉ ℤ , p < lb (x , b) k)
        × (Σ k' ꞉ ℤ , rb (x , b) k' < q) ∥
      → p < q
    I = ∥∥-rec (<ℤ[1/2]-is-prop p q) II
     where
      II : (Σ k ꞉ ℤ , p < lb (x , b) k)
         × (Σ k' ꞉ ℤ , rb (x , b) k' < q)
         → p < q
      II ((k , p<l) , k' , r<q) = trans₂ p l r q p<l l<r r<q
       where
        l = lb (x , b) k
        r = rb (x , b) k'
        l<r = disjoint-lemma (x , b) k k'

  is-located : located L R
  is-located p q p<q = ∥∥-rec ∨-is-prop I (located-lemma₂ (x , b) (q ℤ[1/2]- p) (diff-positive p q p<q ))
   where
    I : Σ k ꞉ ℤ , ((rb (x , b) k) ℤ[1/2]- (lb (x , b) k)) < (q ℤ[1/2]- p)
      → (L p holds) ∨ (R q holds)
    I (k , less) with located-lemma₁ p q (lb (x , b) k) (rb (x , b) k) less
    ... | inl p<l = ∣ inl ∣ k , p<l ∣ ∣
    ... | inr r<q = ∣ inr ∣ k , r<q ∣ ∣

```

We now define a map from dyadic rationals to TBRs. We wish to show
that for any TBR, the embedding of the dyadic rational into the
Dedekind reals is equivalent to the embedding of the TBR defined by
mapping the dyadic rational to a TBR.

More succintly, we prove that (x : ℤ[1/2]) → ⟦ map x ⟧ ≡ ι x. This
requires numerous lemmas regarding normalise, the map, and the bounds
on each level of a TBR.

```agda

layer : ℤ[1/2] → ℕ
layer ((_ , n) , _) = n

map : ℤ[1/2] → 𝕋
map ((k , δ) , _) = build-via (k , pos δ)

map-lemma : (z : ℤ[1/2]) → (i : ℤ) → pos (layer z) < i → lb (map z) i ≡ z
map-lemma ((k , δ) , p) i δ<i with ℤ-trichotomous i (pos δ)
... | inl i<δ       = 𝟘-elim (ℤ-equal-not-less-than i (ℤ<-trans i (pos δ) i i<δ δ<i))
... | inr (inl i≡δ) = 𝟘-elim (ℤ-equal-not-less-than i (transport (_< i) (i≡δ ⁻¹) δ<i))
... | inr (inr (n , refl)) with even-or-odd? (downLeft k)
... | inr odd-2k = 𝟘-elim (times-two-even' k odd-2k)
map-lemma ((k , δ) , p) i δ<i | inr (inr (n , refl)) | inl even-2k = normalise-lemma k δ n p

map-lemma-≤ : (z : ℤ[1/2]) → (i : ℤ) → pos (layer z) ≤ i → lb (map z) i ≡ z
map-lemma-≤ ((k , δ) , p) i δ≤i with ℤ≤-split (pos δ) i δ≤i
... | inl δ<i = map-lemma ((k , δ) , p) i δ<i
... | inr refl with ℤ-trichotomous (pos δ) (pos δ)
... | inl δ<δ = 𝟘-elim (ℤ-equal-not-less-than (pos δ) δ<δ)
... | inr (inr δ<δ) = 𝟘-elim (ℤ-equal-not-less-than (pos δ) δ<δ)
... | inr (inl δ≡δ) = to-subtype-≡ (λ (z , n) → ℤ[1/2]-cond-is-prop z n) (ap pr₁ (lowest-terms-normalised ((k , δ) , p)))

lim₄ : (x' x : ℤ) (n : ℕ) → x' below' x → x * pos (2^ (succ n)) ≤ x' * pos (2^ n)
lim₄ x' x n (inl x'≡2x)         = transport (λ z → x * pos (2^ (succ n)) ≤ z * pos (2^ n)) (x'≡2x ⁻¹) (lim₁ x n) 
lim₄ x' x n (inr (inl x'≡2x+1)) = transport (λ z → x * pos (2^ (succ n)) ≤ z * pos (2^ n)) (x'≡2x+1 ⁻¹) (lim₂ x n)
lim₄ x' x n (inr (inr x'≡2x+2)) = transport (λ z → x * pos (2^ (succ n)) ≤ z * pos (2^ n)) (x'≡2x+2 ⁻¹) (lim₃ x n)

left-interval-monotonic' : (t : 𝕋) → (n : ℤ) → lb t n ≤ lb t (succℤ n)
left-interval-monotonic' (x , b) (pos n) = normalise-≤ ((x (pos n)) , n) (x (pos (succ n)) , succ n)
                                  (lim₄ (x (pos (succ n))) (x (pos n)) n
                                   (below-implies-below' (x (pos (succ n))) (x (pos n)) (b (pos n))))
left-interval-monotonic' (x , b) (negsucc 0) with below-implies-below' (x (pos 0)) (x (negsucc 0)) (b (negsucc 0))
... | inl e = 0 , (e ⁻¹)
... | inr (inl e) = 1 , (e ⁻¹)
... | inr (inr e) = 2 , (e ⁻¹)
left-interval-monotonic' (x , b) (negsucc (succ n)) = normalise-≤' (x (negsucc (succ n)) , (succ n)) (x (negsucc n) , n)
                                                       (lim₄ (x (negsucc n)) (x (negsucc (succ n))) (succ n)
                                                        (below-implies-below' (x (negsucc n)) (x (negsucc (succ n))) (b (negsucc (succ n)))))

```

With the above lemmas we can prove that for any TBR, the bound
represented by the left edge of the brick on each precision can only
increase.


```agda

left-interval-monotonic : (x : ℤ[1/2]) → (n : ℤ) → lb (map x) n ≤ lb (map x) (succℤ n)
left-interval-monotonic x n = left-interval-monotonic' (map x) n

```

We also prove that the left bound on each level is never greater than
the dyadic rational that the TBR represents, by induction on the layers.

The general idea is this:

n             b

n+1   2b    2b+1    2b+2

On level n+1, 2b, 2b+1 and 2b+2 are below b.

But on level n, the left side of brick b represents b/2ⁿ
On level n+1, it represents 2b/2ⁿ⁺¹ ≡ b/2ⁿ ≤ b/2ⁿ.

Clearly (b / 2ⁿ) ≤ (2b /2ⁿ⁺¹) < (2b + 1 /2ⁿ⁺¹) < (2b + 2 /2ⁿ⁺¹).

For a precision level n+k, simply prove inductively using the above argument.


```agda

left-interval-is-minimum-lemma : (x : ℤ[1/2]) → (n : ℤ) (m : ℕ) → succℤ n + pos m ≡ pos (layer x) → lb (map x) n ≤ x 
left-interval-is-minimum-lemma x n 0 e = transport (lb (map x) n ≤_) I II
 where
  I : lb (map x) (succℤ n) ≡ x
  I = map-lemma-≤ x (succℤ n) (0 , (e ⁻¹))
  II : lb (map x) n ≤ lb (map x) (succℤ n)
  II = left-interval-monotonic x n
left-interval-is-minimum-lemma x n (succ m) e = trans' (lb (map x) n) (lb (map x) (succℤ n)) x (left-interval-monotonic x n) I
 where
  I : lb (map x) (succℤ n) ≤ x
  I = left-interval-is-minimum-lemma x (succℤ n) m (ℤ-left-succ (succℤ n) (pos m) ∙ e) 

left-interval-is-minimum : (x : ℤ[1/2]) → (n : ℤ) → lb (map x) n ≤ x
left-interval-is-minimum ((x , δ) , p) n with ℤ-trichotomous (pos δ) n
... | inl δ<n = transport (_≤ ((x , δ) , p)) (map-lemma ((x , δ) , p) n δ<n ⁻¹) (≤-refl ((x , δ) , p))
... | inr (inl refl) = transport (_≤ ((x , δ) , p)) (map-lemma-≤ (((x , δ) , p)) n (ℤ≤-refl (pos δ)) ⁻¹) (≤-refl ((x , δ) , p))
... | inr (inr (m , e)) = left-interval-is-minimum-lemma (((x , δ) , p)) n m e

```

With these lemmas, we can finally prove that the encodings agree with the reals.
Recall that proving that two reals are equal can be reduced to proving
that the left cut of each real is equal, and proving that two sets are
equals means proving that (z ∈ Lx ⇔ z ∈ Ly) for any z ∈ Lx ∪ Ly.

```agda

encodings-agree-with-reals : (x : ℤ[1/2]) → ⟦ map x ⟧ ≡ ι x
encodings-agree-with-reals x = ℝ-d-equality-from-left-cut left right
 where
  left : (y : ℤ[1/2]) → (∃ n ꞉ ℤ , y < lb (map x) n) → y < x
  left y = ∥∥-rec (<ℤ[1/2]-is-prop y x) λ (n , y<l) → trans<≤ y (lb (map x) n) x y<l (left-interval-is-minimum x n) 
  right : (y : ℤ[1/2]) → y < x → ∃ n ꞉ ℤ , y < lb (map x) n
  right y y<x = ∣ (pos (layer x) , (transport (y <_) (map-lemma-≤ x (pos (layer x) ) (ℤ≤-refl (pos (layer x))) ⁻¹) y<x)) ∣

```

Now, we define negation, addition and multiplication of ternary Boehm reals.

𝕀− : (ℤ × ℤ) → (ℤ × ℤ)
𝕀− (k , p) = ( − k − 2 , p)

𝕋− : 𝕋 → 𝕋
𝕋− (x , b) = (λ n → 𝕀− (x n , n)) . {!!}

We begin with negation, being the easiest operation to define.

Notice that we cannot simple take (λ n → - x n) as our new TBR precision function. 

Recall the following brick → interval definition

⟪_⟫ : ℤ × ℤ → ℚ × ℚ
⟪ k , δ ⟫ = (k / 2^{δ - 1}) , ((k + 2) / 2^{δ - 1})

where k = x (δ) for t : 𝕋 , t = (x , b).

If we define subtraction at (λ n → - x n), then we obtain that
⟪ 𝕋- (x , b) , δ ⟫ = (- k / 2^{δ - 1} , - k - 2 / 2^{δ - 1})

```agda

𝕋- : 𝕋 → 𝕋
𝕋- (x , b) = (λ n → predℤ (predℤ (- x n))) , below-proof
 where
  below-proof : (δ : ℤ) → predℤ (predℤ (- x (succℤ δ))) below predℤ (predℤ (- x δ))
  below-proof δ with b (x δ)
  ... | below with ℤ≤-swap₂ (x δ * pos 2) (x (succℤ δ)) (x δ * pos 2 + pos 2) (b δ) 
  ... | l₁ , l₂ = transport (_≤ℤ predℤ (predℤ (- x (succℤ δ)))) I (ℤ≤-adding' (- succℤ (succℤ (x δ + x δ))) (- x (succℤ δ)) (negsucc 1) l₂) ,
                 (transport(predℤ (predℤ (- x (succℤ δ))) ≤ℤ_) II (ℤ≤-adding' (- x (succℤ δ)) (- (x δ + x δ)) (negsucc 1) l₁))
   where
    I : (- ((x δ + x δ) + pos 2)) - pos 2 ≡ (- x δ) - pos 2 + ((- x δ) - pos 2)
    I = (- (x δ + x δ + pos 2)) - pos 2         ≡⟨ ap (λ z → (- z) - pos 2) (ℤ+-assoc (x δ) (x δ) (pos 2)) ⟩
        (- (x δ + (x δ + pos 2))) - pos 2       ≡⟨ ap (_- pos 2) (negation-dist (x δ) (x δ + pos 2) ⁻¹) ⟩
        (- x δ) + (- (x δ + pos 2)) - pos 2     ≡⟨ ap (λ z → (- x δ) + (- z) - pos 2) (ℤ+-comm (x δ) (pos 2)) ⟩
        (- x δ) + (- (pos 2 + x δ)) - pos 2     ≡⟨ ap (λ z → (- x δ) + z - pos 2) (negation-dist (pos 2) (x δ) ⁻¹) ⟩
        (- x δ) + ((- pos 2) + (- x δ)) - pos 2 ≡⟨ ap (_- pos 2) (ℤ+-assoc (- x δ) (- pos 2) (- x δ) ⁻¹) ⟩
        (- x δ) - pos 2 + (- x δ) - pos 2       ≡⟨ ℤ+-assoc ((- x δ) - pos 2) (- x δ) (- pos 2) ⟩
        (- x δ) - pos 2 + ((- x δ) - pos 2)     ∎
    II : (- (x δ + x δ)) - pos 2 ≡ ((- x δ) - pos 2) + ((- x δ) - pos 2) + pos 2
    II = (- (x δ + x δ)) - pos 2                           ≡⟨ ap (_- pos 2) (negation-dist (x δ) (x δ) ⁻¹) ⟩
         (- x δ) + (- x δ) - pos 2                         ≡⟨ ℤ+-assoc (- x δ) (- x δ) (- pos 2) ⟩
         (- x δ) + ((- x δ) - pos 2)                       ≡⟨ ap ((- x δ) +_) (ℤ+-comm (- x δ) (- pos 2)) ⟩
         (- x δ) + ((- pos 2) + (- x δ))                   ≡⟨ ℤ+-assoc (- (x δ)) (- pos 2) (- x δ) ⁻¹ ⟩
         (- x δ) - pos 2 - x δ                             ≡⟨ ap (λ z → (- x δ) - pos 2 + ((- x δ) + z)) (ℤ-sum-of-inverse-is-zero' (pos 2) ⁻¹) ⟩
         (- x δ) - pos 2 + ((- x δ) + ((- pos 2) + pos 2)) ≡⟨ ap (λ z → (- x δ) - pos 2 + z) (ℤ+-assoc (- x δ) (- pos 2) (pos 2) ⁻¹) ⟩
         (- x δ) - pos 2 + ((- x δ) - pos 2 + pos 2)       ≡⟨ ℤ+-assoc ((- x δ) - pos 2) ((- x δ) - pos 2) (pos 2) ⁻¹ ⟩
         (- x δ) - pos 2 + ((- x δ) - pos 2) + pos 2       ∎

open import Todd.BelowLemmas pt fe pe sq

_𝕋+_ : 𝕋 → 𝕋 → 𝕋
(x , b) 𝕋+ (y , b') = (λ n → upRight (upRight ((x (n +pos 2)) + (y (n +pos 2))))) , λ δ → below-upRight (x , b) (y , b') (δ + pos 2)

{-
_𝕋*_ : 𝕋 → 𝕋 → 𝕋
(x , b) 𝕋* (y , b') = {!!}
-}

```

We also require the same operations for Dyadic Reals.

```agda

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

{-
_ℝd*_ : ℝ-d → ℝ-d → ℝ-d
x ℝd* y = {!!}
-}
```

The result we are now interested in is proving that these operations
on TBR and Dedekind reals correlate.

For example, in the case of negation, we want to prove that the encoding of the negation of an tbr is equal to negation of the encoding.⌞

```agda

postulate
 negation : (x k : ℤ) → ℤ[1/2]- (normalise (x , k)) ≡ normalise (- x , k) 

bound-flip₁ : (x : 𝕋) → (k : ℤ) → ℤ[1/2]- lb (𝕋- x) k ≡ rb x k
bound-flip₁ (x , b) k = II
 where
  I : - ((- x k) - pos 2) ≡ x k + pos 2
  I = - ((- x k) - pos 2)         ≡⟨ negation-dist (- x k) (- pos 2) ⁻¹ ⟩
      (- (- x k)) + (- (- pos 2)) ≡⟨ ap₂ _+_ (minus-minus-is-plus (x k)) (minus-minus-is-plus (pos 2)) ⟩
      x k + pos 2 ∎

  II : ℤ[1/2]- normalise ((- x k) - pos 2 , k) ≡ normalise (x k + pos 2 , k)
  II = (ℤ[1/2]- normalise ((- x k) - pos 2 , k)) ≡⟨ negation ((- x k) - pos 2) k ⟩
       normalise (- ((- x k) - pos 2) , k)       ≡⟨ ap (λ z → normalise (z , k)) I ⟩
       normalise (x k + (pos 2) , k)             ∎

bound-flip₂ : (x : 𝕋) → (k : ℤ) → ℤ[1/2]- rb x k ≡ lb (𝕋- x) k
bound-flip₂ x k = (ℤ[1/2]- rb x k)                ≡⟨ ap ℤ[1/2]-_ (bound-flip₁ x k ⁻¹) ⟩
                  (ℤ[1/2]- (ℤ[1/2]- lb (𝕋- x) k)) ≡⟨ ℤ[1/2]-negation-involutive (lb (𝕋- x) k) ⁻¹ ⟩
                  lb (𝕋- x) k                     ∎

tbr-negation-agrees : (x : 𝕋) → ⟦ 𝕋- x ⟧ ≡ ℝd- ⟦ x ⟧
tbr-negation-agrees x = ℝ-d-equality-from-left-cut left right
 where
  left : (p : ℤ[1/2]) → ∃ k ꞉ ℤ  , p < lb (𝕋- x) k → ∃ k ꞉ ℤ , (rb x k) < (ℤ[1/2]- p)
  left p = ∥∥-functor I
   where
    I : Σ k ꞉ ℤ  , p < lb (𝕋- x) k
      → Σ k ꞉ ℤ , (rb x k) < (ℤ[1/2]- p)
    I (k , p<l) = k , transport
                       (_< (ℤ[1/2]- p))
                        (bound-flip₁ x k)
                         (<-swap p (lb (𝕋- x) k) p<l) 

  right : (p : ℤ[1/2]) → ∃ k ꞉ ℤ , (rb x k) < (ℤ[1/2]- p) → ∃ k ꞉ ℤ  , p < lb (𝕋- x) k
  right p = ∥∥-functor I
   where
    I : Σ k ꞉ ℤ , (rb x k) < (ℤ[1/2]- p) → Σ k ꞉ ℤ  , p < lb (𝕋- x) k
    I (k , r<-p) = k , transport₂
                        _<_
                         (ℤ[1/2]-negation-involutive p ⁻¹)
                          (bound-flip₂ x k)
                           (<-swap (rb x k) (ℤ[1/2]- p) r<-p)


```
Attempts to generalise operations on TBR

```agda

monotonic : (f : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]) → 𝓤₀ ̇ -- May need to be commutative? Probably not though
monotonic f = ∀ x y z → (y < z → f x y ≤ f x z)   -- Unless I have defined this wrong, multiplication does not satisfy monotonicity.
                      ∔ (y < z → f x z ≤ f x y)

_⊂_ : ℤ[1/2] × ℤ[1/2] → ℤ[1/2] × ℤ[1/2] → 𝓤₀ ̇ 
(a , b) ⊂ (c , d) = ((c ≤ a) × (d < b))
                  ∔ ((c < a) × (d ≤ b))

-- Why not be more specific than monotonicity?

_≤_≤_ : (x y z : ℤ) → 𝓤₀ ̇
x ≤ y ≤ z = (x ≤ y) × (y ≤ z)

```
Define the type of functions which are monotonic on intervals.
```agda
{-
preserves-bounds : (f : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]) → 𝓤₀ ̇
preserves-bounds f = ∀ lb rb z → lb < rb → (∀ x → lb ≤ x ≤ rb → f lb z ≤ f x z ≤ f rb z)
                                         ∔ (∀ x → lb ≤ x ≤ rb → f rb z ≤ f x z ≤ f lb z)
-}
interval-monotonic : (f : ℤ → ℤ → ℤ) → 𝓤₀ ̇
interval-monotonic f = ∀ lb rb z → lb < rb → (∀ x → lb ≤ x ≤ rb → f lb z ≤ f x z ≤ f rb z)
                                           ∔ (∀ x → lb ≤ x ≤ rb → f rb z ≤ f x z ≤ f lb z) 

```
There are four interesting values for two tbr reals at an arbitrary
level, the bounds.  Since we are using functions which are monotonic
on intervals, we know that for two intervals, the maximum and minuinum
values of the interval operation is achieved by applying the function
to one of the bounds from each interval.

For example, addition may look like the following on some arbitrary
level n:

a  a+2    c   c+2
(   )     (    )


a+c          a+c+4
 (             )

For multiplication, the min and max values can be attained at any of
a * c , a * d , b * c , b * d.

Importantly, note that on the same arbitrary level above, if our new
ternary Boehm real returns a+c as the integer value, it may not be
correct, since a + c on this interval means our real is located in
(a + c , a + c + 2), but it's possible that the real is located at
a + c + 3, for example.

To find our real value on this level in the correct interval, we must
find the real at a higher level of precision in both intervals, and
then reconstruct an interval on the level we are interested in.

As proved above, addition is solved by finding the real to level n + 2,
which suitably bounds the interval, and by performing the upRight operation
twice, we find an interval on level n which is guaranteed to contain our real.

In the general case, we may need to find our real to much higher
degrees of precision to account for the much wider bounds when
applying operations. For example consider multiplication:

         101  103            10   12        
         (    )       x        (    )
=  
       1010                           1236
         (                             )

We want to find the real in some width two interval on this level, but
the operation gives us a width of 226.  Intuitively, the idea is to
find the same real to a much higher degree of precision, so that we
find it to an interval of width 2 on the level we want.

To answer the question of which level is necessary to achieve the
correct accuracy, we need to consider the maximum width an operation
gives. Addition gives width 4.

Multiplication gives a maximum width dependent on the values being
multiplied. In the example above, we need to go level n + 8.


```agda

successive-level-bounds : ((x , b) : 𝕋)
                        → (n : ℤ) (k : ℕ)
                        → pos (2^ (succ k)) * x n ≤ x (succℤ (n + pos k)) ≤ pos (2^ (succ k)) * x n + pos (2^ (succ (succ k))) - pos 2  
successive-level-bounds (x , b) n 0 with b n
... | l₁ , l₂ = transport (_≤ x (succℤ n)) (ℤ*-comm (x n) (pos 2)) l₁ , transport (x (succℤ n) ≤_) I l₂
 where
  I : x n * pos 2 + pos 2 ≡ predℤ (predℤ (succℤ (succℤ (succℤ (succℤ (pos 2 * x n))))))
  I = succℤ (succℤ (x n * pos 2))   ≡⟨ (ap (_+pos 2) (ℤ*-comm (x n) (pos 2))) ⟩
      pos 2 * x n + (pos 4 - pos 2) ≡⟨ ℤ+-assoc (pos 2 * x n) (pos 4) (- pos 2) ⁻¹ ⟩
      pos 2 * x n + pos 4 - pos 2 ∎
successive-level-bounds (x , b) n (succ k) with successive-level-bounds (x , b) n k
... | l₃ , l₄ with b (succℤ (n + pos k))
... | l₅ , l₆ = transport (_≤ x (succℤ (succℤ (n + pos k)))) I l₈
              , transport (x (succℤ (succℤ (n + pos k))) ≤_) II l₁₀
 where
  l₇ : pos (2^ (succ k)) * x n * pos 2 ≤ x (succℤ (n + pos k)) * pos 2
  l₇ = positive-multiplication-preserves-order' (pos (2^ (succ k)) * x n) (x (succℤ (n +pos k))) (pos 2) ⋆ l₃

  l₈ : pos (2^ (succ k)) * x n * pos 2 ≤ x (succℤ (succℤ (n + pos k)))
  l₈ = ℤ≤-trans (pos (2^ (succ k)) * x n * pos 2) (x (succℤ (n + pos k)) * pos 2) (x (succℤ (succℤ (n + pos k)))) l₇ l₅

  I : pos (2^ (succ k)) * x n * pos 2 ≡ pos (2^ (succ (succ k))) * x n
  I = pos (2^ (succ k)) * x n * pos 2   ≡⟨ ℤ*-comm (pos (2^ (succ k)) * x n) (pos 2) ⟩
      pos 2 * (pos (2^ (succ k)) * x n) ≡⟨ ℤ*-assoc (pos 2) (pos (2^ (succ k))) (x n) ⁻¹ ⟩
      pos 2 * pos (2^ (succ k)) * x n   ≡⟨ ap (_* x n) (pos-multiplication-equiv-to-ℕ 2 (2^ (succ k))) ⟩
      pos (2 *ℕ 2^ (succ k)) * x n      ≡⟨ refl ⟩
      pos (2^ (succ (succ k))) * x n ∎

  l₉ : x (succℤ (n + pos k)) * pos 2 ≤ (pos (2^ (succ k)) * x n + pos (2^ (succ (succ k))) - pos 2) * pos 2
  l₉ = positive-multiplication-preserves-order' (x (succℤ (n + pos k))) (pos (2^ (succ k)) * x n + pos (2^ (succ (succ k))) - pos 2) (pos 2) ⋆ l₄

  l₉' : x (succℤ (n + pos k)) * pos 2 + pos 2 ≤ (pos (2^ (succ k)) * x n + pos (2^ (succ (succ k))) - pos 2) * pos 2 + pos 2
  l₉' = ℤ≤-adding'
        (x (succℤ (n + pos k)) * pos 2)
         ((pos (2^ (succ k)) * x n + pos (2^ (succ (succ k))) - pos 2) * pos 2)
          (pos 2) l₉

  l₁₀ : x (succℤ (succℤ (n + pos k))) ≤ (pos (2^ (succ k)) * x n + pos (2^ (succ (succ k))) - pos 2) * pos 2 + pos 2
  l₁₀ = ℤ≤-trans (x (succℤ (succℤ (n + pos k)))) (x (succℤ (n + pos k)) * pos 2 + pos 2) ((pos (2^ (succ k)) * x n + pos (2^ (succ (succ k))) - pos 2) * pos 2 + pos 2) l₆ l₉'

  II : (pos (2^ (succ k)) * x n + pos (2^ (succ (succ k))) - pos 2) * pos 2 + pos 2 ≡ pos (2^ (succ (succ k))) * x n + pos (2^ (succ (succ (succ k)))) - pos 2
  II = (pos (2^ (succ k)) * x n + pos (2^ (succ (succ k))) - pos 2) * pos 2 + pos 2  ≡⟨ ap (_+ pos 2) (distributivity-mult-over-ℤ (pos (2^ (succ k)) * x n + pos (2^ (succ (succ k)))) (- pos 2) (pos 2)) ⟩
       (pos (2^ (succ k)) * x n + pos (2^ (succ (succ k)))) * pos 2 - pos 4 + pos 2  ≡⟨ ℤ+-assoc ((pos (2^ (succ k)) * x n + pos (2^ (succ (succ k)))) * pos 2) (- pos 4) (pos 2) ⟩
       (pos (2^ (succ k)) * x n + pos (2^ (succ (succ k)))) * pos 2 - pos 2          ≡⟨ ap (_- pos 2) (distributivity-mult-over-ℤ (pos (2^ (succ k)) * x n) (pos (2^ (succ (succ k)))) (pos 2)) ⟩
       pos (2^ (succ k)) * x n * pos 2 + pos (2^ (succ (succ k))) * pos 2 - pos 2    ≡⟨ ap₂ (λ a b → a + b - pos 2) (ℤ*-comm (pos (2^ (succ k)) * x n) (pos 2)) (ℤ*-comm (pos (2^ (succ (succ k)))) (pos 2)) ⟩
       pos 2 * (pos (2^ (succ k)) * x n) + pos 2 * pos (2^ (succ (succ k))) - pos 2  ≡⟨ ap₂ (λ a b → a + b - pos 2) (ℤ*-assoc (pos 2) (pos (2^ (succ k))) (x n) ⁻¹) (pos-multiplication-equiv-to-ℕ 2 (2^ (succ (succ k)))) ⟩
       pos 2 * pos (2^ (succ k)) * x n + pos (2^ (succ (succ (succ k)))) - pos 2     ≡⟨ ap (λ a → a * x n + pos (2^ (succ (succ (succ k)))) - pos 2) (pos-multiplication-equiv-to-ℕ 2 (2^ (succ k))) ⟩
       pos (2^ (succ (succ k))) * x n + pos (2^ (succ (succ (succ k)))) - pos 2      ∎

{-
difference : (f : ℤ[1/2] → ℤ[1/2] → ℤ[1/2])             -- Given a dyadic rational function
           → (((x , n) , p₁) ((y , n) , p₂) : ℤ[1/2])   -- and two bounds
           → ℕ                                          -- find the integer difference 
difference f lb rb = {!!}

operation-builder : (_⊕_ : ℤ[1/2] → ℤ[1/2] → ℤ[1/2])          -- Given a function on dyadic rationals
                  → preserves-bounds _⊕_                      -- where function applied at bounds give new bounds
                  → ((lb rb : ℤ[1/2]) → (Σ k ꞉ ℕ , {!!}))     -- 
                  → 𝕋 → 𝕋 → 𝕋 -- We get an operation on TBR
operation-builder _⊕_ ⊕-monotic k (f , b) (g , b') = {!!} , {!!}
-}



open import IntegersAbs
open import NaturalsOrder

power-of-two-grows : (n : ℕ) → 2^ n < 2^ (succ n)
power-of-two-grows 0 = ⋆
power-of-two-grows (succ n) = transport₂ _<_
                               (mult-commutativity (2^ n) 2)
                                (mult-commutativity (2^ (succ n)) 2)
                                 (multiplication-preserves-strict-order (2^ n) (2^ (succ n)) 1 (power-of-two-grows n))

find-next-2-exponent-ℕ : (n : ℕ) → Σ k ꞉ ℕ , n < 2^ k
find-next-2-exponent-ℕ 0 = 0 , ⋆
find-next-2-exponent-ℕ (succ n) with find-next-2-exponent-ℕ n
... | (k , l) with order-split (succ n) (2^ k)
... | inl l₂ = k , l₂
... | inr l₂ = (succ k) , transport (_< 2^ (succ k)) I (power-of-two-grows k) 
 where
  I : 2^ k ≡ succ n
  I = ≤-anti (2^ k) (succ n) l₂ l

find-next-2-exponent : (z : ℤ) → Σ k ꞉ ℕ , z < pos (2^ k)
find-next-2-exponent (negsucc x) = 0 , negative-less-than-positive x (2^ 0)
find-next-2-exponent (pos x)     = let (k , l) = find-next-2-exponent-ℕ x in k , ℕ-order-respects-ℤ-order x (2^ k) l 

operation-builder : (_⊕_ : ℤ → ℤ → ℤ)                                        -- Given a function on integers
                  → interval-monotonic _⊕_                                   -- where function applied at bounds give new bounds
                  → (∀ x y → (Σ k ꞉ ℕ , difference _⊕_ x y < pos (2^ k)))    -- if we can find a bound for each post-operation interval 
                  → 𝕋 → 𝕋 → 𝕋                                                 -- then we get an operation on TBR     
operation-builder _⊕_ ⊕-monotic width (f , b) (g , b') = h , h-gives-below
 where
  h : ℤ → ℤ
  h n with width (f n) (g n) 
  ... | k , l = (_/2' ^ (abs n)) ((upRight ^ (k +ℕ k)) (f (n + pos k) ⊕ g (n + pos k))) 

  h-gives-below : (δ : ℤ) → h (succℤ δ) below h δ
  h-gives-below δ with (width (f δ) (g δ) , width (f (succℤ δ)) (g (succℤ δ)))
  ... | ((k₁ , l₁) , k₂ , l₂) = {!!}

_below''_ : (a b : ℤ) → 𝓤₀ ̇
a below'' b = Σ n ꞉ ℕ , (pos (2^ (succ n)) * b) ≤ a ≤ pos (2^ (succ n)) * b + pos (succ n) * pos 2

--                        p   x   y   lb   rb  p' 
operation-builder' : (f : ℤ → ℤ → ℤ → (ℤ × ℤ × ℤ))
                   → (Σ m ꞉ (ℤ → ℤ) , {!!})
                   → 𝕋 → 𝕋 → 𝕋 
operation-builder' f m (x , b) (y , b') = h , h-is-below
 where
  h : ℤ → ℤ
  h p with f p (x p) (y p)
  ... | x⊕y , p' = {!!}

  h-is-below : {!!}
  h-is-below = {!!}

encode : ℤ[1/2] → ℤ × ℤ
encode ((p , k) , _) = p , pos k

connect : ((c₁ , _) : (ℤ × ℤ)) → ((c₂ , _) : (ℤ × ℤ)) → c₁ ≤ c₂ → ℤ × ℤ --  brick1    brick 2 (smallest brick which contains both) brick 2 always on right
connect (c₁ , p₁) (c₂ , p₂) l  = {!!}
 -- if p1 = p2 then call connect-on-same-level (c1 , c2 , p1)
 -- if p1 > p2 then call connect-on-same-level ((upRight ^ (p1 - p2)) c1  , c2  , p2)
 -- if p1 < p2 then call connect-on-same-leven (c1 , (upLeft ^ (p2 - p1)) , p1)

record Builder : 𝓤₁ ̇ where
 field
  D : ℤ[1/2] × ℤ[1/2] → ℤ[1/2]
  M : ℤ × ℤ → ℤ → ℕ  
  F : ℝ-d × ℝ-d → ℝ-d             -- real function
  ψ : (x y : ℤ[1/2]) → F (ι x , ι y) ≡ ι (D (x , y))
 ll lr rl rr : (ℤ × ℤ) × (ℤ × ℤ) → ℤ[1/2]
 ll ((c₁ , p₁) , (c₂ , p₂)) = D ((lb-of-brick c₁ on-level p₁) , (lb-of-brick c₂ on-level p₂))
 lr ((c₁ , p₁) , (c₂ , p₂)) = D ((lb-of-brick c₁ on-level p₁) , (rb-of-brick c₂ on-level p₂))
 rl ((c₁ , p₁) , (c₂ , p₂)) = D ((rb-of-brick c₁ on-level p₁) , (lb-of-brick c₂ on-level p₂))
 rr ((c₁ , p₁) , (c₂ , p₂)) = D ((rb-of-brick c₁ on-level p₁) , (rb-of-brick c₂ on-level p₂))
 L R : (ℤ × ℤ) × (ℤ × ℤ) → ℤ × ℤ --e.g for addition L ≡ x + y, R ≡ x + y + 2     L(          )R
 L ((c₁ , p₁) , (c₂ , p₂)) = {!!} -- encode (min {f , o , i , l})
 R ((c₁ , p₁) , (c₂ , p₂)) = {!!} -- encode (max {f , o , i , l}) - 2
 -- need proof that L ≤ R
 I : (ℤ × ℤ) × (ℤ × ℤ) → ℤ × ℤ   -- interval which connects L and R   I  (       L(          )R     )
 I ((c₁ , p₁) , (c₂ , p₂)) = connect (L ((c₁ , p₁) , (c₂ , p₂))) (R ((c₁ , p₁) , c₂ , p₂)) {!!} -- In general, need to check all extremes
 E : (ℤ × ℤ) → ℤ → ℤ × ℤ × ℕ     -- two codes, same precision level, returns left and right on same precision - endpoint realiser
 E (c₁ , c₂) p = l , r , {!!}   -- should be (q - p), which requires q ≥ p.  
  where
   lq₁ rq₂ : ℤ × ℤ
   lq₁ = L ((c₁ , p) , (c₂ , p))
   rq₂ = R ((c₁ , p) , (c₂ , p))
   l r q₁ q₂ : ℤ
   l = pr₁ lq₁
   r = pr₁ rq₂
   q₁ = pr₂ lq₁
   q₂ = pr₂ rq₂ -- Must prove that q₁ ≡ q₂ (for every specific function)
 F* : 𝕋 × 𝕋 → 𝕋                   -- from F
 F* ((x , b) , (y , b')) = z , b''
  where
   z : ℤ → ℤ
   z q = (upRight ^ (j +ℕ k)) l
    where
     k : ℕ
     k = M (x q , y q) q
     lrj : ℤ × ℤ × ℕ
     lrj = E (x (q + pos k) , y (q + pos k)) (q + pos k)

     l r : ℤ
     l = pr₁ lrj
     r = pr₁ (pr₂ lrj)
     j : ℕ
     j = pr₂ (pr₂ lrj)
 
   b'' : (δ : ℤ) → z (succℤ δ) below z δ
   b'' = {!!}
   -- If (given any a,b,q,a',b' : ℤ such that (a' below a) k and (b' below b)
   -- then ((upRight ^ (j + k)) l , q) : ℤ × ℤ covers (l , q + j) and (r , q + j)  (q + j ? q + j + k ?)
   -- where (l,r,j) ≔ E(a',b',q+k) and k ≔ M(a,b,q))
   -- and (given all our other conditions, e.g. ψ)
   -- then F (⟦ x ⟧ , ⟦ y ⟧) ≡ ⟦ F* x y  ⟧

   -- ⟦ x ⟧ (p < ⟦ x ⟧ → ∃ q ꞉ ℤ , p < lb x q
   

   -- for all q : ℤ , 
 
```

Proving that multiplication is monotonic on intervals is simple. The
monotonic direction depends on the sign of the argument, but in both
cases reduce to the proofs that order is preserves when multiplying
integers.

```agda

multiplication-interval-monotonic : interval-monotonic _*_
multiplication-interval-monotonic x y (pos 0) x<y = inl I
 where
  I : (k : ℤ) → x ≤ k ≤ y → (x * pos 0) ≤ k * pos 0 ≤ (y * pos 0)
  I k (l₁ , l₂) = ℤ≤-refl (pos 0) , ℤ≤-refl (pos 0)
multiplication-interval-monotonic x y (pos (succ z)) x<y = inl I 
 where
  I : (k : ℤ) → x ≤ k ≤ y → x * pos (succ z) ≤ k * pos (succ z) ≤ y * pos (succ z)
  I k (l₁ , l₂) = positive-multiplication-preserves-order' x k (pos (succ z)) ⋆ l₁
                , positive-multiplication-preserves-order' k y (pos (succ z)) ⋆ l₂
multiplication-interval-monotonic x y (negsucc z) x<y = inr I
 where
  I : (k : ℤ) → x ≤ k ≤ y → y * negsucc z ≤ k * negsucc z ≤ x * negsucc z
  I k (l₁ , l₂) = negative-multiplication-changes-order' k y (negsucc z) ⋆ l₂
                , negative-multiplication-changes-order' x k (negsucc z) ⋆ l₁

```
Proving that multiplication of an interval is bounded by
multiplication of the old bounds is more difficult. 
```agda

-- Σ k ꞉ ℕ , ((upRight ^ k) (difference _⊕_ (x (n + pos k)) (y (n + pos k))) ≤ pos 2)

interval-multiplication-preserves-bounds : ∀ x y → (Σ k ꞉ ℕ , difference _*_ x y < pos (2^ k))
interval-multiplication-preserves-bounds x y = find-next-2-exponent (difference _*_ x y)

addition-interval-monotonic : interval-monotonic _+_
addition-interval-monotonic x y z x<y = inl (λ k (l₁ , l₂) → (ℤ≤-adding' x k z l₁) , ℤ≤-adding' k y z l₂)

interval-addition-preserves-bounds : (x y : ℤ) → Σ k ꞉ ℕ , difference _+_ x y < pos (2^ k)
interval-addition-preserves-bounds x y = find-next-2-exponent (difference _+_ x y)

_𝕋+'_ : 𝕋 → 𝕋 → 𝕋
_𝕋+'_ = operation-builder _+_ addition-interval-monotonic interval-addition-preserves-bounds

0𝕋' : 𝕋
0𝕋' = map (((pos 0) , 0) , {!!})

1𝕋' : 𝕋
1𝕋' = map ((pos 1 , 0) , {!!})

2𝕋' : 𝕋
2𝕋' = map ((pos 2 , 0) , {!!})

3𝕋' : 𝕋
3𝕋' = map ((pos 3 , 0) , {!!})

0𝕋 : 𝕋
0𝕋 = x , {!!}
 where
  x : ℤ → ℤ
  x (pos 0) = pos 0
  x (pos (succ n)) = downLeft (x (pos 0))
  x (negsucc 0) = upRight (pos 0)
  x (negsucc (succ n)) = upRight (x (negsucc n))
  
1𝕋 : 𝕋
1𝕋 = x , {!!}
 where
  x : ℤ → ℤ
  x (pos 0) = pos 1
  x (pos (succ n)) = downLeft (x (pos n))
  x (negsucc 0) = upRight (pos 1)
  x (negsucc (succ n)) = upRight (x (negsucc n))

2𝕋 : 𝕋
2𝕋 = x , {!!}
 where
  x : ℤ → ℤ
  x (pos 0) = pos 2
  x (pos (succ n)) = downLeft (x (pos n))
  x (negsucc 0) = upRight (pos 2)
  x (negsucc (succ n)) = upRight (x (negsucc n))

3𝕋 : 𝕋
3𝕋 = x , {!!}
 where
  x : ℤ → ℤ
  x (pos 0) = pos 3
  x (pos (succ n)) = downLeft (x (pos n))
  x (negsucc 0) = upRight (pos 3)
  x (negsucc (succ n)) = upRight (x (negsucc n))

_𝕋*_ : 𝕋 → 𝕋 → 𝕋
_𝕋*_ = operation-builder _*_ multiplication-interval-monotonic interval-multiplication-preserves-bounds

8𝕋 : 𝕋
8𝕋 = x , {!!}
 where
  x : ℤ → ℤ
  x (pos 0) = pos 8
  x (pos (succ n)) = downLeft (x (pos n))
  x (negsucc 0) = upRight (pos 8)
  x (negsucc (succ n)) = upRight (x (negsucc n))

-2𝕋 : 𝕋
-2𝕋 = x , {!!}
 where
  x : ℤ → ℤ
  x (pos 0) = negsucc 1
  x (pos (succ n)) = downLeft (x (pos n))
  x (negsucc 0) = upRight (negsucc 1)
  x (negsucc (succ n)) = upRight (x (negsucc n))

-3𝕋 : 𝕋
-3𝕋 = x , {!!}
 where
  x : ℤ → ℤ
  x (pos 0) = negsucc 2
  x (pos (succ n)) = downLeft (x (pos n))
  x (negsucc 0) = upRight (negsucc 1)
  x (negsucc (succ n)) = upRight (x (negsucc n))

-5𝕋 : 𝕋
-5𝕋 = x , {!!}
 where
  x : ℤ → ℤ
  x (pos 0) = negsucc 4
  x (pos (succ n)) = downLeft (x (pos n))
  x (negsucc 0) = upRight (negsucc 4)
  x (negsucc (succ n)) = upRight (x (negsucc n))

```

We can define order of TBR's. We could define it similarly to order of
Dedekind reals, however for the sake of havingh accessible
computational content, we can use a modified order which is based on a
specific level of precision. 


```agda
open import IntegersOrder

--Confirm with Todd... This is sound but not complete
_<𝕋_on-level_ : 𝕋 → 𝕋 → ℤ → 𝓤₀ ̇
(x , _) <𝕋 (y , _) on-level n = (x n + pos 2) < y n

```



-- Is the idea that we have (f g : ℤ → ℤ → ℤ)

-- We want to have machinery to build operations defined on TBR's,
-- which agree with operations defined on reals.

{- 

prove-belowness : (f g : ℤ → ℤ)
                → (_⊕_ : ℤ → ℤ → ℤ)
                → Σ k ꞉ ℤ , {!!}
prove-belowness = {!!}

operation-builder : ((f , b) (g , b') : 𝕋)
                  → (_⊕_ : ℤ → ℤ → ℤ)
                  → ((n : ℤ) → (f (succℤ n) ⊕ g (succℤ n)) below (f n ⊕ g n))
                  → 𝕋 
operation-builder (f , b) (g , b') _⊕_ is-below = (λ δ → f δ ⊕ g δ) , is-below

conclusion : ((f , b) (g , b') : 𝕋)
           → (_⊕_ : ℤ → ℤ → ℤ)
           → (is-below : (((n : ℤ) → (f (succℤ n) ⊕ g (succℤ n)) below (f n ⊕ g n))))
           → (_⊕'_ : ℝ-d → ℝ-d → ℝ-d)
           → {!!}
           → ⟦ operation-builder (f , b) (g , b') _⊕_ is-below ⟧ ≡ ⟦ (f  , b) ⟧ ⊕' ⟦ (g , b') ⟧
conclusion = {!!}

-- Some condition (e.g monotonicity, or something else) which guarantees that we only need to consider the endpoints

think : (_⊙_ : ℤ → ℤ → ℤ)
      → Σ k ꞉ ℤ , upRight ^ {!!} ≡ {!!} 
think = {!!}

-}
-- _covers_ : ℤ[1/2] → ℤ[1/2] → 𝓤₀ ̇
-- (a , p) covers (b , q) = (lb (a , p) ≤ lb (b , q))
--                        × (rb (b , q) ≤ rb (a , p))

-- (p : ℕ) (x y : ℤ) → lb (x +ℤ y        , p) ≡ lb (x , p) +ℤ[1/2] lb (y , p)
-- (p : ℕ) (x y : ℤ) → rb (x +ℤ y +pos 2 , p) ≡ rb (x , p) +ℤ[1/2] rb (y , p)

--            (f : ℤ → ℤ → ℤ) (f' : ℤ[1/2] → ℤ[1/2] → ℤ[1/2])
--         → ((p : ℕ) → (a b : ℤ)           → lb (f a b        , p) ≡ f' (lb (a , p)) (lb (b , p)))
--         → ((p : ℕ) → (a b : ℤ) → Σ k ꞉ ℕ , rb (f a b +pos k , p) ≡ f' (rb (a , p)) (rb (b , p)))
--         → ((x y : 𝕋) → (p : ℤ) → (i : ℕ) → ((upRight ^ i) (f x(p) y(p)) covers (f x(p) y(p)        , p)
--                                          × ((upRight ^ i) (f x(p) y(p)) covers (f x(p) y(p) +pos k , p)))
--         → and if this ensures belowness property
--         → (x y : 𝕋) → ⟦ (λ n → (upRight ^ i) (f x(p) y(p))) ⟧ ≡ ι (f' ⟦ x ⟧ ⟦ y ⟧)

{-
addition-agrees : (x y : 𝕋) → ⟦ x 𝕋+ y ⟧ ≡ ⟦ x ⟧ ℝd+ ⟦ y ⟧
addition-agrees x y = ℝ-d-equality-from-left-cut left right
 where
  left : (p : ℤ[1/2])
       → ∃ k ꞉ ℤ , p < lb (x 𝕋+ y) k
       → ∃ (r , s) ꞉ ℤ[1/2] × ℤ[1/2] , (∃ k ꞉ ℤ , r < lb x k)
                                     × (∃ k' ꞉ ℤ , s < lb y k')
                                     × (p ≡ r ℤ[1/2]+ s)
  left p = ∥∥-functor I
   where
    I : Σ k ꞉ ℤ , p < lb (x 𝕋+ y) k
      → Σ (r , s) ꞉ ℤ[1/2] × ℤ[1/2] , r < ⟦ x ⟧ × s < ⟦ y ⟧ × (p ≡ (r ℤ[1/2]+ s))
    I (k , p<lb) = {!!}

  right : lower-cut-of (⟦ x ⟧ ℝd+ ⟦ y ⟧) ⊆ lower-cut-of ⟦ x 𝕋+ y ⟧
  right = {!!}

multiplication-commutes : (x y : 𝕋) → ⟦ x 𝕋* y ⟧ ≡ (⟦ x ⟧ ℝd* ⟦ y ⟧)
multiplication-commutes = {!!}

-}

```




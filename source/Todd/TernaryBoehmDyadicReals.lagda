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
open import NaturalsAddition renaming (_+_ to _+ℕ_)
open import NaturalsMultiplication renaming (_*_ to _*ℕ_)
open import IntegersNegation
open import UF-Base
open import UF-FunExt
open import UF-Powerset hiding (𝕋)
open import UF-PropTrunc
open import UF-Subsingletons

module Todd.TernaryBoehmDyadicReals
  (pt : propositional-truncations-exist)
  (fe : FunExt)
  (pe : PropExt)
 where

open import Todd.DyadicReals pt fe
open import Todd.RationalsDyadic fe
open import Todd.TernaryBoehmRealsPrelude fe
open import Todd.TernaryBoehmReals fe pe hiding (ι)

open PropositionalTruncation pt
module _
  (DyOrPr : OrderProperties)
 where
 
 open OrderProperties DyOrPr
 open DyadicProperties Dp

\end{code}

The following defines machinery to obtain the interval representations
of a ternary Boehm object at each layer n.

\begin{code}

 brick_on-level_ : ℤ → ℤ → ℤ[1/2] × ℤ[1/2]
 brick k on-level n = (normalise (k , n)) , (normalise (succℤ (succℤ k) , n))

 encoding_at-level_ : 𝕋 → ℤ → ℤ[1/2] × ℤ[1/2]
 encoding (x , _) at-level n = brick (x n) on-level n

 lb rb : 𝕋 → ℤ → ℤ[1/2]
 lb t n = pr₁ (encoding t at-level n)
 rb t n = pr₂ (encoding t at-level n)

 disjoint-lemma : (t : 𝕋) → (i j : ℤ) → lb t i < rb t j
 disjoint-lemma t i j = {!!}

 located-lemma₁ : (p q l r : ℤ[1/2]) → (r ℤ[1/2]- l) < (q ℤ[1/2]- p)
                → (p < l) ∔ (r < q)
 located-lemma₁ = {!!}

 located-lemma₂ : (t : 𝕋) → (p : ℤ[1/2]) → 0ℤ[1/2] < p
                → ∃ k ꞉ ℤ , (rb t k ℤ[1/2]- lb t k) < p
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
                        
\end{code}

want to prove that (x : ℤ[1/2]) → ⟦ map x ⟧ ≡ ι x

We now wish to introduce the map from encodings to TBR's : ℤ[1/2] → 𝕋.
The intuition behind the map is that ... 

\begin{code}

 layer : ℤ[1/2] → ℕ
 layer ((_ , n) , _) = n
 
 map : ℤ[1/2] → 𝕋
 map ((k , δ) , _) = build-via (k , pos δ)

 normalise-pos-lemma₁ : (k : ℤ) (δ : ℕ) (p : (δ ≡ 0) ∔ ((δ ≢ 0) × odd k))
              → normalise-pos ((k + k) /2') δ ≡ (k , δ) , p
 normalise-pos-lemma₁ k 0 (inl refl) = to-subtype-≡ (λ (z , n) → ℤ[1/2]-cond-is-prop z n) (to-×-≡ (div-by-two k) refl)
 normalise-pos-lemma₁ k 0 (inr (δnz , k-odd)) = 𝟘-elim (δnz refl)
 normalise-pos-lemma₁ k (succ δ) (inr p) with even-or-odd? ((k + k) /2')
 normalise-pos-lemma₁ k (succ δ) (inr (δnz , k-odd)) | inl k-even = 𝟘-elim (k-even (transport odd (div-by-two k ⁻¹) k-odd))
 ... | inr _ = to-subtype-≡ (λ (z , n) → ℤ[1/2]-cond-is-prop z n) (to-×-≡ (div-by-two k) refl)

 normalise-pos-lemma₂ : (k : ℤ) (δ : ℕ) → normalise-pos k δ ≡ normalise-pos (k + k) (succ δ)
 normalise-pos-lemma₂ k δ with even-or-odd? (k + k)
 ... | inl _ = ap (λ s → normalise-pos s δ) (div-by-two k ⁻¹)
 ... | inr o = 𝟘-elim (times-two-even' k o)
 
 normalise-lemma : (k : ℤ) (δ : ℕ) (n : ℕ) (p : (δ ≡ 0) ∔ ((δ ≢ 0) × odd k))
                 → normalise (rec k downLeft n + rec k downLeft n , (pos (succ δ) + pos n)) ≡ (k , δ) , p
 normalise-lemma k δ 0 p with even-or-odd? (k + k)
 ... | inl even = normalise-pos-lemma₁ k δ p
 ... | inr odd = 𝟘-elim (times-two-even' k odd)
 normalise-lemma k δ (succ n) p with even-or-odd? (k + k)
 ... | inl even = let y = rec k downLeft n 
                      z = (y + y) in 
                  normalise (z + z , (succℤ (pos (succ δ) + pos n))) ≡⟨ ap (λ - → normalise (z + z , succℤ -)) (pos-addition-equiv-to-ℕ (succ δ) n) ⟩
                  normalise (z + z , succℤ (pos (succ δ +ℕ n)))      ≡⟨ refl ⟩
                  normalise-pos (z + z) (succ (succ δ +ℕ n))         ≡⟨ normalise-pos-lemma₂ z (succ δ +ℕ n) ⁻¹ ⟩
                  normalise-pos z (succ δ +ℕ n)                      ≡⟨ refl ⟩
                  normalise (z , pos (succ δ +ℕ n))                  ≡⟨ ap (λ - → normalise (z , -)) (pos-addition-equiv-to-ℕ (succ δ) n ⁻¹) ⟩
                  normalise (z , pos (succ δ) + pos n)               ≡⟨ normalise-lemma k δ n p ⟩
                  (k , δ) , p ∎ 
 ... | inr odd = 𝟘-elim (times-two-even' k odd)
 
 lowest-terms-normalised : (((k , δ) , p) : ℤ[1/2]) → normalise-pos k δ ≡ ((k , δ) , p)
 lowest-terms-normalised ((k , .0) , inl refl) = refl
 lowest-terms-normalised ((k , zero) , inr (δnz , k-odd)) = 𝟘-elim (δnz refl)
 lowest-terms-normalised ((k , succ δ) , inr (δnz , k-odd)) with even-or-odd? k
 ... | inl k-even = 𝟘-elim (k-even k-odd)
 ... | inr k-odd = to-subtype-≡ (λ (z , n) → ℤ[1/2]-cond-is-prop z n) refl

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

 normalise-≤ : ((k , δ) : ℤ × ℕ) → ((m , ε) : ℤ × ℕ)
             → k * pos (2^ ε) ≤ m * pos (2^ δ)
             → normalise (k , pos δ) ≤ normalise (m , pos ε)
 normalise-≤ (k , δ) (m , ε) l with normalise-pos' k δ , normalise-pos' m ε
 ... | (n₁ , e₁) , (n₂ , e₂) = let (((k' , δ') , p) , ((m' , ε') , p')) = (normalise-pos k δ , normalise-pos m ε) in 
  ℤ≤-ordering-right-cancellable
   (k' * pos (2^ ε'))
    (m' * pos (2^ δ'))
     (pos (2^ (n₁ +ℕ n₂)))
      (power-of-pos-positive (n₁ +ℕ n₂))
       (transport₂ _≤_ (I k ε k' ε' n₁ n₂ (pr₁ (from-×-≡' e₁) ⁻¹) (pr₂ (from-×-≡' e₂) ⁻¹))
                       ((I m δ m' δ' n₂ n₁ (pr₁ (from-×-≡' e₂) ⁻¹) (pr₂ (from-×-≡' e₁) ⁻¹))
                        ∙ ap (λ z → m' * pos (2^ δ') * pos (2^ z)) (addition-commutativity n₂ n₁)) l)
   where
    k' = pr₁ (pr₁ (normalise-pos k δ))
    δ' = pr₂ (pr₁ (normalise-pos k δ))
    m' = pr₁ (pr₁ (normalise-pos m ε))
    ε' = pr₂ (pr₁ (normalise-pos m ε))
    I : (k : ℤ) (ε : ℕ) (k' : ℤ) (ε' : ℕ) (n₁ n₂ : ℕ) → k ≡ pos (2^ n₁) * k' → ε ≡ ε' +ℕ n₂ → k * pos (2^ ε) ≡ k' * pos (2^ ε') * pos (2^ (n₁ +ℕ n₂))
    I k ε k' ε' n₁ n₂ e₁ e₂ =
        k * pos (2^ ε)                            ≡⟨ ap (_* pos (2^ ε)) e₁ ⟩
        pos (2^ n₁) * k' * pos (2^ ε)             ≡⟨ ap (_* pos (2^ ε)) (ℤ*-comm (pos (2^ n₁)) k') ⟩
        k' * pos (2^ n₁) * pos (2^ ε)             ≡⟨ ap (λ z → k' * pos (2^ n₁) * pos (2^ z)) e₂ ⟩
        k' * pos (2^ n₁) * pos (2^ (ε' +ℕ n₂))    ≡⟨ ℤ*-assoc k' (pos (2^ n₁)) (pos (2^ (ε' +ℕ n₂))) ⟩
        k' * (pos (2^ n₁) * pos (2^ (ε' +ℕ n₂)))  ≡⟨ ap (k' *_) (pos-multiplication-equiv-to-ℕ (2^ n₁) (2^ (ε' +ℕ n₂))) ⟩
        k' * pos ((2^ n₁) *ℕ 2^ (ε' +ℕ n₂))       ≡⟨ ap (λ z →  k' * pos ((2^ n₁) *ℕ z)) (prod-of-powers 2 ε' n₂ ⁻¹) ⟩
        k' * pos (2^ n₁ *ℕ (2^ ε' *ℕ 2^ n₂))      ≡⟨ ap (λ z → k' * pos z) (mult-associativity (2^ n₁) (2^ ε') (2^ n₂) ⁻¹) ⟩
        k' * pos (2^ n₁ *ℕ 2^ ε' *ℕ 2^ n₂)        ≡⟨ ap (λ z → k' * pos (z *ℕ 2^ n₂)) (mult-commutativity (2^ n₁) (2^ ε')) ⟩
        k' * pos (2^ ε' *ℕ 2^ n₁ *ℕ 2^ n₂)        ≡⟨ ap (λ z → k' * pos z) (mult-associativity (2^ ε') (2^ n₁) (2^ n₂)) ⟩
        k' * pos (2^ ε' *ℕ (2^ n₁ *ℕ 2^ n₂))      ≡⟨ ap (λ z → k' * z) (pos-multiplication-equiv-to-ℕ (2^ ε') (2^ n₁ *ℕ 2^ n₂) ⁻¹) ⟩
        k' * (pos (2^ ε') * pos (2^ n₁ *ℕ 2^ n₂)) ≡⟨ ap (λ z → k' * (pos (2^ ε') * pos z)) (prod-of-powers 2 n₁ n₂) ⟩
        k' * (pos (2^ ε') * pos (2^ (n₁ +ℕ n₂)))  ≡⟨ ℤ*-assoc k' (pos (2^ ε')) (pos (2^ (n₁ +ℕ n₂))) ⁻¹ ⟩
        k' * pos (2^ ε') * pos (2^ (n₁ +ℕ n₂))    ∎

 left-interval-monotonic' : (t : 𝕋) → (n : ℤ) → lb t n ≤ lb t (succℤ n)
 left-interval-monotonic' (x , b) (pos n) = normalise-≤ ((x (pos n)) , n) (x (pos (succ n)) , succ n) {!!}
 left-interval-monotonic' (x , b) (negsucc n) = {!!}
 -- goal : normalise ((x n) , n) ≤ normalise (x (succℤ n) , succℤ n)
 
 left-interval-monotonic : (x : ℤ[1/2]) → (n : ℤ) → lb (map x) n ≤ lb (map x) (succℤ n)
 left-interval-monotonic x n = let (f , b) = map x
                               in left-interval-monotonic' (map x) n

 left-interval-is-minimum : (x : ℤ[1/2]) → (n : ℤ) → lb (map x) n ≤ x
 left-interval-is-minimum ((x , δ) , p) n with ℤ-trichotomous (pos δ) n
 ... | inl δ<n = transport (_≤ ((x , δ) , p)) (map-lemma ((x , δ) , p) n δ<n ⁻¹) (≤-refl ((x , δ) , p))
 ... | inr (inl refl) = transport (_≤ ((x , δ) , p)) (map-lemma-≤ (((x , δ) , p)) n (ℤ≤-refl (pos δ)) ⁻¹) (≤-refl ((x , δ) , p))
 ... | inr (inr n<δ) = {!!}

 encodings-agree-with-reals : (x : ℤ[1/2]) → ⟦ map x ⟧ ≡ ι x
 encodings-agree-with-reals x = ℝ-d-equality-from-left-cut left right
  where
   left : (y : ℤ[1/2]) → (∃ n ꞉ ℤ , y < lb (map x) n) → y < x
   left y = ∥∥-rec (<ℤ[1/2]-is-prop y x) λ (n , y<l) → trans<≤ y (lb (map x) n) x y<l (left-interval-is-minimum x n) 
   right : (y : ℤ[1/2]) → y < x → ∃ n ꞉ ℤ , y < lb (map x) n
   right y y<x = ∣ (pos (layer x) , (transport (y <_) (map-lemma-≤ x (pos (layer x) ) (ℤ≤-refl (pos (layer x))) ⁻¹) y<x)) ∣

\end{code}

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

\begin{code}

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
          
 {-
 _𝕋+_ : 𝕋 → 𝕋 → 𝕋
 (x , b) 𝕋+ (y , b') = (λ n → upRight (upRight ((x (n +pos 2)) + (y (n +pos 2))))) , {!!}
 -}
 {-
 _𝕋*_ : 𝕋 → 𝕋 → 𝕋
 (x , b) 𝕋* (y , b') = {!!}
 -}
\end{code}

We also require the same operations for Dyadic Reals.

\begin{code}
 {-
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
 -}
\end{code}

The result we are now interested in is proving that these operations
on TBR and Dedekind reals correlate.

\begin{code}
 {-
 ℤ[1/2]<-swap : (x y : ℤ[1/2]) → (x < y) ⇔ (ℤ[1/2]- y) < (ℤ[1/2]- x)
 ℤ[1/2]<-swap = {!!}
 -}


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




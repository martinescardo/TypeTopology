This file defines dyadic rationals, denoted ℤ[1/2], and postulates a
number of operations, relations and properties of the
postulates. These are well known, commonly accepted results, but the
aim is to provide specific implementations of these postulates.

```agda

{-# OPTIONS --without-K --exact-split --allow-unsolved-metas #-}

open import SpartanMLTT renaming (_+_ to _∔_) -- TypeTopology

open import IntegersB
open import IntegersAbs
open import IntegersAddition renaming (_+_ to _+ℤ_)
open import IntegersMultiplication 
open import IntegersNegation
open import IntegersOrder
open import NaturalsAddition
open import NaturalsMultiplication renaming (_*_ to _ℕ*_)
open import NaturalNumbers
open import NaturalNumbers-Properties
open import OrderNotation
open import UF-Base
open import UF-FunExt
open import UF-Miscelanea
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

module Todd.RationalsDyadic
  (fe : FunExt)
 where
 
open import Todd.TernaryBoehmRealsPrelude fe

```

Rational dyadics clearly rely on powers of two, so it is useful to
introduce power notation.  Some simple properties of powers are also
proved.

```agda

_ℕ^_ : ℕ → ℕ → ℕ
a ℕ^ b = ((a ℕ*_) ^ b) 1

infixl 33 _ℕ^_ 

_/2' : ℤ → ℤ
pos x     /2' = pos (x /2)
negsucc x /2' = - (pos (succ x /2))

2^ : ℕ → ℕ
2^ = 2 ℕ^_

zero-base : (a : ℕ) → a ℕ^ 0 ≡ 1
zero-base a = refl

prod-of-powers : (n a b : ℕ) → n ℕ^ a ℕ* n ℕ^ b ≡ n ℕ^ (a + b)
prod-of-powers n a zero     = refl
prod-of-powers n a (succ b) = I
 where
  I : n ℕ^ a ℕ* n ℕ^ succ b ≡ n ℕ^ (a + succ b)
  I = n ℕ^ a ℕ* n ℕ^ succ b   ≡⟨ refl ⟩
      n ℕ^ a ℕ* (n ℕ* n ℕ^ b) ≡⟨ mult-associativity (n ℕ^ a) n (n ℕ^ b) ⁻¹ ⟩
      n ℕ^ a ℕ* n ℕ* n ℕ^ b   ≡⟨ ap (_ℕ* n ℕ^ b) (mult-commutativity (n ℕ^ a) n) ⟩
      n ℕ* n ℕ^ a ℕ* n ℕ^ b   ≡⟨ mult-associativity n (n ℕ^ a) (n ℕ^ b) ⟩
      n ℕ* (n ℕ^ a ℕ* n ℕ^ b) ≡⟨ ap (n ℕ*_) (prod-of-powers n a b) ⟩
      n ℕ* n ℕ^ (a + b)       ≡⟨ refl ⟩
      n ℕ^ succ (a + b)       ≡⟨ refl ⟩
      n ℕ^ (a + succ b)       ∎

raise-again : (n a b : ℕ) → (n ℕ^ a) ℕ^ b ≡ n ℕ^ (a ℕ* b)
raise-again n a zero     = refl
raise-again n a (succ b) = I
 where
  IH : n ℕ^ a ℕ^ b ≡ n ℕ^ (a ℕ* b)
  IH = raise-again n a b
  
  I : n ℕ^ a ℕ^ succ b ≡ n ℕ^ (a ℕ* succ b)
  I = n ℕ^ a ℕ^ succ b        ≡⟨ refl ⟩
      n ℕ^ a ℕ* (n ℕ^ a) ℕ^ b ≡⟨ ap (n ℕ^ a ℕ*_) IH ⟩
      n ℕ^ a ℕ* n ℕ^ (a ℕ* b) ≡⟨ prod-of-powers n a (a ℕ* b) ⟩
      n ℕ^ (a + a ℕ* b)       ≡⟨ refl ⟩
      n ℕ^ (a ℕ* succ b)      ∎

power-of-pos-positive : ∀ n → greater-than-zero (pos (2^ n))
power-of-pos-positive 0 = ⋆
power-of-pos-positive (succ n) = transport greater-than-zero (pos-multiplication-equiv-to-ℕ 2 (2^ n)) I
 where
  I : greater-than-zero (pos 2 * pos (2^ n))
  I = greater-than-zero-mult-trans (pos 2) (pos (2^ n)) ⋆ (power-of-pos-positive n) 

-- TODO : Move following proofs into relevant files/places.

negsucc-lemma : (x : ℕ) → negsucc x +ℤ negsucc x ≡ negsucc (x + succ x)
negsucc-lemma x = negsucc x +ℤ negsucc x           ≡⟨ refl ⟩
                  (- pos (succ x)) - pos (succ x)  ≡⟨ negation-dist (pos (succ x)) (pos (succ x)) ⟩
                  - (pos (succ x) +ℤ pos (succ x)) ≡⟨ refl ⟩
                  - succℤ (pos (succ x) +ℤ pos x)  ≡⟨ ap (λ z → - succℤ z) (pos-addition-equiv-to-ℕ (succ x) x) ⟩
                  - succℤ (pos (succ x + x))       ≡⟨ refl ⟩
                  negsucc (succ x + x)             ≡⟨ ap negsucc (addition-commutativity (succ x) x) ⟩
                  negsucc (x + succ x)             ∎

div-by-two' : (k : ℕ) → k + k /2 ≡ k
div-by-two' 0 = refl
div-by-two' (succ k) = (succ k + succ k) /2     ≡⟨ ap _/2 (succ-left k (succ k)) ⟩
                       succ (succ (k + k)) /2  ≡⟨ refl ⟩
                       succ ((k + k) /2)        ≡⟨ ap succ (div-by-two' k) ⟩
                       succ k                    ∎

div-by-two : (k : ℤ) → (k +ℤ k) /2' ≡ k
div-by-two (pos k) = (pos k +ℤ pos k) /2' ≡⟨ ap _/2' (pos-addition-equiv-to-ℕ k k) ⟩     
                     pos (k + k) /2'      ≡⟨ ap pos (div-by-two' k) ⟩
                     pos k ∎
div-by-two (negsucc x) = (negsucc x +ℤ negsucc x) /2'   ≡⟨ ap _/2' (negsucc-lemma x) ⟩
                         negsucc (x + succ x) /2'     ≡⟨ refl ⟩
                         - pos (succ (x + succ x) /2) ≡⟨ ap (λ z → - pos (z /2)) (succ-left x (succ x) ⁻¹) ⟩
                         - pos ((succ x + succ x) /2) ≡⟨ ap (λ z → - pos z) (div-by-two' (succ x)) ⟩
                         negsucc x ∎

odd-succ-succ' : (k : ℤ) → odd (succℤ (succℤ k)) → odd k
odd-succ-succ' (pos x) = id
odd-succ-succ' (negsucc zero) = id
odd-succ-succ' (negsucc (succ (succ x))) = id

even-succ-succ' : (k : ℤ) → even (succℤ (succℤ k)) → even k
even-succ-succ' (pos 0) e = id
even-succ-succ' (pos (succ 0)) e = 𝟘-elim (e ⋆)
even-succ-succ' (pos (succ (succ x))) e = e
even-succ-succ' (negsucc 0) e = 𝟘-elim (e ⋆)
even-succ-succ' (negsucc (succ 0)) e = id
even-succ-succ' (negsucc (succ (succ x))) e = e

times-two-even' : (k : ℤ) → even (k +ℤ k)
times-two-even' (pos (succ k)) odd2k = times-two-even' (pos k) (odd-succ-succ' (pos k +ℤ pos k) (transport odd I odd2k))
 where
  I : pos (succ k) +ℤ pos (succ k) ≡ pos k +ℤ pos (succ (succ k))
  I = ℤ-left-succ (pos k) (pos (succ k))
times-two-even' (negsucc (succ k)) odd2k = times-two-even' (negsucc k) (transport odd I (odd-succ-succ (negsucc (succ k) +ℤ negsucc (succ k)) odd2k))
 where
  I : succℤ (succℤ (negsucc (succ k) +ℤ negsucc (succ k))) ≡ negsucc k +ℤ negsucc k
  I = succℤ (succℤ (negsucc (succ k) +ℤ negsucc (succ k)))   ≡⟨ refl ⟩
      succℤ (succℤ (predℤ (negsucc k) +ℤ predℤ (negsucc k))) ≡⟨ refl ⟩
      succℤ (succℤ (predℤ (predℤ (negsucc k) +ℤ negsucc k))) ≡⟨ ap (λ a → succℤ a) (succpredℤ (predℤ (negsucc k) +ℤ negsucc k)) ⟩
      succℤ (predℤ (negsucc k) +ℤ negsucc k)                 ≡⟨ ap succℤ (ℤ-left-pred (negsucc k) (negsucc k)) ⟩
      succℤ (predℤ (negsucc k +ℤ negsucc k))                 ≡⟨ succpredℤ (negsucc k +ℤ negsucc k) ⟩
      negsucc k +ℤ negsucc k ∎

negation-preserves-parity : (x : ℤ) → even x → even (- x)
negation-preserves-parity (pos 0) = id
negation-preserves-parity (pos (succ 0)) e = 𝟘-elim (e ⋆)
negation-preserves-parity (pos (succ (succ 0))) e = id
negation-preserves-parity (pos (succ (succ (succ x)))) e = negation-preserves-parity (pos (succ x)) e
negation-preserves-parity (negsucc 0) e = 𝟘-elim (e ⋆)
negation-preserves-parity (negsucc (succ 0)) e = id
negation-preserves-parity (negsucc (succ (succ x))) e = negation-preserves-parity (negsucc x) (even-succ-succ (negsucc (succ (succ x))) e)

even-lemma-pos : (x : ℕ) → even (pos x) → (pos x /2') * pos 2 ≡ pos x
even-lemma-pos 0 even-x = refl
even-lemma-pos (succ 0) even-x = 𝟘-elim (even-x ⋆)
even-lemma-pos (succ (succ x)) even-x = succℤ (pos x /2') +ℤ succℤ (pos x /2')    ≡⟨ ℤ-left-succ (pos x /2') (succℤ (pos x /2')) ⟩
                                          succℤ (succℤ ((pos x /2') * pos 2))       ≡⟨ ap (λ z → succℤ (succℤ z)) (even-lemma-pos x even-x) ⟩
                                          pos (succ (succ x)) ∎

even-lemma-neg : (x : ℕ) → even (negsucc x) → (negsucc x /2') * pos 2 ≡ negsucc x
even-lemma-neg x even-x = (- pos (succ x /2)) - pos (succ x /2)  ≡⟨ negation-dist (pos (succ x /2)) (pos (succ x /2)) ⟩
                          - (pos (succ x /2) +ℤ pos (succ x /2)) ≡⟨ ap -_ (even-lemma-pos (succ x) (negation-preserves-parity (negsucc x) even-x)) ⟩
                          negsucc x ∎

even-lemma : (x : ℤ) → even x → (x /2') * pos 2 ≡ x
even-lemma (pos x) = even-lemma-pos x
even-lemma (negsucc x) = even-lemma-neg x

```

The definition of dyadic rationals follow.  The dyadic rational ((k ,
δ) , p), to illustrate, refers to the dyadic rational (k / 2ᵟ).  We
could use integers values for δ, but negative values of δ are simply
integer valued dyadic rationals.  For example, (3 / 2⁻⁶) = 192 = (192
/ 2⁰).

```agda

ℤ[1/2] : 𝓤₀ ̇
ℤ[1/2] = Σ (z , n) ꞉ ℤ × ℕ , (n ≡ 0) ∔ ((n ≢ 0) × odd z)

ℤ[1/2]-cond-is-prop : (z : ℤ) (n : ℕ) → is-prop ((n ≡ 0) ∔ ((n ≢ 0) × odd z))
ℤ[1/2]-cond-is-prop z n =
 +-is-prop ℕ-is-set (×-is-prop (Π-is-prop (fe 𝓤₀ 𝓤₀) (λ _ → 𝟘-is-prop)) (odd-is-prop z)) λ e (ne , _) → ne e

0ℤ[1/2] : ℤ[1/2]
0ℤ[1/2] = (pos 0 , 0) , inl refl

1ℤ[1/2] : ℤ[1/2]
1ℤ[1/2] = (pos 1 , 0) , inl refl

```

We must now introduce a function to reduce an arbitrary dyadic
rational into it's canonical form (i.e with a positive power
denominator, which is either coprime to an odd denominator or is (2⁰ ≡
1).

As is usual with integers, we split into positive and negative
cases. In the negative case, simply recursively multiply by two to
obtain an integer. In the positive case, we must check if the top is
even or odd, and then recursively divide by two as necessary.

```agda

normalise-pos normalise-neg : ℤ → ℕ → ℤ[1/2]
normalise-pos z 0        = (z , 0) , inl refl
normalise-pos z (succ n) with even-or-odd? z
... | inl e = normalise-pos (z /2') n
... | inr o = (z , succ n) , inr (positive-not-zero n , o)
normalise-neg z 0        = (z +ℤ z , 0) , inl refl
normalise-neg z (succ n) = normalise-neg (z +ℤ z) n

normalise-pos' : (x : ℤ) → (a : ℕ) → let ((k , δ) , p) = normalise-pos x a
                                     in Σ m ꞉ ℕ , ((pos (2^ m) * k , δ + m) ≡ x , a)
normalise-pos' x 0 = 0 , to-×-≡ (ℤ-mult-left-id x) refl
normalise-pos' x (succ a) with even-or-odd? x
... | inr odd-k = 0 , (to-×-≡ (ℤ-mult-left-id x) refl)
... | inl even-k with normalise-pos' (x /2') a
... | (m , e) with from-×-≡' e
... | (e₁ , e₂) = let (k , δ) , p = normalise-pos (x /2') a in
                  succ m ,
                  to-×-≡' (
                  (pos (2^ (succ m)) * k   ≡⟨ refl ⟩
                  pos (2 ℕ* 2^ m) * k      ≡⟨ ap (_* k) (pos-multiplication-equiv-to-ℕ 2 (2^ m) ⁻¹) ⟩
                  pos 2 * pos (2^ m) * k   ≡⟨ ℤ*-assoc (pos 2) (pos (2^ m)) k ⟩
                  pos 2 * (pos (2^ m) * k) ≡⟨ ap (pos 2 *_) e₁ ⟩
                  pos 2 * (x /2')          ≡⟨ ℤ*-comm (pos 2) (x /2') ⟩
                  (x /2') * pos 2          ≡⟨ even-lemma x even-k ⟩ 
                  x ∎)
                  , ap succ e₂)

normalise : ℤ × ℤ → ℤ[1/2]
normalise (k , pos     n) = normalise-pos k n
normalise (k , negsucc n) = normalise-neg k n

```

Order is easily defined. There are many ways one could define order,
but this definition aligns with the standard definition of order of
rationals.

```agda

_<ℤ[1/2]_ _≤ℤ[1/2]_ : ℤ[1/2] → ℤ[1/2] → 𝓤₀ ̇
((x , n) , _) <ℤ[1/2] ((y , m) , _) = x * pos (2^ m) < y * pos (2^ n)
((x , n) , _) ≤ℤ[1/2] ((y , m) , _) = x * pos (2^ m) ≤ y * pos (2^ n)

<ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x <ℤ[1/2] y)
<ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _) = ℤ<-is-prop (x * pos (2^ b)) (y * pos (2^ a)) 

≤ℤ[1/2]-is-prop : (x y : ℤ[1/2]) → is-prop (x ≤ℤ[1/2] y)
≤ℤ[1/2]-is-prop ((x , a) , _) ((y , b) , _) = ℤ≤-is-prop (x * pos (2^ b)) (y * pos (2^ a))

instance
 Order-ℤ[1/2]-ℤ[1/2] : Order ℤ[1/2] ℤ[1/2]
 _≤_ {{Order-ℤ[1/2]-ℤ[1/2]}} = _≤ℤ[1/2]_

 Strict-Order-ℤ[1/2]-ℤ[1/2] : Strict-Order ℤ[1/2] ℤ[1/2]
 _<_ {{Strict-Order-ℤ[1/2]-ℤ[1/2]}} = _<ℤ[1/2]_

```
The following records define all the properties of dyadic rationals we
need in this development.

```agda

record DyadicProperties : 𝓤₁ ̇ where
 field
  _ℤ[1/2]+_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]+-comm  : commutative _ℤ[1/2]+_
  ℤ[1/2]+-assoc : associative _ℤ[1/2]+_
  ℤ[1/2]-_      : ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]+-inv   : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x ℤ[1/2]+ y) ≡ 0ℤ[1/2]
  _ℤ[1/2]*_     : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
  ℤ[1/2]*-comm   : commutative _ℤ[1/2]*_
  ℤ[1/2]*-assoc  : associative _ℤ[1/2]*_
  ℤ[1/2]-negation-involutive : (x : ℤ[1/2]) → x ≡ ℤ[1/2]- (ℤ[1/2]- x)
  
 infix 20  ℤ[1/2]-_
 infixl 19 _ℤ[1/2]-_

 _ℤ[1/2]-_ : (p q : ℤ[1/2]) → ℤ[1/2]
 p ℤ[1/2]- q = p ℤ[1/2]+ (ℤ[1/2]- q)

record OrderProperties : 𝓤₁ ̇ where
 field
  Dp : DyadicProperties
 open DyadicProperties Dp
 field
  trans  : (x y z : ℤ[1/2]) → x < y → y < z → x < z
  trans' : (x y z : ℤ[1/2]) → x ≤ y → y ≤ z → x ≤ z
  no-min : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (y < x)
  no-max : (x : ℤ[1/2]) → Σ y ꞉ ℤ[1/2] , (x < y)
  dense  : (x y : ℤ[1/2]) → Σ k ꞉ ℤ[1/2] , x < k × (k < y)
  trans<≤ : (x y z : ℤ[1/2]) → x < y → y ≤ z → x < z
  ≤-refl : (x : ℤ[1/2]) → x ≤ x
  <-is-≤ℤ[1/2] : (x y : ℤ[1/2]) → x < y → x ≤ y
  diff-positive : (x y : ℤ[1/2]) → x < y → 0ℤ[1/2] < (y ℤ[1/2]- x)
  <-swap : (x y : ℤ[1/2]) → x < y → (ℤ[1/2]- y) < (ℤ[1/2]- x)

 trans₂ : (w x y z : ℤ[1/2]) → w < x → x < y → y < z → w < z
 trans₂ w x y z w<x x<y y<z = trans w x z w<x (trans x y z x<y y<z)

```

The following code begins the process of directly implementing the
above postulates. They are all commonly accepted results, but time
consuming to prove and so are deferred to a later time.

```agda

_𝔻+_ : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
((k , n) , e) 𝔻+ ((h , m) , e') = normalise ((k * pos m +ℤ h * pos n) , (pos n * pos m))

𝔻+-comm : commutative _𝔻+_
𝔻+-comm ((k , n) , e) ((h , m) , e') = ap normalise (to-×-≡' (I , II)) 
 where
  I : k * pos m +ℤ h * pos n ≡ h * pos n +ℤ k * pos m
  I = ℤ+-comm (k * pos m) (h * pos n)

  II : pos n * pos m ≡ pos m * pos n
  II = ℤ*-comm (pos n) (pos m)

normalise-𝔻+ : ∀ x y → normalise x 𝔻+ normalise y ≡ normalise {!!}
normalise-𝔻+ = {!!}

D+-assoc : associative _𝔻+_
D+-assoc x y z = {!!}

```

The following code may be necessary at some point. Unfortunately,
there was an error in assuming that even and odd numbers are coprime,
so thought is required as to how to define the embedding of dyadic
rationals into rationals.

```agda

open import CanonicalMapNotation
open import NaturalsDivision
open import ncRationals
open import Rationals
open import RationalsMultiplication renaming (_*_ to _ℚ*_)

```
Proof that any integer is in lowest terms. 
```agda
zero-denom-lt : (x : ℤ) → is-in-lowest-terms (x , 0)
zero-denom-lt x = (1-divides-all (abs x) , (1 , refl)) , (λ f (k , e) → e)

```
Now we have the inclusion of the dyadic rationals into the rationals,
and the usual canonical map notational.
```agda


--Not ideal, should probably use previously considered method
ℤ[1/2]-to-ℚ' : (a : ℤ) (n : ℕ) → (p : (n ≡ 0) ∔ ¬ (n ≡ 0) × odd a) → ℚ
ℤ[1/2]-to-ℚ' a 0 p        = (a , 0) , (zero-denom-lt a)
ℤ[1/2]-to-ℚ' a (succ n) (inr (nz , a-odd))
 = ℤ[1/2]-to-ℚ' a n (Cases (ℕ-is-discrete n 0) (λ e → inl e) (λ nz → inr (nz , a-odd))) ℚ* 1/2

ℤ[1/2]-to-ℚ : ℤ[1/2] → ℚ
ℤ[1/2]-to-ℚ ((a , n) , p) = ℤ[1/2]-to-ℚ' a n p

instance
 canonical-map-ℤ[1/2]-to-ℚ : Canonical-Map ℤ[1/2] ℚ
 ι {{canonical-map-ℤ[1/2]-to-ℚ}} = ℤ[1/2]-to-ℚ

```

ℕ-even ℕ-odd : ℕ → 𝓤₀ ̇
ℕ-odd 0 = 𝟘
ℕ-odd 1 = 𝟙
ℕ-odd (succ (succ n)) = ℕ-odd n
ℕ-even n = ¬ ℕ-odd n

odd→ℕ-odd : (z : ℤ) → odd z → ℕ-odd (abs z)
odd→ℕ-odd (pos (succ 0))            o = ⋆
odd→ℕ-odd (pos (succ (succ x)))     o = odd→ℕ-odd (pos x) o
odd→ℕ-odd (negsucc 0)               o = ⋆
odd→ℕ-odd (negsucc (succ (succ x))) o = odd→ℕ-odd (negsucc x) o

odd-even-gives-hcf-1 : (a b : ℕ) → ℕ-odd a → ℕ-even b → coprime a b
odd-even-gives-hcf-1 (succ a) b odd-a even-b = ((1-divides-all (succ a)) , 1-divides-all b) , I
 where
  I : (f : ℕ) → is-common-divisor f (succ a) b → f ∣ 1
  I 0 ((k , e) , _) = 𝟘-elim (zero-not-positive a (zero-left-is-zero k ⁻¹ ∙ e))
  I 1 icd = 1-divides-all 1
  I (succ (succ f)) ((k , α) , l , β) = {!!}

positive-powers-of-two-not-zero : (n : ℕ) → ¬ (2^ (succ n) ≡ 0)
positive-powers-of-two-not-zero (succ n) e = positive-powers-of-two-not-zero n (mult-left-cancellable (2^ (succ n)) 0 1 e)

succ-succ-even : (n : ℕ) → ℕ-even n → ℕ-even (2 + n)
succ-succ-even zero even-n ()
succ-succ-even (succ zero) even-n = λ _ → even-n ⋆
succ-succ-even (succ (succ n)) even-n = succ-succ-even n even-n

times-two-even : (n : ℕ) → ℕ-even (2 * n)
times-two-even 0 ()
times-two-even (succ n) = succ-succ-even (2 * n) (times-two-even n)

-- incorrect, odd-even-gives-hcf-1 not true




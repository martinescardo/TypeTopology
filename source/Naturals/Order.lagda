Martin Escardo, started 5th May 2018

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Naturals.Order where

open import MLTT.Spartan hiding (_^_)

open import Naturals.Addition renaming (_+_ to _+'_)
open import Naturals.AbsoluteDifference
open import Naturals.Properties
open import Notation.Order
open import Ordinals.Notions
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Subsingletons

_≤ℕ_ : ℕ → ℕ → 𝓤₀ ̇
0    ≤ℕ n        = 𝟙
succ m ≤ℕ 0      = 𝟘
succ m ≤ℕ succ n = m ≤ℕ n

instance
 Order-ℕ-ℕ : Order ℕ ℕ
 _≤_ {{Order-ℕ-ℕ}} = _≤ℕ_

≤-is-prop-valued : (m n : ℕ) → is-prop (m ≤ n)
≤-is-prop-valued 0        n        = 𝟙-is-prop
≤-is-prop-valued (succ m) 0        = 𝟘-is-prop
≤-is-prop-valued (succ m) (succ n) = ≤-is-prop-valued m n

right-addition-is-embedding : (m n : ℕ) → is-prop (Σ k ꞉ ℕ , k +' m ＝ n)
right-addition-is-embedding 0        n        (n , refl) (n , refl) = refl
right-addition-is-embedding (succ m) 0        (k , p)    (k' , p')  =
  𝟘-elim (positive-not-zero (k +' m) p)
right-addition-is-embedding (succ m) (succ n) (k , p)    (k' , p') =
 to-Σ-＝ (ap pr₁ IH , ℕ-is-set _ _)
 where
  IH : k , succ-lc p ＝ k' , succ-lc p'
  IH = right-addition-is-embedding m n (k , succ-lc p) (k' , succ-lc p')

zero-least : (n : ℕ) → 0 ≤ n
zero-least n = ⋆

zero-least' : (n : ℕ) → ¬ (succ n ≤ 0)
zero-least' n l = l

zero-least'' : (n : ℕ) → n ≤ 0 → n ＝ 0
zero-least'' 0 l = refl

succ-monotone : (m n : ℕ) → m ≤ n → succ m ≤ succ n
succ-monotone m n l = l

succ-order-injective : (m n : ℕ) → succ m ≤ succ n → m ≤ n
succ-order-injective m n l = l

≤-induction : (P : (m n : ℕ) (l : m ≤ n) → 𝓤 ̇ )
            → ((n : ℕ) → P 0 n (zero-least n))
            → ((m n : ℕ) (l : m ≤ n)
                    → P m n l
                    → P (succ m) (succ n) (succ-monotone m n l))
            → (m n : ℕ) (l : m ≤ n) → P m n l
≤-induction P b f 0    n ⋆            = b n
≤-induction P b f (succ m) 0    l     = 𝟘-elim l
≤-induction P b f (succ m) (succ n) l = f m n l (≤-induction P b f m n l)

succ≤＝ : (m n : ℕ) → (succ m ≤ succ n) ＝ (m ≤ n)
succ≤＝ m n = refl

≤-refl : (n : ℕ) → n ≤ n
≤-refl 0        = ⋆
≤-refl (succ n) = ≤-refl n

≤-trans : (l m n : ℕ) → l ≤ m → m ≤ n → l ≤ n
≤-trans 0    m n p q = ⋆
≤-trans (succ l) 0    n p q = 𝟘-elim p
≤-trans (succ l) (succ m) 0    p q = 𝟘-elim q
≤-trans (succ l) (succ m) (succ n) p q = ≤-trans l m n p q

≤-anti : (m n : ℕ) → m ≤ n → n ≤ m → m ＝ n
≤-anti 0    0    p q = refl
≤-anti 0    (succ n) p q = 𝟘-elim q
≤-anti (succ m) 0    p q = 𝟘-elim p
≤-anti (succ m) (succ n) p q = ap succ (≤-anti m n p q)

≤-succ : (n : ℕ) → n ≤ succ n
≤-succ 0        = ⋆
≤-succ (succ n) = ≤-succ n

unique-least : (n : ℕ) → n ≤ 0 → n ＝ 0
unique-least 0    l = refl
unique-least (succ n) l = 𝟘-elim l

≤-split : (m n : ℕ) → m ≤ succ n → (m ≤ n) + (m ＝ succ n)
≤-split 0    n l = inl l
≤-split (succ m) 0    l = inr (ap succ (unique-least m l))
≤-split (succ m) (succ n) l = cases inl (inr ∘ (ap succ)) (≤-split m n l)

≤-join : (m n : ℕ) → (m ≤ n) + (m ＝ succ n) → m ≤ succ n
≤-join m n (inl l) = ≤-trans m n (succ n) l (≤-succ n)
≤-join .(succ n) n (inr refl) = ≤-refl n

≤-down : (m n : ℕ) → m ≤ succ n → (m ≠ succ n) → (m ≤ n)
≤-down m n l u = cases id (λ p → 𝟘-elim (u p)) (≤-split m n l)

≤-+ : (m n : ℕ) → (m ≤ m +' n)
≤-+ m 0        = ≤-refl m
≤-+ m (succ n) = ≤-join m (m +' n) (inl IH)
 where
  IH : m ≤ m +' n
  IH = ≤-+ m n

≤-+' : (m n : ℕ) → (n ≤ m +' n)
≤-+' m n = transport (λ k → n ≤ k) γ (≤-+ n m)
 where
  γ : n +' m ＝ m +' n
  γ = addition-commutativity n m

_<ℕ_ : ℕ → ℕ → 𝓤₀ ̇
m <ℕ n = succ m ≤ℕ n

instance
 Strict-Order-ℕ-ℕ : Strict-Order ℕ ℕ
 _<_ {{Strict-Order-ℕ-ℕ}} = _<ℕ_

<-succ : (n : ℕ) → n < succ n
<-succ = ≤-refl

not-less-than-itself : (n : ℕ) → ¬ (n < n)
not-less-than-itself 0    l = l
not-less-than-itself (succ n) l = not-less-than-itself n l

not-less-bigger-or-equal : (m n : ℕ) → ¬ (n < m) → n ≥ m
not-less-bigger-or-equal 0        n        = λ _ → zero-least n
not-less-bigger-or-equal (succ m) 0        = ¬¬-intro (zero-least m)
not-less-bigger-or-equal (succ m) (succ n) = not-less-bigger-or-equal m n

bigger-or-equal-not-less : (m n : ℕ) → n ≥ m → ¬ (n < m)
bigger-or-equal-not-less m n l u = not-less-than-itself n γ
 where
  γ : succ n ≤ n
  γ = ≤-trans (succ n) m n u l

less-not-bigger-or-equal : (m n : ℕ) → m < n → ¬ (n ≤ m)
less-not-bigger-or-equal m n l u = bigger-or-equal-not-less n m u l

bounded-∀-next : (A : ℕ → 𝓤 ̇ ) (k : ℕ)
               → A k
               → ((n : ℕ) → n < k → A n)
               → (n : ℕ) → n < succ k → A n
bounded-∀-next A k a φ n l = cases f g s
 where
  s : (n < k) + (succ n ＝ succ k)
  s = ≤-split (succ n) k l
  f : n < k → A n
  f = φ n
  g : succ n ＝ succ k → A n
  g p = transport⁻¹ A (succ-lc p) a

\end{code}

Added 20th June 2018:

\begin{code}

<-is-prop-valued : (m n : ℕ) → is-prop (m < n)
<-is-prop-valued m n = ≤-is-prop-valued (succ m) n

<-coarser-than-≤ : (m n : ℕ) → m < n → m ≤ n
<-coarser-than-≤ m n = ≤-trans m (succ m) n (≤-succ m)

<-trans : (l m n : ℕ) → l < m → m < n → l < n
<-trans l m n u v = ≤-trans (succ l) m n u (<-coarser-than-≤ m n v)

<-split : (m n : ℕ) → m < succ n → (m < n) + (m ＝ n)
<-split m 0        l = inr (unique-least m l)
<-split m (succ n) l = ≤-split m n l

regress : (P : ℕ → 𝓤 ̇ )
        → ((n : ℕ) → P (succ n) → P n)
        → (n m : ℕ) → m ≤ n → P n → P m
regress P ρ 0    m l p = transport⁻¹ P (unique-least m l) p
regress P ρ (succ n) m l p = cases (λ (l' : m ≤ n) → IH m l' (ρ n p))
                                   (λ (r : m ＝ succ n) → transport⁻¹ P r p)
                                   (≤-split m n l)
 where
  IH : (m : ℕ) → m ≤ n → P n → P m
  IH = regress P ρ n

<-is-well-founded : (m : ℕ) → is-accessible _<_ m
<-is-well-founded 0        = acc (λ y l → unique-from-𝟘 l)
<-is-well-founded (succ m) = acc (τ (<-is-well-founded m))
 where
  τ : is-accessible _<_ m → (n : ℕ) → n < succ m → is-accessible _<_ n
  τ a n u = cases (λ (v : n < m) → prev _<_ a n v)
                  (λ (p : n ＝ m) → transport⁻¹ (is-accessible _<_) p a)
                  (<-split n m u)

course-of-values-induction : (P : ℕ → 𝓤 ̇ )
                           → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
                           → (n : ℕ) → P n
course-of-values-induction = transfinite-induction _<_ <-is-well-founded

course-of-values-induction-on-value-of-function
 : {X : 𝓤 ̇ }
   (f : X → ℕ)
   (P : X → 𝓥 ̇ )
 → ((x : X) → ((y : X) → f y < f x → P y) → P x)
 → (x : X) → P x
course-of-values-induction-on-value-of-function
 {𝓤} {𝓥} {X} f P h x = II (f x) x refl
 where
  A : ℕ → 𝓤 ⊔ 𝓥 ̇
  A n = (x : X) → f x ＝ n → P x

  I : (n : ℕ) → ((m : ℕ) → m < n → A m) → A n
  I .(f x) g x refl = h x (λ y l → g (f y) l y refl)

  II : (n : ℕ) → A n
  II = course-of-values-induction A I

\end{code}

TODO. Also add plain induction on the values of a function.

TODO. Notice that this proof of course-of-values induction uses the
accessibility predicate. From a foundational point of view, this is a
too powerful tool - an indexed W-type. In fact, this is not
needed. The course-of-values-induction theorem can be proved in MLTT
with only natural numbers and without universes, identity types, of W
types (indexed or not) other than the natural numbers.

\begin{code}

<-is-extensional : is-extensional _<_
<-is-extensional 0        0        f g = refl
<-is-extensional 0        (succ n) f g = unique-from-𝟘 (g 0    (zero-least n))
<-is-extensional (succ m) (0   )   f g = unique-from-𝟘 (f 0    (zero-least m))
<-is-extensional (succ m) (succ n) f g = ap succ (≤-anti m n γ₁ γ₂)
 where
  γ₁ : m ≤ n
  γ₁ = f m (≤-refl m)

  γ₂ : n ≤ m
  γ₂ = g n (≤-refl n)

ℕ-ordinal : is-well-order _<_
ℕ-ordinal = <-is-prop-valued , <-is-well-founded , <-is-extensional , <-trans

\end{code}

Induction on z, then x, then y:

\begin{code}

ℕ-cotransitive : cotransitive _<_
ℕ-cotransitive 0        y        0        l = inr l
ℕ-cotransitive (succ x) y        0        l = inr (≤-trans 1 (succ(succ x)) y ⋆ l)
ℕ-cotransitive 0        (succ y) (succ z) l = inl (zero-least y)
ℕ-cotransitive (succ x) (succ y) (succ z) l = γ IH
 where
  IH : (x < z) + (z < y)
  IH = ℕ-cotransitive x y z l
  γ : (x < z) + (z < y) → (succ x < succ z) + (succ z < succ y)
  γ (inl l) = inl (succ-monotone (succ x) z l)
  γ (inr r) = inr (succ-monotone (succ z) y r)

\end{code}

Added December 2019.

\begin{code}

open import NotionsOfDecidability.Complemented

≤-decidable : (m n : ℕ ) → is-decidable (m ≤ n)
≤-decidable 0        n        = inl (zero-least n)
≤-decidable (succ m) 0        = inr (zero-least' m)
≤-decidable (succ m) (succ n) = ≤-decidable m n

<-decidable : (m n : ℕ ) → is-decidable (m < n)
<-decidable m n = ≤-decidable (succ m) n

\end{code}

Bounded minimization (added 14th December 2019):

\begin{code}

βμ : (A : ℕ → 𝓤 ̇ )
  → is-complemented A
  → (k : ℕ)
  → (Σ m ꞉ ℕ , (m < k) × A m × ((n : ℕ) → A n → m ≤ n))
  + ((n : ℕ) → A n → n ≥ k)

βμ A δ 0 = inr (λ n a → zero-least n)
βμ A δ (succ k) = γ
 where
  conclusion = (Σ m ꞉ ℕ , (m < succ k) × A m × ((n : ℕ) → A n → m ≤ n))
             + ((n : ℕ) → A n → n ≥ succ k)

  f : (Σ m ꞉ ℕ , (m < k) × A m × ((n : ℕ) → A n → m ≤ n)) → conclusion
  f (m , l , a , φ) = inl (m , <-trans m k (succ k) l (<-succ k) , a , φ)
  g : ((n : ℕ) → A n → k ≤ n) → conclusion
  g φ = cases g₀ g₁ (δ k)
   where
    g₀ : A k → conclusion
    g₀ a = inl (k , ≤-refl k , a , φ)
    g₁ : ¬ A k → conclusion
    g₁ u = inr ψ
     where
      ψ : (n : ℕ) → A n → succ k ≤ n
      ψ 0 a = 𝟘-elim (v a)
       where
        p : k ＝ 0
        p = zero-least'' k (φ 0 a)
        v : ¬ A 0
        v = transport (λ - → ¬ A -) p u
      ψ (succ n) a = III
       where
        I : k ≤ succ n
        I = φ (succ n) a
        II : k ≠ succ n
        II p = transport (λ - → ¬ A -) p u a
        III : k ≤ n
        III = ≤-down k n I II

  γ : conclusion
  γ = cases f g (βμ A δ k)

\end{code}

Given k : ℕ with A k, find the least m : ℕ with A m, by reduction to
bounded minimization:

\begin{code}

Σμ : (ℕ → 𝓤 ̇ ) → 𝓤 ̇
Σμ A = Σ m ꞉ ℕ , A m × ((n : ℕ) → A n → m ≤ n)

least-from-given : (A : ℕ → 𝓤 ̇ ) → is-complemented A → Σ A → Σμ A
least-from-given A δ (k , a) = γ
 where
  f : (Σ m ꞉ ℕ , (m < k) × A m × ((n : ℕ) → A n → m ≤ n)) → Σμ A
  f (m , l , a' , φ) = m , a' , φ
  g : ((n : ℕ) → A n → k ≤ n) → Σμ A
  g φ = k , a , φ
  γ : Σμ A
  γ = cases f g (βμ A δ k)

\end{code}

20th November 2020.

\begin{code}

max : ℕ → ℕ → ℕ
max 0        n        = n
max (succ m) 0        = succ m
max (succ m) (succ n) = succ (max m n)

max-idemp : (x : ℕ) → max x x ＝ x
max-idemp 0        = refl
max-idemp (succ x) = ap succ (max-idemp x)

max-comm : (m n : ℕ) → max m n ＝ max n m
max-comm 0        0        = refl
max-comm 0        (succ n) = refl
max-comm (succ m) 0        = refl
max-comm (succ m) (succ n) = ap succ (max-comm m n)

max-assoc : (x y z : ℕ) → max (max x y) z ＝ max x (max y z)
max-assoc 0        y        z        = refl
max-assoc (succ x) 0        z        = refl
max-assoc (succ x) (succ y) 0        = refl
max-assoc (succ x) (succ y) (succ z) = ap succ (max-assoc x y z)

max-ord→ : (x y : ℕ) → x ≤ y → max x y ＝ y
max-ord→ 0        y        le = refl
max-ord→ (succ x) 0        le = 𝟘-elim le
max-ord→ (succ x) (succ y) le = ap succ (max-ord→ x y le)

max-ord← : (x y : ℕ) → max x y ＝ y → x ≤ y
max-ord← 0        y        p = ⋆
max-ord← (succ x) 0        p = 𝟘-elim (positive-not-zero x p)
max-ord← (succ x) (succ y) p = max-ord← x y (succ-lc p)

max-≤-upper-bound : (m n : ℕ) → m ≤ max m n
max-≤-upper-bound 0        n        = ⋆
max-≤-upper-bound (succ m) 0        = ≤-refl m
max-≤-upper-bound (succ m) (succ n) = max-≤-upper-bound m n

max-≤-upper-bound' : (m n : ℕ) → m ≤ max n m
max-≤-upper-bound' 0    n = ⋆
max-≤-upper-bound' (succ m) 0    = ≤-refl m
max-≤-upper-bound' (succ m) (succ n) = max-≤-upper-bound' m n

minus : (m n : ℕ) → n ≤ m → ℕ
minus 0        n        le = 0
minus (succ m) 0        ⋆  = succ m
minus (succ m) (succ n) le = minus m n le

open import Naturals.Addition renaming (_+_ to _∔_)

minus-property : (m n : ℕ) (le : n ≤ m) → minus m n le ∔ n ＝ m
minus-property 0        0        ⋆  = refl
minus-property (succ m) 0        ⋆  = refl
minus-property (succ m) (succ n) le = ap succ (minus-property m n le)

max-minus-property : (m n : ℕ)
                   → minus (max m n) m (max-≤-upper-bound m n) ∔ m ＝ max m n
max-minus-property m n = minus-property (max m n) m (max-≤-upper-bound m n)

\end{code}

Tom de Jong, 5 November 2021.

\begin{code}

<-trichotomous : (n m : ℕ) → (n < m) + (n ＝ m) + (m < n)
<-trichotomous 0        0        = inr (inl refl)
<-trichotomous 0        (succ m) = inl ⋆
<-trichotomous (succ n) 0        = inr (inr ⋆)
<-trichotomous (succ n) (succ m) = γ IH
 where
  γ : (n < m) + (n ＝ m) + (m < n)
    → (succ n < succ m) + (succ n ＝ succ m) + (succ m < succ n)
  γ (inl k)       = inl k
  γ (inr (inl e)) = inr (inl (ap succ e))
  γ (inr (inr l)) = inr (inr l)

  IH : (n < m) + (n ＝ m) + (m < n)
  IH = <-trichotomous n m

\end{code}

Added 12/05/2020 by Andrew Sneap.
Following are proofs of common properties of strict and non-strict order of
Natural Numbers.

\begin{code}

≤-trans₂ : (x y u v : ℕ) → x ≤ y → y ≤ u → u ≤ v → x ≤ v
≤-trans₂ x y u v l₁ l₂ = ≤-trans x u v I
 where
  I : x ≤ u
  I = ≤-trans x y u l₁ l₂

<-trans₂ : (x y u v : ℕ) → x < y → y < u → u < v → x < v
<-trans₂ x y u v l₁ l₂ = <-trans x u v I
 where
  I : x < u
  I = <-trans x y u l₁ l₂

≤-<-trans : (x y z : ℕ) → x ≤ y → y < z → x < z
≤-<-trans x y z l₁ l₂ = ≤-trans (succ x) (succ y) z l₁ l₂

<-≤-trans : (x y z : ℕ) → x < y → y ≤ z → x < z
<-≤-trans x y z l₁ l₂ = ≤-trans (succ x) y z l₁ l₂

≤-n-monotone-right : (x y z : ℕ) → x ≤ y → (x +' z) ≤ (y +' z)
≤-n-monotone-right x y 0        l = l
≤-n-monotone-right x y (succ n) l = ≤-n-monotone-right x y n l

≤-n-monotone-left : (x y z : ℕ) → x ≤ y → (z +' x) ≤ (z +' y)
≤-n-monotone-left x y z l = transport₂ _≤_ γ₁ γ₂ γ₃
  where
   γ₁ : x ∔ z ＝ z ∔ x
   γ₁ = addition-commutativity x z

   γ₂ : y ∔ z ＝ z ∔ y
   γ₂ = addition-commutativity y z

   γ₃ : x ∔ z ≤ y ∔ z
   γ₃ = ≤-n-monotone-right x y z l

≤-adding : (x y u v : ℕ) → x ≤ y → u ≤ v → (x +' u) ≤ (y +' v)
≤-adding x y u v l₁ l₂ = ≤-trans (x +' u) (y +' u) (y +' v) γ₁ γ₂
 where
  γ₁ : x ∔ u ≤ y ∔ u
  γ₁ = ≤-n-monotone-right x y u l₁

  γ₂ : y ∔ u ≤ y ∔ v
  γ₂ = ≤-n-monotone-left u v y l₂

<-succ-monotone : (x y : ℕ) → x < y → succ x < succ y
<-succ-monotone x y = id

<-n-monotone-right : (x y z : ℕ) → x < y → (x +' z) < (y +' z)
<-n-monotone-right x y  0       l = l
<-n-monotone-right x y (succ z) l = <-n-monotone-right x y z l

<-n-monotone-left : (x y z : ℕ) → x < y → (z +' x) < (z +' y)
<-n-monotone-left x y z l = transport₂ _<_ γ₁ γ₂ γ₃
 where
  γ₁ : x ∔ z ＝ z ∔ x
  γ₁ = addition-commutativity x z

  γ₂ : y ∔ z ＝ z ∔ y
  γ₂ = addition-commutativity y z

  γ₃ : x ∔ z < y ∔ z
  γ₃ = <-n-monotone-right x y z l

<-adding : (x y u v : ℕ) → x < y → u < v → (x +' u) < (y +' v)
<-adding x y u v l₁ l₂ = <-trans (x +' u) (y +' u) (y +' v) γ₁ γ₂
 where
  γ₁ : x ∔ u < y ∔ u
  γ₁ = <-n-monotone-right x y u l₁

  γ₂ : y ∔ u < y ∔ v
  γ₂ = <-n-monotone-left u v y l₂

<-+ : (x y z : ℕ) → x < y → x < y +' z
<-+ x y z l₁ = ≤-trans (succ x) y (y +' z) l₁ l₂
 where
  l₂ : y ≤ y +' z
  l₂ = ≤-+ y z

equal-gives-less-than-or-equal : (x y : ℕ) → x ＝ y → x ≤ y
equal-gives-less-than-or-equal x y p = transport (_≤ y) (p ⁻¹) (≤-refl y)

less-than-not-equal : (x y : ℕ) → x < y → ¬ (x ＝ y)
less-than-not-equal x y r p = less-not-bigger-or-equal x y r γ
 where
  γ : y ≤ x
  γ = equal-gives-less-than-or-equal y x (p ⁻¹)

less-than-one-is-0 : (x : ℕ) → x < 1 → x ＝ 0
less-than-one-is-0 0        l = refl
less-than-one-is-0 (succ x) l = 𝟘-elim l

not-less-or-equal-is-bigger : (x y : ℕ) → ¬ (x ≤ y) → y < x
not-less-or-equal-is-bigger 0        y        l = l (zero-least y)
not-less-or-equal-is-bigger (succ x) 0        l = zero-least x
not-less-or-equal-is-bigger (succ x) (succ y) l
 = not-less-or-equal-is-bigger x y l

≤-dichotomous : (x y : ℕ) → (x ≤ y) + (y ≤ x)
≤-dichotomous 0        y        = inl ⋆
≤-dichotomous (succ x) 0        = inr ⋆
≤-dichotomous (succ x) (succ y) = ≤-dichotomous x y

≥-dichotomy : (x y : ℕ) → (x ≥ y) + (x ≤ y)
≥-dichotomy 0        y        = inr (zero-least y)
≥-dichotomy (succ x) 0        = inl (zero-least (succ x))
≥-dichotomy (succ x) (succ y) = ≥-dichotomy x y

order-split : (x y : ℕ) → (x < y) + (x ≥ y)
order-split 0        0        = inr (zero-least 0)
order-split 0        (succ y) = inl (zero-least (succ y))
order-split (succ x) 0        = inr (zero-least (succ x))
order-split (succ x) (succ y) = order-split x y

least-element-unique : {A : ℕ → 𝓤 ̇ }
                     → (σ : is-complemented A)
                     → ((α , αₚ) : Σ k ꞉ ℕ , A k × ((z : ℕ) → A z → k ≤ z))
                     → ((β , βₚ) : Σ n ꞉ ℕ , A n × ((z : ℕ) → A z → n ≤ z))
                     → α ＝ β

least-element-unique σ (α , α₀ , α₁) (β , β₀ , β₁) = ≤-anti α β I II
 where
  I : α ≤ β
  I = α₁ β β₀

  II : β ≤ α
  II = β₁ α α₀

least-element-unique' : {A : ℕ → 𝓤 ̇ }
                      → (σ : is-complemented A)
                      → (x y : ℕ)
                      → (δ : Σ A)
                      → x ＝ pr₁ (least-from-given A σ δ)
                      → y ＝ pr₁ (least-from-given A σ δ)
                      → x ＝ y

least-element-unique' σ x y δ e₁ e₂ = e₁ ∙ e₂ ⁻¹

\end{code}

The following section provides an algorithm for bounded maximisation
of decidable propositions on Natural numbers, similar to the algorithm
for bounded-minimisation above.

We want to prove the following:

Given a complemented predicate A on naturals numbers and strict upper bound k,
either there exists a maximal element m such that m < k , A m holds and
(∀ n , A n → n ≤ m), or our predicate only holds for n ≥ k.

Proof:
 We proceed by induction on the upper bound. Given an upper bound of 0, we
 are done, because there are no natural numbers less than 0.

 Now we consider the induction hypothesis that our statement is true for an upper
 bound k. We consider each case.

 Case 1: We have some maximal element m such that A m holds, with m < k.
 Since A is decidable, we find that either A k holds, or it doesn't. If it holds,
 then have a new maximal element A k, with k < k + 1.

 Case 2: The predicate does not hold for any m < k. Again, we inspect A k. If it
 holds, then we have found a maximal (and the only) element m < k + 1. Otherwise,
 the statement does not hold for any n is our range.

Also given are the types of maximal element m : ℕ such that A m holds, given an
upper bound k

\begin{code}

maximal-element : (A : ℕ → 𝓤 ̇ ) → (k : ℕ) → 𝓤 ̇
maximal-element A k
 = Σ m ꞉ ℕ , (m < k × A m × ((n : ℕ) → n < k → A n → n ≤ m))

maximal-element' : (A : ℕ → 𝓤 ̇ ) → (k : ℕ) → 𝓤 ̇
maximal-element' A k
 = Σ m ꞉ ℕ , (m ≤ k × A m × ((n : ℕ) → n ≤ k → A n → n ≤ m))

no-maximal-element : (A : ℕ → 𝓤 ̇ ) → (k : ℕ) → 𝓤 ̇
no-maximal-element A k = (n : ℕ) → A n → n ≥ k

no-maximal-element' : (A : ℕ → 𝓤 ̇ ) → (k : ℕ) → 𝓤 ̇
no-maximal-element' A k = (n : ℕ) → A n → k < n

bounded-maximisation : (A : ℕ → 𝓤 ̇ )
                     → is-complemented A
                     → (k : ℕ)
                     → maximal-element A k + no-maximal-element A k
bounded-maximisation A δ 0        = inr (λ n _ → zero-least n)
bounded-maximisation A δ (succ k) = γ (δ k) (bounded-maximisation A δ k)
 where
  γ : A k + ¬ A k
   → maximal-element A k + no-maximal-element A k
   → maximal-element A (succ k) + no-maximal-element A (succ k)

  -- Case 1
  γ (inl Ak)  (inl (m , l , Am , ψ)) = inl (k , <-succ k , Ak , ψ')
   where
   ψ' : (n : ℕ) → n < succ k → A n → n ≤ k
   ψ' n l' An = l'
  γ (inr ¬Ak) (inl (m , l , Am , ψ)) = inl (m , l' , Am , ψ')
   where
    l' : m < succ k
    l' = <-trans m k (succ k) l (<-succ k)
    ψ' : (n : ℕ) → n < succ k → A n → n < succ m
    ψ' n l' An = ρ (<-split n k l')
     where
      ρ : (n < k) + (n ＝ k) → n < succ m
      ρ (inl l'') = ψ n l'' An
      ρ (inr e)   = 𝟘-elim (¬Ak (transport A e An))

  -- Case 2
  γ (inl Ak)  (inr ω)  = inl (k , <-succ k , Ak , ψ)
   where
    ψ : (n : ℕ) → n < succ k → A n → n ≤ k
    ψ n l An = l
  γ (inr ¬Ak) (inr ψ) = inr ψ'
   where
    ψ' : (n : ℕ) → A n → n ≥ succ k
    ψ' n An = ρ (<-split k n (ψ n An))
     where
      ρ : (k < n) + (k ＝ n) → n ≥ succ k
      ρ (inl l') = l'
      ρ (inr e)  = 𝟘-elim (¬Ak (transport A (e ⁻¹) An))

\end{code}

We can use the above result to prove the same statement for inclusive order.

\begin{code}

bounded-maximisation' : (A : ℕ → 𝓤 ̇ )
                      → is-complemented A
                      → (k : ℕ)
                      → maximal-element' A k + no-maximal-element' A k
bounded-maximisation' A δ k = bounded-maximisation A δ (succ k)

no-maximal-lemma : (A : ℕ → 𝓤 ̇ )
                 → (k : ℕ)
                 → no-maximal-element A k
                 → ¬ maximal-element A k
no-maximal-lemma A k ω (m , l , Am , ψ) = not-less-than-itself k β
 where
  α : k ≤ m
  α = ω m Am

  β : k < k
  β = ≤-<-trans k m k α l

\end{code}

With above machinery in mind, we can now produce maximal elements of
propositions of Natural Numbers, given some initial Natural Number for
which the property holds. Of course, we must provide an upper bound.

\begin{code}

maximal-from-given : (A : ℕ → 𝓤 ̇ )
                   → (b : ℕ)
                   → is-complemented A
                   → Σ k ꞉ ℕ , A k × k < b
                   → maximal-element A b
maximal-from-given A b δ (k , Ak , l) = Cases (bounded-maximisation A δ b) γ₁ γ₂
 where
  γ₁ : maximal-element A b → maximal-element A b
  γ₁ = id

  γ₂ : no-maximal-element A b → maximal-element A b
  γ₂ ω = 𝟘-elim (not-less-than-itself b β)
   where
    α : b ≤ k
    α = ω k Ak

    β : b < b
    β = ≤-<-trans b k b α l

maximal-from-given' : (A : ℕ → 𝓤 ̇ )
                    → (b : ℕ)
                    → is-complemented A
                    → Σ k ꞉ ℕ , A k × k ≤ b
                    → maximal-element' A b
maximal-from-given' A b = maximal-from-given A (succ b)

\end{code}

Multiplication preserves non-strict order, and this is proved by induction.

In the base case, it is required to prove that 0 ≤ 0 which is true by
definition.  In the inductive case, we need to prove that
m * succ k ≤ n * succ k, or by definitional equality m + m * k ≤ n + n * k.

By the inductive hypothesis, m * k ≤ n * k, and we have that m ≤ n, so we
can use the result which says we can combine two order relations into one.

\begin{code}

open import Naturals.Multiplication

multiplication-preserves-order : (m n k : ℕ) → m ≤ n → m * k ≤ n * k
multiplication-preserves-order m n 0        l = zero-least 0
multiplication-preserves-order m n (succ k) l = γ
 where
  IH : m * k ≤ n * k
  IH = multiplication-preserves-order m n k l

  γ : m * (succ k) ≤ n * (succ k)
  γ = ≤-adding m n (m * k) (n * k) l IH

\end{code}

For strict order, order is only preserved when multiplying by a value
greater than 0.  Again by induction, the base case is trivial since we
are multiplying by 1.  The inductive case is similar to the above
proof.

\begin{code}

multiplication-preserves-strict-order : (m n k : ℕ)
                                      → m < n
                                      → m * succ k < n * succ k
multiplication-preserves-strict-order m n 0        l = l
multiplication-preserves-strict-order m n (succ k) l = γ
 where
  IH : m * succ k < n * succ k
  IH = multiplication-preserves-strict-order m n k l

  γ : m * succ (succ k) < n * succ (succ k)
  γ = <-adding m n (m * succ k) (n * succ k) l IH

\end{code}

A variation added by Fredrik Nordvall Forsberg on 11 October 2025.

\begin{code}

multiplication-preserves-strict-order' : (m n k : ℕ)
                                       → m < n
                                       → 0 < k
                                       → m * k < n * k
multiplication-preserves-strict-order' m n (succ k) l p =
 multiplication-preserves-strict-order m n k l

\end{code}

If x * (y + 1) ≤ z, then x ≤ z. This is a useful property to have, and
proof follows from x ≤ x * y + 1 and transitivity of order.

A similar proof for strict order is sometimes useful.

\begin{code}

product-order-cancellable : (x y z : ℕ) → x * (succ y) ≤ z → x ≤ z
product-order-cancellable x 0        z   = id
product-order-cancellable x (succ y) z l = γ
 where
  I : x ≤ x ∔ x * succ y
  I = ≤-+ x (x * succ y)

  γ : x ≤ z
  γ = ≤-trans x (x * succ (succ y)) z I l

less-than-pos-mult : (x y z : ℕ) → x < y → x < y * succ z
less-than-pos-mult x y z l = <-+ x y (y * z) l

\end{code}

Lane Biocini, 07 September 2023

Here we define some order lemmas for the Absolute Difference operation
and then prove the analog of the triangle inequality for the Natural
Numbers under it.

Slight refactoring on 12 October 2023

\begin{code}

≤-diff : (x y : ℕ) → ∣ x - y ∣ ≤ x +' y
≤-diff x        0        = ≤-refl x
≤-diff 0        (succ y) = ≤-+' 0    y
≤-diff (succ x) (succ y) = γ
 where
  Γ : (x +' y) ≤ (succ x +' y)
  Γ = ≤-trans (x +' y) (succ (x +' y)) (succ x +' y)
       (≤-succ (x +' y))
       (equal-gives-less-than-or-equal (succ (x +' y)) (succ x +' y)
         (succ-left x y ⁻¹))

  γ : ∣ x - y ∣ ≤ succ (succ x +' y)
  γ = ≤-trans₂ ∣ x - y ∣ (x +' y) (succ x +' y) (succ (succ x +' y))
       (≤-diff x y) Γ (≤-succ (succ x +' y))

≤-diff-minus : (x y : ℕ) → x ≤ y +' ∣ y - x ∣
≤-diff-minus 0    y = ⋆
≤-diff-minus (succ x) 0    = ≤-+' 0    x
≤-diff-minus (succ x) (succ y) = γ
 where
  Γ : x ≤ (y +' ∣ y - x ∣)
  Γ = ≤-diff-minus x y

  γ : succ x ≤ (succ y +' ∣ y - x ∣)
  γ = ≤-trans (succ x) (succ (y +' ∣ y - x ∣)) (succ y +' ∣ y - x ∣)
       (succ-monotone x (y +' ∣ y - x ∣) Γ)
       (equal-gives-less-than-or-equal
        (succ (y +' ∣ y - x ∣)) (succ y +' ∣ y - x ∣)
        (succ-left y ∣ y - x ∣ ⁻¹))

≤-diff-plus : (x y : ℕ) → x ≤ (∣ x - y ∣ +' y)
≤-diff-plus 0        y        = ⋆
≤-diff-plus (succ x) 0        = ≤-refl x
≤-diff-plus (succ x) (succ y) = ≤-diff-plus x y

triangle-inequality : (x y z : ℕ) → ∣ x - z ∣ ≤ ∣ x - y ∣ +' ∣ y - z ∣
triangle-inequality 0    y z =
 ≤-trans₂ ∣ 0 - z ∣ z (y +' ∣ y - z ∣) (∣ 0 - y ∣ +' ∣ y - z ∣) Γ α γ
  where
   Γ : ∣ 0 - z ∣ ≤ z
   Γ = equal-gives-less-than-or-equal ∣ 0 - z ∣ z (minus-nothing z)

   α : z ≤ (y +' ∣ y - z ∣)
   α = ≤-diff-minus z y

   β : y ≤ ∣ 0 - y ∣
   β = equal-gives-less-than-or-equal y ∣ 0 - y ∣ (minus-nothing y ⁻¹)

   γ : (y +' ∣ y - z ∣) ≤ (∣ 0 - y ∣ +' ∣ y - z ∣)
   γ = ≤-adding y ∣ 0 - y ∣ ∣ y - z ∣ ∣ y - z ∣ β (≤-refl ∣ y - z ∣)
triangle-inequality (succ x) 0    0        = ≤-refl x
triangle-inequality (succ x) 0    (succ z) =
 ≤-trans₂ ∣ x - z ∣ (x +' z) (succ (x +' z)) (succ (succ x +' z))
      (≤-diff x z)
      (≤-succ (x +' z))
      (≤-trans (x +' z) (succ (x +' z)) (succ x +' z) (≤-succ (x +' z)) α )
  where
   α : succ (x +' z) ≤ (succ x +' z)
   α = equal-gives-less-than-or-equal (succ (x +' z)) (succ x +' z)
        (succ-left x z ⁻¹)
triangle-inequality (succ x) (succ y) 0        = ≤-diff-plus x y
triangle-inequality (succ x) (succ y) (succ z) = triangle-inequality x y z

\end{code}

Lane Biocini, 18 September 2023

Another lemma for Absolute Difference

\begin{code}
triangle-inequality-bound : (a b : ℕ) → ¬ (succ (a +' b) ≤ ∣ a - b ∣)
triangle-inequality-bound a b l = not-less-than-itself (a +' b) γ
 where
  Γ : ∣ a - b ∣ ≤ a +' b
  Γ = ≤-diff a b

  γ : succ (a +' b) ≤ (a +' b)
  γ = ≤-trans (succ (a +' b)) ∣ a - b ∣ (a +' b) l Γ

triangle-inequality-bound' : (a b : ℕ) → ¬ (succ (succ a +' b) ≤ ∣ a - b ∣)
triangle-inequality-bound' a b l = triangle-inequality-bound a b γ
 where
  Γ : succ (a +' b) ≤ succ a +' b
  Γ = equal-gives-less-than-or-equal (succ (a +' b)) (succ a +' b)
   (succ-left a b ⁻¹)

  γ : succ (a +' b) ≤ ∣ a - b ∣
  γ = ≤-trans₂ (succ (a +' b)) (succ a +' b) (succ (succ a +' b)) ∣ a - b ∣
       Γ (≤-succ (succ a +' b) ) l
\end{code}

Added 26 September 2025 by Fredrik Nordvall Forsberg.

\begin{code}

double-reflects-≤ : {x y : ℕ} → double x ≤ double y → x ≤ y
double-reflects-≤ {zero} {y} _ = ⋆
double-reflects-≤ {succ x} {succ y} p = double-reflects-≤ {x} {y} p

double-reflects-< : {x y : ℕ} → double x < double y → x < y
double-reflects-< {zero} {succ y} _ = ⋆
double-reflects-< {succ x} {succ y} p = double-reflects-< {x} {y} p

\end{code}

Added 11 October 2025 by Fredrik Nordvall Forsberg.

\begin{code}

open import Naturals.Exponentiation renaming (_ℕ^_ to _^_)

exponential-positive-if-base-positive : (n m : ℕ) → 0 < n → 0 < n ^ m
exponential-positive-if-base-positive n zero _ = ⋆
exponential-positive-if-base-positive n@(succ n') (succ m) l = II
 where
  IH : 0 < (n ^ m)
  IH = exponential-positive-if-base-positive n m l

  I : 0 < (n ^ m) * n
  I = less-than-pos-mult 0 (n ^ m) n' IH

  II : 0 < n * (n ^ m)
  II = transport (0 <_) (mult-commutativity (n ^ m) n) I

exponent-smaller-than-exponential-for-base-at-least-two : (n k : ℕ)
                                                        → 2 ≤ k
                                                        → n ≤ (k ^ n)
exponent-smaller-than-exponential-for-base-at-least-two zero k _ = ⋆
exponent-smaller-than-exponential-for-base-at-least-two
 (succ n) k@(succ (succ k')) l = ≤-<-trans n (1 * k ^ n) (k * (k ^ n)) I III
  where
   IH : n ≤ (k ^ n)
   IH = exponent-smaller-than-exponential-for-base-at-least-two n k l

   I : n ≤ 1 * k ^ n
   I = transport⁻¹ (n ≤_) (mult-left-id (k ^ n)) IH

   II : 0 < k ^ n
   II = exponential-positive-if-base-positive k n ⋆

   III : 1 * (k ^ n) < k * (k ^ n)
   III = multiplication-preserves-strict-order' 1 k (k ^ n) ⋆ II

\end{code}

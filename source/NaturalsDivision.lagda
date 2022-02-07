Andrew Sneap - 27th April 2021

In this file I define the division operator on Natural Numbers, and prove the division theorem.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT renaming (_+_ to _∔_) --TypeTopology

open import NaturalsAddition --TypeTopology
open import NaturalNumbers-Properties -- TypeTopology
open import NaturalsOrder --TypeTopology
open import OrderNotation --TypeTopology
open import UF-Base --TypeTopology
open import UF-Miscelanea -- TypeTopology
open import UF-Subsingletons -- TypeTopology

open import MoreNaturalProperties
open import NaturalsMultiplication
open import NaturalsOrderExtended 

module NaturalsDivision where

_∣_ : ℕ → ℕ → 𝓤₀ ̇
x ∣ y = Σ a ꞉ ℕ , (x * a ≡ y)

_∣_-is-prop : (x y : ℕ) → is-prop (succ x ∣ y)
_∣_-is-prop x y (a , p) (b , p') = to-subtype-≡ (λ _ → ℕ-is-set) (mult-left-cancellable a b x (p ∙ p' ⁻¹))

zero-does-not-divide-positive : (x : ℕ) → ¬(0 ∣ succ x)
zero-does-not-divide-positive x (a , p) = positive-not-zero x (p ⁻¹ ∙ zero-left-is-zero a)

∣-anti-lemma : (x y z : ℕ) → x < y → x < z → x < y * z
∣-anti-lemma x y = induction base step
 where
  base : x < y
       → x < zero
       → x < y * zero
  base _ = id

  step : (k : ℕ)
       → (x < y → x < k → x < y * k)
       → (x < y)
       → (x < succ k)
       → x < y * succ k
  step k IH l₁ _ = <-+ x y (y * k) l₁

product-one-gives-one : (x y : ℕ) → x * y ≡ 1 → x ≡ 1
product-one-gives-one x y r = tri-split (nat-order-trichotomous x 1)
 where
  tri-split : (x < 1) ∔ (x ≡ 1) ∔ (1 < x) → x ≡ 1
  tri-split (inl z) = have succ-no-fp 0 which-contradicts I
    where
      I : 0 ≡ 1
      I = 0     ≡⟨ zero-left-is-zero y ⁻¹                    ⟩
          0 * y ≡⟨ ap (_* y) (less-than-one-is-zero x z ⁻¹ ) ⟩
          x * y ≡⟨ r                                         ⟩
          1     ∎
                                                       
  tri-split (inr (inl z)) = z
  tri-split (inr (inr z)) = tri-split' (nat-order-trichotomous y 1)
   where
    tri-split' : (y < 1) ∔ (y ≡ 1) ∔ (1 < y) → x ≡ 1
    tri-split' (inl z')       = have succ-no-fp 0 which-contradicts I
     where
      I : 0 ≡ 1
      I = 0     ≡⟨ zero-right-is-zero x ⁻¹                    ⟩
          x * 0 ≡⟨ ap (x *_) (less-than-one-is-zero y z' ⁻¹)  ⟩
          x * y ≡⟨ r                                          ⟩
          1     ∎
                                               
    tri-split' (inr (inl z')) = have less-than-not-equal 1 x z which-contradicts I
     where
      I : 1 ≡ x
      I = 1     ≡⟨ r ⁻¹         ⟩
          x * y ≡⟨ ap (x *_) z' ⟩
          x     ∎
    tri-split' (inr (inr z')) = have I which-contradicts (r ⁻¹)
     where
      I : 1 ≡ x * y → 𝟘
      I = less-than-not-equal 1 (x * y) (∣-anti-lemma 1 x y z z')

∣-anti : (x y : ℕ) → x ∣ y → y ∣ x → x ≡ y
∣-anti 0        y (a , p) (b , q) = δ
 where
  δ : zero ≡ y
  δ = zero     ≡⟨ zero-left-is-zero a ⁻¹ ⟩
      zero * a ≡⟨ p                      ⟩
      y        ∎ 
∣-anti (succ x) y (a , p) (b , q) = δ
 where
  a*b-is-one : a * b ≡ 1
  a*b-is-one = mult-left-cancellable (a * b) 1 x I
   where
    I : succ x * (a * b) ≡ succ x * 1
    I = succ x * (a * b) ≡⟨ mult-associativity (succ x) a b ⁻¹ ⟩
        succ x * a * b   ≡⟨ ap (_* b) p                        ⟩
        y * b            ≡⟨ q                                  ⟩
        succ x           ≡⟨ refl ⟩
        succ x * 1       ∎

  b-is-1 : b ≡ 1
  b-is-1 = product-one-gives-one b a I
   where
    I : b * a ≡ 1
    I = b * a ≡⟨ mult-commutativity b a ⟩
        a * b ≡⟨ a*b-is-one             ⟩
        1     ∎                              

  δ : succ x ≡ y
  δ = succ x ≡⟨ q ⁻¹             ⟩
      y * b  ≡⟨ ap (y *_) b-is-1 ⟩
      y      ∎

∣-respects-addition : (x y z : ℕ) → x ∣ y → x ∣ z → x ∣ (y + z)
∣-respects-addition x y z (a , p) (b , q) = (a + b , I)
 where
  I : x * (a + b) ≡ y + z
  I = x * (a + b)   ≡⟨ distributivity-mult-over-nat x a b ⟩
      x * a + x * b ≡⟨ ap (_+ x * b) p                    ⟩
      y + x * b     ≡⟨ ap (y +_) q                        ⟩
      y + z         ∎

∣-respects-multiples : (a b c k l : ℕ) → a ∣ b → a ∣ c → a ∣ (k * b + l * c)
∣-respects-multiples a b c k l (x , p) (y , q) = (k * x + l * y , I)
 where
  I : a * (k * x + l * y) ≡ k * b + l * c
  I = a * (k * x + l * y)       ≡⟨ distributivity-mult-over-nat a (k * x) (l * y)                                     ⟩
      a * (k * x) + a * (l * y) ≡⟨ ap₂ _+_ (ap (a *_) (mult-commutativity k x)) (ap (a *_) (mult-commutativity l y))  ⟩
      a * (x * k) + a * (y * l) ≡⟨ ap₂ _+_ (mult-associativity a x k ⁻¹) (mult-associativity a y l ⁻¹)                ⟩
      (a * x) * k + (a * y) * l ≡⟨ ap₂ _+_ (ap (_* k) p) (ap (_* l) q)                                                ⟩
      b * k + c * l             ≡⟨ ap₂ _+_ (mult-commutativity b k) (mult-commutativity c l)                          ⟩
      k * b + l * c             ∎                                                                                      

∣-trans : (a b c : ℕ) → a ∣ b → b ∣ c → a ∣ c
∣-trans a b c (x , p) (y , q) = (x * y) , I
 where
  I : a * (x * y) ≡ c
  I = a * (x * y)  ≡⟨ mult-associativity a x y ⁻¹ ⟩
      (a * x) * y  ≡⟨ ap ( _* y) p                ⟩
      b * y        ≡⟨ q                           ⟩
      c            ∎

∣-divisor-divides-multiple : (a b k : ℕ) → a ∣ b → a ∣ k * b
∣-divisor-divides-multiple a b k (x , p) = (x * k) , I
 where
  I : a * (x * k) ≡ k * b
  I = a * (x * k) ≡⟨ mult-associativity a x k ⁻¹ ⟩
      a * x * k   ≡⟨ ap (_* k) p                 ⟩
      b * k       ≡⟨ mult-commutativity b k ⟩
      k * b       ∎

divisiontheorem : (a d : ℕ) → 𝓤₀ ̇
divisiontheorem a d = Σ q ꞉ ℕ , Σ r ꞉ ℕ , (a ≡ q * d + r) × (r < d)

division : (a d : ℕ) → divisiontheorem a (succ d)
division a d = induction base step a
 where
  base : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (0 ≡ q * succ d + r) × (r < succ d)  
  base = 0 , (0 , (I , II))
   where
    I : 0 ≡ 0 * succ d + 0
    I = 0         ≡⟨ refl                               ⟩
        0 + 0     ≡⟨ ap (0 +_) (zero-left-is-zero d ⁻¹) ⟩
        0 + 0 * d ∎

    II : 0 < succ d
    II = unique-to-𝟙 (0 < succ d)

  step : (k : ℕ)
       → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (k ≡ q * succ d + r) × (r < succ d)
       → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ k ≡ q * succ d + r) × (r < succ d)
  step k (q , r , e , l) = helper (<-split r d l)
   where
    helper : (r < d) ∔ (r ≡ d) →  Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ k ≡ q * succ d + r) × (r < succ d)
    helper (inl x) = q , succ r , ap succ e , x
    helper (inr x) = succ q , 0 , I , unique-to-𝟙 (0 < succ d)
     where
      I : succ k ≡ succ q + succ q * d
      I = succ k                        ≡⟨ ap succ e                                           ⟩
          succ (q + q * d + r)          ≡⟨ ap succ (ap (q + q * d +_) x)                       ⟩
          succ (q + q * d + d)          ≡⟨ ap succ (addition-associativity q (q * d) d)        ⟩
          succ (q + (q * d + d))        ≡⟨ succ-left q (q * d + d) ⁻¹                          ⟩
          succ q + (q * d + d)          ≡⟨ ap (succ q +_) (ap (_+ d) (mult-commutativity q d)) ⟩
          succ q + (d * q + d)          ≡⟨ ap (succ q +_) (addition-commutativity (d * q) d)   ⟩ 
          succ q + (d + d * q)          ≡⟨ ap (succ q +_) (mult-commutativity d (succ q))      ⟩ 
          succ q + succ q * d           ∎

division-is-prop-lemma : (a b c : ℕ) → a ≤ b → b < c → a < c
division-is-prop-lemma a b c l₀ l₁ = ≤-trans (succ a) (succ b) c l₀ l₁

division-is-prop : (a d : ℕ) → is-prop (divisiontheorem a d)
division-is-prop a d (q₀ , r₀ , α , αₚ) (q₁ , r₁ , β , βₚ) = to-subtype-≡ I II
 where
  I : (q : ℕ) → is-prop (Σ r ꞉ ℕ , (a ≡ q * d + r) × (r < d))
  I q (r₀ , δ) (r₁ , γ) = to-subtype-≡ (λ r → ×-is-prop ℕ-is-set (<-is-prop-valued r d)) remainders-equal
   where
    remainders-equal : r₀ ≡ r₁
    remainders-equal = addition-left-cancellable r₀ r₁ (q * d) i
     where
      i : q * d + r₀ ≡ q * d + r₁
      i = q * d + r₀ ≡⟨ pr₁ δ ⁻¹ ⟩
          a          ≡⟨ pr₁ γ ⟩
          q * d + r₁ ∎

  assumption : q₀ * d + r₀ ≡ q₁ * d + r₁
  assumption = α ⁻¹ ∙ β

  II-abstract : (q q' r r' : ℕ) → q * d + r ≡ q' * d + r' → q < q' → r < d → q ≡ q'
  II-abstract q q' r r' e l₁ l₂ = 𝟘-elim (not-less-than-itself (d * succ k) vii)
   where
    i : Σ k ꞉ ℕ , (succ k) + q ≡ q'
    i = subtraction'' q q' l₁

    k : ℕ
    k = pr₁ i

    μ : (succ k) + q ≡ q'
    μ = pr₂ i

    ii : q * d + r ≡ q * d + ((succ k) * d + r')
    ii = q * d + r                   ≡⟨ e ⟩
         q' * d + r'                 ≡⟨ ap (λ - → - * d + r') (μ ⁻¹) ⟩
         ((succ k) + q) * d + r'     ≡⟨ ap (_+ r') (distributivity-mult-over-nat' (succ k) q d) ⟩
         (succ k) * d + q * d + r'   ≡⟨ ap (_+ r') (addition-commutativity ((succ k) * d) (q * d)) ⟩
         q * d + (succ k) * d + r'   ≡⟨ addition-associativity (q * d) ((succ k) * d) r' ⟩
         q * d + ((succ k) * d + r') ∎

    iii : r' + d * (succ k) ≡ r
    iii = r' + d * succ k         ≡⟨ ap (r' +_) (mult-commutativity d (succ k)) ⟩
          r' + (succ k) * d       ≡⟨ addition-commutativity r' ((succ k) * d) ⟩
          (succ k) * d + r'       ≡⟨ addition-left-cancellable r ((succ k) * d + r') (q * d) ii ⁻¹ ⟩ 
          r                       ∎

    iv : d * (succ k) ≤ r
    iv = cosubtraction (d * succ k) r (r' , iii)

    v : r < d * succ k
    v = less-than-pos-mult r d k l₂
    
    vii : d * succ k < d * succ k
    vii = division-is-prop-lemma (d * succ k) r (d * succ k) iv v

  II : q₀ ≡ q₁
  II = f (nat-order-trichotomous q₀ q₁)
   where
    f : (q₀ < q₁) ∔ (q₀ ≡ q₁) ∔ (q₁ < q₀) → q₀ ≡ q₁
    f (inl z)       = II-abstract q₀ q₁ r₀ r₁ assumption z αₚ
    f (inr (inl z)) = z
    f (inr (inr z)) = II-abstract q₁ q₀ r₁ r₀ (assumption ⁻¹) z βₚ ⁻¹

division' : (a d : ℕ) → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (a ≡ q * (succ d) + r) × (r < (succ d))
division' 0 d     = 0 , (0 , (I , II))
 where
  I : 0 ≡ 0 * succ d + 0
  I = 0         ≡⟨ refl                               ⟩
      0 + 0     ≡⟨ ap (0 +_) (zero-left-is-zero d ⁻¹) ⟩
      0 + 0 * d ∎

  II : 0 < succ d
  II = unique-to-𝟙 (0 < succ d)
division' (succ a) d = f (maximal-from-given' (λ - → - * succ d ≤ succ a) (succ a) (λ q → ≤-decidable (q * succ d) (succ a)) ii)
 where
  i : (0 + 0 * d) ≤ succ a
  i = transport (_≤ succ a) (zero-left-is-zero (succ d) ⁻¹) (zero-minimal (succ a))
    
  ii : Σ k ꞉ ℕ , (k * succ d ≤ succ a) × (k ≤ succ a)
  ii = 0 , i , zero-minimal (succ a)

  f : Σ q ꞉ ℕ , q ≤ succ a × (q * succ d) ≤ succ a × ((n : ℕ) → n ≤ succ a → n * succ d ≤ succ a → n ≤ q)
    → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ a ≡ q * succ d + r) × (r < succ d)
  f (q , l₁ , l₂ , qf) = g (subtraction (q * succ d) (succ a) l₂)
   where
    g : Σ r ꞉ ℕ , r + q * succ d ≡ succ a
      → Σ q ꞉ ℕ , Σ r ꞉ ℕ , (succ a ≡ q * succ d + r) × (r < succ d)
    g (r , rf) = q , r , I , II (order-split r (succ d))
     where
      I : succ a ≡ q * succ d + r
      I = succ a         ≡⟨ rf ⁻¹                                 ⟩
          r + q * succ d ≡⟨ addition-commutativity r (q * succ d) ⟩
          q * succ d + r ∎

      II : r < succ d ∔ r ≥ succ d → r < succ d
      II (inl z) = z
      II (inr z) = 𝟘-elim (not-less-than-itself q IV)
       where
        III : succ q * succ d ≤ succ a
        III = transport₂ _≤_ α (addition-commutativity (q * succ d) r ∙ rf) β
         where
          α : q * succ d + succ d ≡ succ q * succ d
          α = q * succ d + succ d     ≡⟨ ap (q * succ d +_) (mult-left-id (succ d) ⁻¹) ⟩
              q * succ d + 1 * succ d ≡⟨ distributivity-mult-over-nat' q 1 (succ d) ⁻¹ ⟩
              (q + 1) * succ d        ≡⟨ refl ⟩
              succ q * succ d ∎

          β : q * succ d + succ d ≤ q * succ d + r
          β = ≤-n-monotone-left (succ d) r (q * succ d) z

        IV : q < q
        IV = qf (succ q) (product-less-than-cancellable (succ q) d (succ a) III) III

division-agrees-with-division' : (x y : ℕ) → division x y ≡ division' x y
division-agrees-with-division' a d = division-is-prop a (succ d) (division a d) (division' a d)

\end{code}


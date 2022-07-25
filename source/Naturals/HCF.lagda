Andrew Sneap - 27th April 2021
Updated July 2022

In this file I define common divisors, and HCF's, along with a proof
that the Euclidean Algorithm produces HCF's.
\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan renaming (_+_ to _∔_) 

open import Naturals.Addition
open import Naturals.Division
open import Naturals.Multiplication
open import Naturals.Properties
open import Naturals.Order 
open import Notation.Order 
open import UF.Base 
open import UF.FunExt
open import UF.Subsingletons 
open import UF.Subsingletons-FunExt

module Naturals.HCF where

\end{code}

A common divisor d of x and y is a Natural Number which divides x and y,
and clearly is a proposition.

\begin{code}

is-common-divisor : (d x y : ℕ) → 𝓤₀ ̇
is-common-divisor d x y = (d ∣ x) × (d ∣ y)

is-common-divisor-is-prop : (d x y : ℕ) → is-prop (is-common-divisor (succ d) x y)
is-common-divisor-is-prop d x y = ×-is-prop (d ∣ x -is-prop) (d ∣ y -is-prop)

\end{code}

The highest common divisor of x and y is the common divisor of x and y
which is greater than all other common divisors. One way to formulate
the type of the hcf h of x and y is to say that any other common
factor is a divisor of the highest common factor.

\begin{code}

is-hcf : (h x y : ℕ) → 𝓤₀ ̇
is-hcf h x y = (is-common-divisor h x y) × ((d : ℕ) →  is-common-divisor d x y → d ∣ h)

\end{code}

Of course, any we can retrieve from the cartesian product that the hcf
is a common divisor.

\begin{code}

is-hcf-gives-is-common-divisor : (h x y : ℕ) → is-hcf h x y → is-common-divisor h x y
is-hcf-gives-is-common-divisor h x y (a , p) = a

\end{code}

The statement "succ h is the highest common factor of x and y" is a
proposition.  In order to prove this, function extensionality is
required, because the second projection of the cartesian product is a
function. With function extensionality, proof that this statement is a
proposition follows from the proof that (is-common-divisor d x y) is a
proposition.

\begin{code}

is-hcf-is-prop : Fun-Ext → (h x y : ℕ) → is-prop (is-hcf (succ h) x y)
is-hcf-is-prop fe h x y p q = ×-is-prop (is-common-divisor-is-prop h x y) II p q
  where
    I : (d : ℕ) → is-common-divisor d x y → is-prop (d ∣ succ h)
    I 0        i x = 𝟘-elim (zero-does-not-divide-positive h x)
    I (succ d) i   = d ∣ (succ h) -is-prop
  
    II : is-prop ((d : ℕ) → is-common-divisor d x y → d ∣ succ h)
    II p' q' = Π₂-is-prop fe I p' q'

\end{code}

Of course, hcf is commutative, which is easily proved by re-ordering projections.

\begin{code}

hcf-comm : (x y h : ℕ) → is-hcf h x y → is-hcf h y x
hcf-comm x y h ((h∣x , h∣y) , f) = (h∣y , h∣x) , (λ d icd → f d (pr₂ icd , pr₁ icd))

hcf-comm' : (x y : ℕ) → Σ h ꞉ ℕ , is-hcf h x y → Σ h ꞉ ℕ , is-hcf h y x
hcf-comm' x y (h , is-hcf) = h , (hcf-comm x y h is-hcf)

\end{code}

With an eye towards implement Euclid's algorithm to compute the
highest common factor, we now prove two lemmas; each direction of the
following proof:

If x ＝ q * y + r, then is-hcf h x y ⇔ is-hcf y r.

For Euclid's algorithm, we only need the right-to-left implication,
but both are proved for completeness.

The general idea of the right-to-left implication is as follows:

x ＝ q * y + r, h | y and h | r, with h ＝ hcf(y , r).

Now, clearly h | x since h | (q * y + r), and h | y by assumption,
so h is a common factor of x and y.

To show that h is the highest common factor, assume that d | x,
d | y, and further that d * u ＝ x , d * v ＝ y for some u , v.

If we can show that d | y, and d | r, then d | h since is-hcf h y r.
First, d | y by assumption.

Now, d * u ＝ q * (d * v) + r, so by the factor-of-sum-consequence,
d | r, and we are done.

\begin{code}

euclids-algorithm-lemma : (x y q r h : ℕ) → x ＝ q * y + r → is-hcf h x y → is-hcf h y r
euclids-algorithm-lemma x y q r h e (((a , e₀) , b , e₁) , f) = I , II
 where
  I : is-common-divisor h y r
  I = (b , e₁) , factor-of-sum-consequence h a (q * b) r i
   where
    i : h * a ＝ h * (q * b) + r
    i = h * a           ＝⟨ e₀                                            ⟩
        x               ＝⟨ e                                             ⟩
        q * y + r       ＝⟨ ap (λ - → q * - + r) (e₁ ⁻¹)                  ⟩
        q * (h * b) + r ＝⟨ ap (_+ r) (mult-associativity q h b ⁻¹)       ⟩
        q * h * b + r   ＝⟨ ap (λ - → - * b + r) (mult-commutativity q h) ⟩
        h * q * b + r   ＝⟨ ap (_+ r) (mult-associativity h q b)          ⟩
        h * (q * b) + r ∎
        
  II : (d : ℕ) → is-common-divisor d y r → d ∣ h
  II d ((u , e₁) , v , e₂) = f d ((q * u + v , i) , u , e₁)
   where
    i : d * (q * u + v) ＝ x
    i = d * (q * u + v)     ＝⟨ distributivity-mult-over-addition d (q * u) v ⟩
        d * (q * u) + d * v ＝⟨ ap (d * (q * u) +_) e₂                        ⟩
        d * (q * u) + r     ＝⟨ ap (_+ r) (mult-associativity d q u ⁻¹)       ⟩
        d * q * u + r       ＝⟨ ap (λ - → - * u + r) (mult-commutativity d q) ⟩
        q * d * u + r       ＝⟨ ap (_+ r) (mult-associativity q d u)          ⟩
        q * (d * u) + r     ＝⟨ ap (λ - → q * - + r) e₁                       ⟩
        q * y + r           ＝⟨ e ⁻¹                                          ⟩
        x                   ∎

euclids-algorithm-lemma' : (x y q r h : ℕ) → x ＝ q * y + r → is-hcf h y r → is-hcf h x y
euclids-algorithm-lemma' x y q r h e (((a , e₀) , b , e₁) , f) = I , II
 where
  I : is-common-divisor h x y
  I = (q * a + b , i) , (a , e₀)
   where
    i : h * (q * a + b) ＝ x
    i = h * (q * a + b)     ＝⟨ distributivity-mult-over-addition h (q * a) b ⟩
        h * (q * a) + h * b ＝⟨ ap (h * (q * a) +_) e₁                        ⟩
        h * (q * a) + r     ＝⟨ ap (_+ r) (mult-associativity h q a ⁻¹)       ⟩
        h * q * a + r       ＝⟨ ap (λ - → - * a + r) (mult-commutativity h q) ⟩
        q * h * a + r       ＝⟨ ap (_+ r) (mult-associativity q h a)          ⟩
        q * (h * a) + r     ＝⟨ ap (λ - → q * - + r) e₀                       ⟩
        q * y + r           ＝⟨ e ⁻¹                                          ⟩
        x                   ∎  
  II : (d : ℕ) → is-common-divisor d x y → d ∣ h
  II d ((u , e₂) , v , e₃)  = f d ((v , e₃) , factor-of-sum-consequence d u (q * v) r i)
   where
    i : d * u ＝ d * (q * v) + r
    i = d * u           ＝⟨ e₂                                            ⟩
        x               ＝⟨ e                                             ⟩
        q * y + r       ＝⟨ ap (λ - → q * - + r) (e₃ ⁻¹)                  ⟩
        q * (d * v) + r ＝⟨ ap (_+ r) (mult-associativity q d v ⁻¹)       ⟩
        q * d * v + r   ＝⟨ ap (λ - → - * v + r) (mult-commutativity q d) ⟩
        d * q * v + r   ＝⟨ ap (_+ r) (mult-associativity d q v)          ⟩
        d * (q * v) + r ∎


\end{code}

Now we have the function which computes the highest common factor for any two natural numbers x and y.
This function uses course-of-values induction in order to satisfy the Agda termination checker.

The step function includes an induction, which says the following:

If for any number x, we can find a number r with r < x, and for any
number k there exists a highest common factor of r and k, then for any
y there exists a highest common factor of x and y. (In the proof I use y in the IH, but this is not necessary.

\begin{code}

HCF : (x y : ℕ) → Σ h ꞉ ℕ , is-hcf h x y
HCF = course-of-values-induction (λ x → (y : ℕ) → Σ h ꞉ ℕ , is-hcf h x y) step
 where
  step : (x : ℕ) → ((r : ℕ) → r < x → (y : ℕ) → Σ h ꞉ ℕ , is-hcf h r y) → (y : ℕ) → Σ h ꞉ ℕ , is-hcf h x y
  step 0        IH y = y , (everything-divides-zero , ∣-refl) , (λ d icd → pr₂ icd)
  step (succ x) IH y = I (division y x)
   where
    I : Σ q ꞉ ℕ , Σ r ꞉ ℕ , (y ＝ q * succ x + r) × (r < succ x) → Σ h ꞉ ℕ , is-hcf h (succ x) y
    I (q , r , e₀ , l) = II (IH r l (succ x))
     where
      II : Σ h ꞉ ℕ , is-hcf h r (succ x) → Σ h ꞉ ℕ , is-hcf h (succ x) y
      II (h , h-is-hcf) = h , hcf-comm y (succ x) h i
       where
        i : is-hcf h y (succ x)
        i = euclids-algorithm-lemma' y (succ x) q r h e₀ (hcf-comm r (succ x) h h-is-hcf)

hcf : (a b : ℕ) → ℕ
hcf a b = pr₁ (HCF a b)

\end{code}

Two numbers being coprime is also a proposition, as a simple
consequence of hcf being a proposition for all values of h.

Two numbers are coprime in the special case that the hcf is 1.

\begin{code}

coprime : (a b : ℕ) → 𝓤₀ ̇
coprime a b = is-hcf 1 a b

coprime-is-prop : Fun-Ext → (a b : ℕ) → is-prop (coprime a b)
coprime-is-prop fe a b = is-hcf-is-prop fe 0 a b

divbyhcf : (a b : ℕ) → Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h * x ＝ a) × (h * y ＝ b)) × coprime x y
divbyhcf 0 b = b , (0 , (1 , ((refl , refl) , (everything-divides-zero , 1-divides-all 1) , λ d → pr₂)))
divbyhcf (succ a) b = I (HCF (succ a) b)
 where
  I : Σ c ꞉ ℕ , is-hcf c (succ a) b → Σ h ꞉ ℕ , Σ x ꞉ ℕ , Σ y ꞉ ℕ , ((h * x ＝ succ a) × (h * y ＝ b)) × coprime x y 
  I (0 , ((x , xₚ) , y , yₚ) , γ) = 𝟘-elim (positive-not-zero a II)
   where
    II : succ a ＝ 0
    II = succ a  ＝⟨ xₚ ⁻¹                     ⟩
         0 * x   ＝⟨ mult-commutativity zero x ⟩
         0       ∎
  I (succ h , ((x , xₚ) , y , yₚ) , γ) = (succ h) , (x , (y , ((xₚ , yₚ) , (((x , mult-commutativity 1 x) , y , (mult-commutativity 1 y)) , II))))
   where
    II : (f' : ℕ) → is-common-divisor f' x y → f' ∣ 1
    II f' ((α , αₚ) , β , βₚ) = III (γ (succ h * f') ((α , αₚ') , β , βₚ'))
     where
      αₚ' : succ h * f' * α ＝ succ a
      αₚ' = succ h * f' * α     ＝⟨ mult-associativity (succ h) f' α ⟩
            succ h * (f' * α)   ＝⟨ ap (succ h *_) αₚ                ⟩
            succ h * x          ＝⟨ xₚ                               ⟩
            succ a              ∎

      βₚ' : succ h * f' * β ＝ b
      βₚ' = succ h * f' * β   ＝⟨ mult-associativity (succ h) f' β ⟩
            succ h * (f' * β) ＝⟨ ap (succ h *_) βₚ                ⟩
            succ h * y        ＝⟨ yₚ                               ⟩
            b                 ∎

      III : (succ h) * f' ∣ (succ h) → f' ∣ 1
      III (δ , δₚ) = 1 , product-one-gives-one f' δ (mult-left-cancellable (f' * δ) 1 h e)
       where
        e : succ h * (f' * δ) ＝ succ h * 1
        e = succ h * (f' * δ) ＝⟨ mult-associativity (succ h) f' δ ⁻¹ ⟩
            succ h * f' * δ   ＝⟨ δₚ ⟩
            succ h            ∎

hcf-unique : (a b : ℕ) → ((h , p) : Σ h ꞉ ℕ , is-hcf h a b) → ((h' , p') : Σ h' ꞉ ℕ , is-hcf h' a b) → h ＝ h'
hcf-unique a b (h , h-icd , f) (h' , h'-icd , f') = ∣-anti h h' I II
 where
  I : h ∣ h'
  I = f' h h-icd

  II : h' ∣ h
  II = f h' h'-icd

\end{code}

\begin{code}

\end{code}

The statement "x and y have a highest-common-factor" is also a
proposition. Again, function extensionality is required.

To prove that the hcf is unique, we assume there are two different
hcf's. But by the definition of is-hcf, all common factors are factors
of the hcf, and both hcf's are common factors. Two numbers which are
factors of each other are equal by the anti-symmetric property of
division.

\begin{code}

has-hcf : (x y : ℕ) → 𝓤₀ ̇
has-hcf x y = Σ d ꞉ ℕ , is-hcf (succ d) x y

has-hcf-is-prop : Fun-Ext → (x y : ℕ) → is-prop (has-hcf x y)
has-hcf-is-prop fe x y (h₁ , h₁-cf , f) (h₂ , h₂-cf , g) = to-subtype-＝ I II
 where
  I : (d : ℕ) → is-prop (is-hcf (succ d) x y)
  I d = is-hcf-is-prop fe d x y

  II : h₁ ＝ h₂
  II = succ-lc (∣-anti (succ h₁) (succ h₂) α β)
   where
    α : succ h₁ ∣ succ h₂
    α = g (succ h₁) h₁-cf

    β : succ h₂ ∣ succ h₁
    β = f (succ h₂) h₂-cf

\end{code}

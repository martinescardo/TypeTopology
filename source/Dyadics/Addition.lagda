Andrew Sneap

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Dyadics.Type
open import Dyadics.Negation
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import Integers.Type
open import Integers.Addition renaming (_+_ to _ℤ+_)
open import Integers.Multiplication
open import Integers.Negation renaming (-_ to ℤ-_)
open import Naturals.Exponents
open import UF.Base hiding (_≈_)

module Dyadics.Addition where

\end{code}

The usual strategy is applied to define addition of dyadic
rationals. We first define addition of unsimplified dyadics, and then
addition of dyadic rationals is defined by normalising the result of
this addition.

\begin{code}

_+'_ : ℤ × ℕ → ℤ × ℕ → ℤ × ℕ
(p , a) +' (q , b) = p * pos (2^ b) ℤ+ q * pos (2^ a) , a ℕ+ b

_+_ : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
(p , _) + (q , _) = normalise-pos (p +' q)

infixl 32 _+'_
infixl 32 _+_

\end{code}

Commutativity is trivial as usual, and follows by commutativity of
addition of integers and natural numbers. To get commutativity of
addition of dyadic rationals, we can simply take the action on paths
of normalise-pos on addition of unsimplified dyadic rationals.

\begin{code}

ℤ[1/2]+'-comm : (p q : ℤ × ℕ) → p +' q ＝ q +' p
ℤ[1/2]+'-comm (p , a) (q , b) = ap₂ _,_ I II
 where
  I : p * pos (2^ b) ℤ+ q * pos (2^ a) ＝ q * pos (2^ a) ℤ+ p * pos (2^ b)
  I = ℤ+-comm (p * pos (2^ b)) (q * pos (2^ a))
  II : a ℕ+ b ＝ b ℕ+ a
  II = addition-commutativity a b

ℤ[1/2]+-comm : (p q : ℤ[1/2]) → p + q ＝ q + p
ℤ[1/2]+-comm (p , _) (q , _) = ap normalise-pos (ℤ[1/2]+'-comm p q)

\end{code}

For associativity, it is slightly more involved. It's not possible to
take the action on paths as with commutativity, because on each side
we have two addition, meaning we apply normalise-pos on intermediate
calculations. The idea of the associativity proof is as follows:

(p , α) + (q , β) + (r , γ) = normalise-pos p + normalise-pos q + normalise-pos r
                            = normalise-pos (p +' q) + normalise-pos r
                            = normalise-pos (p +' q +' r)                          
                            = normalise-pos (p +' (q +' r))
                            = normalise-pos p + normalise (q +' r)
                            = normalise-pos p + (normalise pos q + normalise-pos r)
                            = (p , α) + ((q , β) + (r , γ)) ∎

This proof requires that proof that (p , α) ＝ normalise-pos p, which
is proved in the Dyadics.Type file. It also requires that
(normalise-pos p + normalise-pos q) ＝ (normalise-pos (p +' q)).

This proof follows, preceded by a lemma about equivalences on
unsimplified rationals.

\begin{code}

ℤ[1/2]+'-≈' : (p q r : ℤ × ℕ) → p ≈' q → (p +' r) ≈' (q +' r)
ℤ[1/2]+'-≈' (p , a) (q , b) (r , c) e = γ
 where
  e' : p * pos (2^ b) ＝ q * pos (2^ a)
  e' = e

  rearrangement₁ : (a : ℤ) (b c d : ℕ) → a * pos (2^ b) * pos (2^ (c ℕ+ d)) ＝ a * pos (2^ c) * pos (2^ (b ℕ+ d))
  rearrangement₁ a b c d = a * pos (2^ b) * pos (2^ (c ℕ+ d))         ＝⟨ ap (λ - → a * pos (2^ b) * pos -) (prod-of-powers 2 c d ⁻¹) ⟩
                           a * pos (2^ b) * pos (2^ c ℕ* 2^ d)        ＝⟨ ap (a * pos (2^ b) *_) (pos-multiplication-equiv-to-ℕ (2^ c) (2^ d) ⁻¹) ⟩
                           a * pos (2^ b) * (pos (2^ c) * pos (2^ d)) ＝⟨ ℤ*-assoc (a * pos (2^ b)) (pos (2^ c)) (pos (2^ d)) ⁻¹ ⟩
                           a * pos (2^ b) * pos (2^ c) * pos (2^ d)   ＝⟨ ap (_* pos (2^ d)) (ℤ*-assoc a (pos (2^ b)) (pos (2^ c))) ⟩
                           a * (pos (2^ b) * pos (2^ c)) * pos (2^ d) ＝⟨ ap (λ - → a * - * pos (2^ d)) (ℤ*-comm (pos (2^ b)) (pos (2^ c))) ⟩
                           a * (pos (2^ c) * pos (2^ b)) * pos (2^ d) ＝⟨ ap (_* pos (2^ d)) (ℤ*-assoc a (pos (2^ c)) (pos (2^ b)) ⁻¹) ⟩
                           a * pos (2^ c) * pos (2^ b) * pos (2^ d)   ＝⟨ ℤ*-assoc (a * pos (2^ c)) (pos (2^ b)) (pos (2^ d)) ⟩
                           a * pos (2^ c) * (pos (2^ b) * pos (2^ d)) ＝⟨ ap (a * pos (2^ c) *_) (pos-multiplication-equiv-to-ℕ (2^ b) (2^ d)) ⟩
                           a * pos (2^ c) * pos (2^ b ℕ* 2^ d)        ＝⟨ ap (λ - → a * pos (2^ c) * pos - ) (prod-of-powers 2 b d) ⟩
                           a * pos (2^ c) * pos (2^ (b ℕ+ d)) ∎

  I : p * pos (2^ c) * pos (2^ (b ℕ+ c)) ＝ q * pos (2^ c) * pos (2^ (a ℕ+ c))
  I = p * pos (2^ c) * pos (2^ (b ℕ+ c))   ＝⟨ rearrangement₁ p c b c ⟩
      p * pos (2^ b) * pos (2^ (c ℕ+ c))   ＝⟨ ap (_* pos (2^ (c ℕ+ c))) e ⟩
      q * pos (2^ a) * pos (2^ (c ℕ+ c))   ＝⟨ rearrangement₁ q a c c ⟩
      q * pos (2^ c) * pos (2^ (a ℕ+ c))      ∎
  
  γ : (p * pos (2^ c) ℤ+ r * pos (2^ a)) * pos (2^ (b ℕ+ c)) -- lhs of unfolded type
    ＝ (q * pos (2^ c) ℤ+ r * pos (2^ b)) * pos (2^ (a ℕ+ c)) -- rhs of unfolded type
  γ = (p * pos (2^ c) ℤ+ r * pos (2^ a)) * pos (2^ (b ℕ+ c))                   ＝⟨ distributivity-mult-over-ℤ (p * pos (2^ c)) (r * pos (2^ a)) (pos (2^ (b ℕ+ c))) ⟩
      p * pos (2^ c) * pos (2^ (b ℕ+ c)) ℤ+ r * pos (2^ a) * pos (2^ (b ℕ+ c)) ＝⟨ ap (p * pos (2^ c) * pos (2^ (b ℕ+ c)) ℤ+_) (rearrangement₁ r a b c) ⟩
      p * pos (2^ c) * pos (2^ (b ℕ+ c)) ℤ+ r * pos (2^ b) * pos (2^ (a ℕ+ c)) ＝⟨ ap (_ℤ+ r * pos (2^ b) * pos (2^ (a ℕ+ c))) I ⟩
      q * pos (2^ c) * pos (2^ (a ℕ+ c)) ℤ+ r * pos (2^ b) * pos (2^ (a ℕ+ c)) ＝⟨ distributivity-mult-over-ℤ (q * pos (2^ c)) (r * pos (2^ b)) (pos (2^ (a ℕ+ c))) ⁻¹ ⟩       
      (q * pos (2^ c) ℤ+ r * pos (2^ b)) * pos (2^ (a ℕ+ c))                   ∎

ℤ[1/2]+-normalise-pos : (p q : ℤ × ℕ) → normalise-pos (p +' q) ＝ (normalise-pos p) + (normalise-pos q)
ℤ[1/2]+-normalise-pos p q = ≈'-to-＝ (p +' q) (p' +' q') γ
 where
  p' = from-ℤ[1/2] (normalise-pos p)
  q' = from-ℤ[1/2] (normalise-pos q)

  I : p ≈' p'
  I = ≈'-normalise-pos p

  II : q ≈' q'
  II = ≈'-normalise-pos q
  
  III : (p +' q) ≈' (p' +' q)
  III = ℤ[1/2]+'-≈' p p' q I

  IV : (q +' p') ≈' (q' +' p')
  IV = ℤ[1/2]+'-≈' q q' p' II

  V : (p' +' q) ≈' (p' +' q')
  V = transport₂ _≈'_ (ℤ[1/2]+'-comm q p') (ℤ[1/2]+'-comm q' p') IV

  γ : (p +' q) ≈' (p' +' q')
  γ = ≈'-trans (p +' q) (p' +' q) (p' +' q') III V

ℤ[1/2]+'-assoc : (p q r : ℤ × ℕ) → (p +' q) +' r ＝ p +' (q +' r)
ℤ[1/2]+'-assoc (p , a) (q , b) (r , c) = to-×-＝' (γ₁ , γ₂)
 where
  I : (p * pos (2^ b) ℤ+ q * pos (2^ a)) * pos (2^ c) ＝ p * (pos (2^ b) * pos (2^ c)) ℤ+ q * pos (2^ c) * pos (2^ a)
  I = (p * pos (2^ b) ℤ+ q * pos (2^ a)) * pos (2^ c)             ＝⟨ distributivity-mult-over-ℤ (p * pos (2^ b)) (q * pos (2^ a)) (pos (2^ c)) ⟩
      p * pos (2^ b) * pos (2^ c) ℤ+ q * pos (2^ a) * pos (2^ c)  ＝⟨ ap ( p * pos (2^ b) * pos (2^ c) ℤ+_) (ℤ-mult-rearrangement q (pos (2^ a)) (pos (2^ c))) ⟩
      p * pos (2^ b) * pos (2^ c) ℤ+ q * pos (2^ c) * pos (2^ a)  ＝⟨ ap (_ℤ+ q * pos (2^ c) * pos (2^ a)) (ℤ*-assoc p (pos (2^ b)) (pos (2^ c)) ) ⟩    
      p * (pos (2^ b) * pos (2^ c)) ℤ+ q * pos (2^ c) * pos (2^ a) ∎
  
  γ₁ : (p * pos (2^ b) ℤ+ q * pos (2^ a)) * pos (2^ c) ℤ+ r * pos (2^ (a ℕ+ b)) ＝ p * pos (2^ (b ℕ+ c)) ℤ+ (q * pos (2^ c) ℤ+ r * pos (2^ b)) * pos (2^ a)
  γ₁ = (p * pos (2^ b) ℤ+ q * pos (2^ a)) * pos (2^ c) ℤ+ r * pos (2^ (a ℕ+ b))                      ＝⟨ i ⟩
       (p * pos (2^ b) ℤ+ q * pos (2^ a)) * pos (2^ c) ℤ+ r * pos (2^ a ℕ* 2^ b)                     ＝⟨ ii ⟩
       (p * pos (2^ b) ℤ+ q * pos (2^ a)) * pos (2^ c) ℤ+ r * (pos (2^ a) * pos (2^ b))              ＝⟨ iii ⟩
       p * (pos (2^ b) * pos (2^ c)) ℤ+ q * pos (2^ c) * pos (2^ a) ℤ+ r * (pos (2^ a) * pos (2^ b)) ＝⟨ iv ⟩
       p * (pos (2^ b) * pos (2^ c)) ℤ+ q * pos (2^ c) * pos (2^ a) ℤ+ r * (pos (2^ b) * pos (2^ a)) ＝⟨ v ⟩
       p * (pos (2^ b) * pos (2^ c)) ℤ+ q * pos (2^ c) * pos (2^ a) ℤ+ r * pos (2^ b) * pos (2^ a)   ＝⟨ vi ⟩
       p * (pos (2^ b) * pos (2^ c)) ℤ+ (q * pos (2^ c) * pos (2^ a) ℤ+ r * pos (2^ b) * pos (2^ a)) ＝⟨ vii ⟩
       p * (pos (2^ b) * pos (2^ c)) ℤ+ (q * pos (2^ c) ℤ+ r * pos (2^ b)) * pos (2^ a)              ＝⟨ viii ⟩
       p * pos (2^ b ℕ* 2^ c) ℤ+ (q * pos (2^ c) ℤ+ r * pos (2^ b)) * pos (2^ a)                     ＝⟨ ix ⟩      
       p * pos (2^ (b ℕ+ c)) ℤ+ (q * pos (2^ c) ℤ+ r * pos (2^ b)) * pos (2^ a)                      ∎
        where
         i = ap (λ - → (p * pos (2^ b) ℤ+ q * pos (2^ a)) * pos (2^ c) ℤ+ r * pos -) (prod-of-powers 2 a b ⁻¹)
         ii = ap (λ - → (p * pos (2^ b) ℤ+ q * pos (2^ a)) * pos (2^ c) ℤ+ r * -) (pos-multiplication-equiv-to-ℕ (2^ a) (2^ b) ⁻¹)
         iii = ap (λ - → - ℤ+ r * (pos (2^ a) * pos (2^ b))) I
         iv = ap (λ - → p * (pos (2^ b) * pos (2^ c)) ℤ+ q * pos (2^ c) * pos (2^ a) ℤ+ r * -) (ℤ*-comm (pos (2^ a)) (pos (2^ b)))
         v = ap (λ - → p * (pos (2^ b) * pos (2^ c)) ℤ+ q * pos (2^ c) * pos (2^ a) ℤ+ -) (ℤ*-assoc r (pos (2^ b)) (pos (2^ a)) ⁻¹)
         vi = ℤ+-assoc (p * (pos (2^ b) * pos (2^ c))) ((q * pos (2^ c) * pos (2^ a))) (r * pos (2^ b) * pos (2^ a))
         vii = ap (λ - → p * (pos (2^ b) * pos (2^ c)) ℤ+ -) (distributivity-mult-over-ℤ (q * pos (2^ c)) (r * pos (2^ b)) (pos (2^ a)) ⁻¹)
         viii = ap (λ - → p * - ℤ+ (q * pos (2^ c) ℤ+ r * pos (2^ b)) * pos (2^ a)) (pos-multiplication-equiv-to-ℕ (2^ b) (2^ c))
         ix = ap (λ - → p * pos - ℤ+ (q * pos (2^ c) ℤ+ r * pos (2^ b)) * pos (2^ a)) (prod-of-powers 2 b c)
        
  γ₂ : a ℕ+ b ℕ+ c ＝ a ℕ+ (b ℕ+ c)
  γ₂ = addition-associativity a b c

ℤ[1/2]+-assoc : (p q r : ℤ[1/2]) → p + q + r ＝ p + (q + r)
ℤ[1/2]+-assoc (p , α) (q , β) (r , δ) = γ
 where
  γ : (p , α) + (q , β) + (r , δ) ＝ (p , α) + ((q , β) + (r , δ))
  γ = (p , α) + (q , β) + (r , δ)              ＝⟨ refl ⟩
      normalise-pos (p +' q) + (r , δ)         ＝⟨ ap (λ - → normalise-pos (p +' q) + -) (ℤ[1/2]-to-normalise-pos (r , δ)) ⟩
      normalise-pos (p +' q) + normalise-pos r ＝⟨ ℤ[1/2]+-normalise-pos (p +' q) r ⁻¹ ⟩
      normalise-pos ((p +' q) +' r)            ＝⟨ ap normalise-pos (ℤ[1/2]+'-assoc p q r) ⟩
      normalise-pos (p +' (q +' r))            ＝⟨ ℤ[1/2]+-normalise-pos p (q +' r) ⟩
      normalise-pos p + normalise-pos (q +' r) ＝⟨ ap (_+ normalise-pos (q +' r)) (ℤ[1/2]-to-normalise-pos (p , α) ⁻¹) ⟩
      (p , α) + normalise-pos (q +' r)         ＝⟨ refl ⟩      
      (p , α) + ((q , β) + (r , δ)) ∎

ℤ[1/2]'-zero-left-neutral : (p : ℤ × ℕ) → (pos 0 , 0) +' p ＝ p
ℤ[1/2]'-zero-left-neutral (p , a) = ap₂ _,_ γ₁ γ₂
 where
  γ₁ : pos 0 * pos (2^ a) ℤ+ p * pos (2^ 0) ＝ p
  γ₁ = pos 0 * pos (2^ a) ℤ+ p * pos (2^ 0) ＝⟨ ap (_ℤ+ p * pos (2^ 0)) (ℤ-zero-left-base (pos (2^ a))) ⟩
       pos 0 ℤ+ p                           ＝⟨ ℤ-zero-left-neutral p ⟩
       p                                    ∎

  γ₂ : 0 ℕ+ a ＝ a
  γ₂ = zero-left-neutral a
  
ℤ[1/2]-zero-left-neutral : (q : ℤ[1/2]) → 0ℤ[1/2] + q ＝ q
ℤ[1/2]-zero-left-neutral (q , α) = γ
 where
  γ : 0ℤ[1/2] + (q , α) ＝ (q , α)
  γ = 0ℤ[1/2] + (q , α)                 ＝⟨ refl ⟩
      normalise-pos ((pos 0 , 0) +' q)  ＝⟨ ap normalise-pos (ℤ[1/2]'-zero-left-neutral q) ⟩
      normalise-pos q                   ＝⟨ ℤ[1/2]-to-normalise-pos (q , α) ⁻¹ ⟩
      (q , α) ∎

ℤ[1/2]-zero-right-neutral : (q : ℤ[1/2]) → q + 0ℤ[1/2] ＝ q
ℤ[1/2]-zero-right-neutral q = ℤ[1/2]+-comm 0ℤ[1/2] q ⁻¹ ∙ ℤ[1/2]-zero-left-neutral q

ℤ[1/2]-negation-dist : (p q : ℤ[1/2]) → - p + q ＝ (- p) + (- q)
ℤ[1/2]-negation-dist ((p , a) , α) ((q , b) , β) = γ
 where 
  γ : - ((p , a) , α) + ((q , b) , β) ＝ (- ((p , a) , α)) + (- ((q , b) , β))
  γ = - ((p , a) , α) + ((q , b) , β)                                     ＝⟨ ap (λ z → - ((p , a) , α) + z) (ℤ[1/2]-to-normalise-pos ((q , b) , β)) ⟩
      - ((p , a) , α) + normalise-pos (q , b)                             ＝⟨ ap (λ z → - z + normalise-pos (q , b)) (ℤ[1/2]-to-normalise-pos ((p , a) , α)) ⟩
      - normalise-pos (p , a) + normalise-pos (q , b)                     ＝⟨ ap -_ (ℤ[1/2]+-normalise-pos (p , a) (q , b) ⁻¹) ⟩
      - normalise-pos ((p , a) +' (q , b))                                ＝⟨ refl ⟩
      - normalise-pos (p * pos (2^ b) ℤ+ q * pos (2^ a) , a ℕ+ b)         ＝⟨ minus-normalise-pos (p * pos (2^ b) ℤ+ q * pos (2^ a)) (a ℕ+ b) ⟩
      normalise-pos (ℤ- (p * pos (2^ b) ℤ+ q * pos (2^ a)) , a ℕ+ b)      ＝⟨ ap (λ z → normalise-pos (z , a ℕ+ b)) (negation-dist (p * pos (2^ b)) (q * pos (2^ a)) ⁻¹) ⟩
      normalise-pos ((ℤ- p * pos (2^ b)) ℤ+ (ℤ- q * pos (2^ a)) , a ℕ+ b) ＝⟨ ap (λ z → normalise-pos (z ℤ+ (ℤ- q * pos (2^ a)) , a ℕ+ b)) (negation-dist-over-mult' p (pos (2^ b)) ⁻¹) ⟩
      normalise-pos ((ℤ- p) * pos (2^ b) ℤ+ (ℤ- q * pos (2^ a)) , a ℕ+ b) ＝⟨ ap (λ z → normalise-pos ((ℤ- p) * pos (2^ b) ℤ+ z , a ℕ+ b)) (negation-dist-over-mult' q (pos (2^ a)) ⁻¹) ⟩
      normalise-pos ((ℤ- p) * pos (2^ b) ℤ+ (ℤ- q) * pos (2^ a) , a ℕ+ b) ＝⟨ refl ⟩
      normalise-pos ((ℤ- p , a) +' (ℤ- q , b))                            ＝⟨ ℤ[1/2]+-normalise-pos (ℤ- p , a) (ℤ- q , b) ⟩
      normalise-pos (ℤ- p , a) + normalise-pos (ℤ- q , b)                 ＝⟨ ap (_+ normalise-pos (ℤ- q , b)) (minus-normalise-pos p a ⁻¹) ⟩
      (- normalise-pos (p , a)) + normalise-pos (ℤ- q , b)                ＝⟨ ap ((- normalise-pos (p , a)) +_) (minus-normalise-pos q b ⁻¹) ⟩
      (- normalise-pos (p , a)) + (- normalise-pos (q , b))               ＝⟨ ap (λ z → (- normalise-pos (p , a)) + (- z)) (ℤ[1/2]-to-normalise-pos ((q , b) , β) ⁻¹) ⟩
      (- normalise-pos (p , a)) + (- ((q , b) , β))                       ＝⟨ ap (λ z → (- z) + (- ((q , b) , β))) (ℤ[1/2]-to-normalise-pos ((p , a) , α) ⁻¹) ⟩            
      (- ((p , a) , α)) + (- ((q , b) , β)) ∎

\end{code}

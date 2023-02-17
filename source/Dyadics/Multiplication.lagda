Andrew Sneap

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Dyadics.Rationals
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Type
open import Naturals.Addition renaming (_+_ to _ℕ+_)
open import Naturals.Exponents
open import Naturals.Multiplication renaming (_*_ to _ℕ*_)
open import UF.Base hiding (_≈_)

module Dyadics.Multiplication where

\end{code}

Instead of defining multiplication by pattern matching, we define it
by using the reducing function. This has efficiency implications, but
avoiding pattern matching helps to reduce the size of proofs.

We use an intermediate _*'_ relation (as in the approach with rationals).

\begin{code}

_*'_ : (p q : ℤ × ℕ) → ℤ × ℕ
(p , a) *' (q , b) = p ℤ* q , a ℕ+ b

ℤ[1/2]*'-comm : (p q : ℤ × ℕ) → p *' q ＝ q *' p
ℤ[1/2]*'-comm (p , a) (q , b) = ap₂ _,_ (ℤ*-comm p q) (addition-commutativity a b)

infixl 33 _*'_

_*_ : ℤ[1/2] → ℤ[1/2] → ℤ[1/2]
(p , _) * (q , _) = normalise-pos (p *' q)

infixl 33 _*_

\end{code}

Commutativity for multiplication is trivial (as usual), relying only
on commutativity properties of integer multiplication and natural
number addition.

\begin{code}

ℤ[1/2]*-comm : (p q : ℤ[1/2]) → (p * q) ＝ (q * p)
ℤ[1/2]*-comm ((p , a) , α) ((q , b) , β) = γ
 where
  γ : (((p , a) , α) * ((q , b) , β)) ＝ (((q , b) , β) * ((p , a) , α))
  γ = ((p , a) , α) * ((q , b) , β)   ＝⟨ refl  ⟩
      normalise-pos (p ℤ* q , a ℕ+ b) ＝⟨ ap normalise-pos (ℤ[1/2]*'-comm (p , a) (q , b)) ⟩
      normalise-pos (q ℤ* p , b ℕ+ a) ＝⟨ refl ⟩
      ((q , b) , β) * ((p , a) , α)   ∎

\end{code}

Looking towards the associativity proof, we expect to need the proof
that multiplication respects the normalisation function on dyadic
rationals.

We will also need the prove associativity of the intermediate
multiplication operation.

\begin{code}

ℤ[1/2]-rearrangement-lemma : (p q : ℤ) → (a b : ℕ) → p ℤ* q ℤ* pos (2^ (a ℕ+ b)) ＝ p ℤ* pos (2^ a) ℤ* q ℤ* pos (2^ b)
ℤ[1/2]-rearrangement-lemma p q a b = γ
 where
  γ : p ℤ* q ℤ* pos (2^ (a ℕ+ b)) ＝ p ℤ* pos (2^ a) ℤ* q ℤ* pos (2^ b)
  γ = p ℤ* q ℤ* pos (2^ (a ℕ+ b))          ＝⟨ ap (λ - →  p ℤ* q ℤ* pos -) (prod-of-powers 2 a b ⁻¹) ⟩
      p ℤ* q ℤ* pos (2^ a ℕ* 2^ b)         ＝⟨ ap (p ℤ* q ℤ*_) (pos-multiplication-equiv-to-ℕ (2^ a) (2^ b) ⁻¹) ⟩
      p ℤ* q ℤ* (pos (2^ a) ℤ* pos (2^ b)) ＝⟨ ℤ*-assoc (p ℤ* q) (pos (2^ a)) (pos (2^ b)) ⁻¹ ⟩
      p ℤ* q ℤ* pos (2^ a) ℤ* pos (2^ b)   ＝⟨ ap (_ℤ* pos (2^ b)) (ℤ*-assoc p q (pos (2^ a))) ⟩
      p ℤ* (q ℤ* pos (2^ a)) ℤ* pos (2^ b) ＝⟨ ap (λ - → p ℤ* - ℤ* pos (2^ b)) (ℤ*-comm q (pos (2^ a))) ⟩
      p ℤ* (pos (2^ a) ℤ* q) ℤ* pos (2^ b) ＝⟨ ap (_ℤ* pos (2^ b)) (ℤ*-assoc p (pos (2^ a)) q ⁻¹) ⟩
      p ℤ* pos (2^ a) ℤ* q ℤ* pos (2^ b)   ∎
      
ℤ[1/2]*'-≈' : (p q r : ℤ × ℕ) → p ≈' q → (p *' r) ≈' (q *' r)
ℤ[1/2]*'-≈' (p , a) (q , b) (r , c) e = γ
 where
  e' : p ℤ* pos (2^ b) ＝ q ℤ* pos (2^ a) -- Unfolded goal type
  e' = e
  
  γ : p ℤ* r ℤ* pos (2^ (b ℕ+ c)) ＝ q ℤ* r ℤ* pos (2^ (a ℕ+ c))
  γ = p ℤ* r ℤ* pos (2^ (b ℕ+ c))          ＝⟨ ℤ[1/2]-rearrangement-lemma p r b c ⟩
      p ℤ* pos (2^ b) ℤ* r ℤ* pos (2^ c)   ＝⟨ ap (λ - → - ℤ* r ℤ* pos (2^ c)) e' ⟩
      q ℤ* pos (2^ a) ℤ* r ℤ* pos (2^ c)   ＝⟨ ℤ[1/2]-rearrangement-lemma q r a c ⁻¹ ⟩      
      q ℤ* r ℤ* pos (2^ (a ℕ+ c)) ∎

ℤ[1/2]*-normalise-pos : (p q : ℤ × ℕ) → normalise-pos (p *' q) ＝ normalise-pos p * normalise-pos q
ℤ[1/2]*-normalise-pos p q = ≈'-to-＝ (p *' q) (p' *' q') γ
 where
  p' = from-ℤ[1/2] (normalise-pos p)
  q' = from-ℤ[1/2] (normalise-pos q)

  I : p ≈' p'
  I = ≈'-normalise-pos p

  II : q ≈' q'
  II = ≈'-normalise-pos q

  III : (p *' q) ≈' (p' *' q)
  III = ℤ[1/2]*'-≈' p p' q I

  IV : (q *' p') ≈' (q' *' p')
  IV = ℤ[1/2]*'-≈' q q' p' II

  V : (p' *' q) ≈' (p' *' q')
  V = transport₂ _≈'_ (ℤ[1/2]*'-comm q p') (ℤ[1/2]*'-comm q' p') IV

  γ : (p *' q) ≈' (p' *' q')
  γ = ≈'-trans (p *' q) (p' *' q) (p' *' q') III V

ℤ[1/2]*'-assoc : (p q r : ℤ × ℕ) → p *' q *' r ＝ p *' (q *' r)
ℤ[1/2]*'-assoc (p , a) (q , b) (r , c) = γ
 where
  γ : (p , a) *' (q , b) *' (r , c) ＝ (p , a) *' ((q , b) *' (r , c))
  γ = (p , a) *' (q , b) *' (r , c)   ＝⟨ refl ⟩
      (p ℤ* q , a ℕ+ b) *' (r , c)    ＝⟨ refl ⟩
      p ℤ* q ℤ* r , a ℕ+ b ℕ+ c       ＝⟨ ap (_, a ℕ+ b ℕ+ c) (ℤ*-assoc p q r) ⟩
      p ℤ* (q ℤ* r) , a ℕ+ b ℕ+ c     ＝⟨ ap (p ℤ* (q ℤ* r) ,_) (addition-associativity a b c) ⟩
      p ℤ* (q ℤ* r) , a ℕ+ (b ℕ+ c)   ＝⟨ refl ⟩
      (p , a) *' (q ℤ* r , b ℕ+ c)    ＝⟨ refl ⟩
      (p , a) *' ((q , b) *' (r , c)) ∎

\end{code}

Now associativity follows, since normalisation of a dyadic gives the
same dyadic, and using the above two proofs.

\begin{code}

ℤ[1/2]*-assoc : (p q r : ℤ[1/2]) → p * q * r ＝ p * (q * r)
ℤ[1/2]*-assoc (p , α) (q , β) (r , δ) = γ
 where
  γ : (p , α) * (q , β) * (r , δ) ＝ (p , α) * ((q , β) * (r , δ))
  γ = (p , α) * (q , β) * (r , δ)              ＝⟨ refl ⟩
      normalise-pos (p *' q) * (r , δ)         ＝⟨ ap (λ - → (normalise-pos (p *' q)) * -) (ℤ[1/2]-to-normalise-pos (r , δ)) ⟩
      normalise-pos (p *' q) * normalise-pos r ＝⟨ ℤ[1/2]*-normalise-pos (p *' q) r ⁻¹ ⟩
      normalise-pos ((p *' q) *' r)            ＝⟨ ap normalise-pos (ℤ[1/2]*'-assoc p q r) ⟩ 
      normalise-pos (p *' (q *' r))            ＝⟨ ℤ[1/2]*-normalise-pos p (q *' r) ⟩
      normalise-pos p * normalise-pos (q *' r) ＝⟨ ap (_* normalise-pos (q *' r)) (ℤ[1/2]-to-normalise-pos (p , α) ⁻¹) ⟩
      (p , α) * normalise-pos (q *' r)         ＝⟨ refl ⟩
      (p , α) * ((q , β) * (r , δ))            ∎

\end{code}

Now we prove the zero and unit laws for multiplication. In each case
we prove one side, and the other follows by commutativity.

\begin{code}

ℤ[1/2]*-zero-left-base : (p : ℤ[1/2]) → 0ℤ[1/2] * p ＝ 0ℤ[1/2]
ℤ[1/2]*-zero-left-base (p , α) = γ
 where
  x = pr₁ p -- numerator   of p
  a = pr₂ p -- denominator of p
  
  γ : 0ℤ[1/2] * (p , α) ＝ 0ℤ[1/2]
  γ = 0ℤ[1/2] * (p , α)                           ＝⟨ ap (0ℤ[1/2] *_) (ℤ[1/2]-to-normalise-pos (p , α)) ⟩
      0ℤ[1/2] * normalise-pos p                   ＝⟨ refl ⟩
      normalise-pos (pos 0 , 0) * normalise-pos p ＝⟨ ℤ[1/2]*-normalise-pos (pos 0 , 0) p ⁻¹ ⟩
      normalise-pos ((pos 0 , 0) *' p)            ＝⟨ refl ⟩
      normalise-pos ((pos 0 , 0) *' (x , a))      ＝⟨ refl ⟩
      normalise-pos (pos 0 ℤ* x , 0 ℕ+ a)         ＝⟨ ap₂ (λ -₁ -₂ → normalise-pos (-₁ , -₂)) (ℤ-zero-left-base x) (zero-left-neutral a) ⟩
      normalise-pos (pos 0 , a)                   ＝⟨ ℤ[1/2]-numerator-zero-is-zero' a ⟩
      0ℤ[1/2] ∎

ℤ[1/2]*-zero-right-base : (p : ℤ[1/2]) → p * 0ℤ[1/2] ＝ 0ℤ[1/2]
ℤ[1/2]*-zero-right-base p = ℤ[1/2]*-comm p 0ℤ[1/2] ∙ ℤ[1/2]*-zero-left-base p

ℤ[1/2]*-mult-left-id : (p : ℤ[1/2]) → 1ℤ[1/2] * p ＝ p
ℤ[1/2]*-mult-left-id (p , α) = γ
 where
  x = pr₁ p -- numerator   of p
  a = pr₂ p -- denominator of p

  I : (pos 1 , 0) *' (x , a) ＝ (x , a)
  I = (pos 1 , 0) *' (x , a) ＝⟨ refl ⟩
      pos 1 ℤ* x , 0 ℕ+ a    ＝⟨ ap (_, 0 ℕ+ a) (ℤ-mult-left-id x) ⟩
      x , 0 ℕ+ a             ＝⟨ ap (x ,_) (zero-left-neutral a) ⟩
      x , a ∎
  
  γ : 1ℤ[1/2] * (p , α) ＝ (p , α)
  γ = 1ℤ[1/2] * (p , α)                           ＝⟨ ap (1ℤ[1/2] *_) (ℤ[1/2]-to-normalise-pos (p , α)) ⟩
      1ℤ[1/2] * normalise-pos p                   ＝⟨ ap (_* normalise-pos p) (ℤ[1/2]-to-normalise-pos 1ℤ[1/2]) ⟩
      normalise-pos (pos 1 , 0) * normalise-pos p ＝⟨ ℤ[1/2]*-normalise-pos (pos 1 , 0) p ⁻¹ ⟩
      normalise-pos ((pos 1 , 0) *' (x , a))      ＝⟨ ap normalise-pos I ⟩
      normalise-pos (x , a)                       ＝⟨ refl ⟩
      normalise-pos p                             ＝⟨ ℤ[1/2]-to-normalise-pos (p , α) ⁻¹ ⟩      
      (p , α) ∎

ℤ[1/2]*-mult-right-id : (p : ℤ[1/2]) → p * 1ℤ[1/2] ＝ p
ℤ[1/2]*-mult-right-id p = ℤ[1/2]*-comm p 1ℤ[1/2] ∙ ℤ[1/2]*-mult-left-id p

\end{code}

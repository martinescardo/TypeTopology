Andrew Sneap

\begin{code}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Dyadics.Rationals
open import Integers.Multiplication renaming (_*_ to _ℤ*_)
open import Integers.Type
open import Naturals.Addition renaming (_+_ to _ℕ+_)

module Dyadics.Multiplication where

\end{code}

Instead of defining multiplication by pattern matching, we define it
by using the reducing function. This has efficiency implications, but
avoiding pattern matching helps to reduce the size of proofs.

We use an intermediate _*'_ relation (as in the approach with rationals).

\begin{code}

_*'_ : (p q : ℤ × ℕ) → ℤ × ℕ
(p , a) *' (q , b) = p ℤ* q , a ℕ+ b

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
      normalise-pos (p ℤ* q , a ℕ+ b) ＝⟨ ap (λ - → normalise-pos (- , a ℕ+ b)) (ℤ*-comm p q) ⟩
      normalise-pos (q ℤ* p , a ℕ+ b) ＝⟨ ap (λ - → normalise-pos (q ℤ* p , -)) (addition-commutativity a b) ⟩
      normalise-pos (q ℤ* p , b ℕ+ a) ＝⟨ refl ⟩
      ((q , b) , β) * ((p , a) , α)   ∎

\end{code}

Looking towards the associativity proof, we expect to need the proof
that multiplication respects the normalisation function on dyadic
rationals.

We will also need the prove associativity of the intermediate
multiplication operation.

\begin{code}

ℤ[1/2]*-normalise-pos : (p q : ℤ × ℕ) → normalise-pos (p *' q) ＝ normalise-pos p * normalise-pos q
ℤ[1/2]*-normalise-pos p q = {!!}
 where
  I : p ≈' {!!}
  I = {!!}

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
ℤ[1/2]*-assoc ((p , a) , α) ((q , b) , β) ((r , c) , δ) = γ
 where
  γ : ((p , a) , α) * ((q , b) , β) * ((r , c) , δ) ＝ ((p , a) , α) * (((q , b) , β) * ((r , c) , δ))
  γ = ((p , a) , α) * ((q , b) , β) * ((r , c) , δ)           ＝⟨ refl ⟩
      normalise-pos (p ℤ* q , a ℕ+ b) * ((r , c) , δ)         ＝⟨ ap (λ - → (normalise-pos (p ℤ* q , a ℕ+ b)) * -) (ℤ[1/2]-to-normalise-pos ((r , c) , δ)) ⟩
      normalise-pos (p ℤ* q , a ℕ+ b) * normalise-pos (r , c) ＝⟨ ℤ[1/2]*-normalise-pos (p ℤ* q , a ℕ+ b) (r , c) ⁻¹ ⟩
      normalise-pos ((p ℤ* q , a ℕ+ b) *' (r , c))            ＝⟨ ap normalise-pos (ℤ[1/2]*'-assoc (p , a) (q , b) (r , c)) ⟩ 
      normalise-pos ((p , a) *' (q ℤ* r , b ℕ+ c))            ＝⟨ ℤ[1/2]*-normalise-pos (p , a) (q ℤ* r , b ℕ+ c) ⟩
      normalise-pos (p , a) * normalise-pos (q ℤ* r , b ℕ+ c) ＝⟨ ap (_* normalise-pos (q ℤ* r , b ℕ+ c)) (ℤ[1/2]-to-normalise-pos ((p , a) , α) ⁻¹) ⟩
      ((p , a) , α) * normalise-pos (q ℤ* r , b ℕ+ c)         ＝⟨ refl ⟩
      ((p , a) , α) * (((q , b) , β) * ((r , c) , δ))         ∎

\end{code}

Martin Escardo, started 5th May 2018

\begin{code}

module NaturalsOrder where

open import SpartanMLTT hiding (_≤_) hiding (≤-anti) public

_≤_ : ℕ → ℕ → U₀ ̇
zero ≤ n        = 𝟙
succ m ≤ zero   = 𝟘
succ m ≤ succ n = m ≤ n

zero-minimal : (n : ℕ) → zero ≤ n
zero-minimal n = *

succ-monotone : (m n : ℕ) → m ≤ n → succ m ≤ succ n
succ-monotone m n l = l

succ-order-injective : (m n : ℕ) → succ m ≤ succ n → m ≤ n 
succ-order-injective m n l = l

succ≤≡ : (m n : ℕ) → (succ m ≤ succ n) ≡ (m ≤ n)
succ≤≡ m n = refl

≤-induction : {U : Universe} (P : (m n : ℕ) (l : m ≤ n) → U ̇)
            → ((n : ℕ) → P zero n (zero-minimal n))
            → ((m n : ℕ) (l : m ≤ n) → P m n l → P (succ m) (succ n) (succ-monotone m n l)) 
            → (m n : ℕ) (l : m ≤ n) → P m n l 
≤-induction P base step zero n *            = base n
≤-induction P base step (succ m) zero ()
≤-induction P base step (succ m) (succ n) l = step m n l (≤-induction P base step m n l)

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero     = *
≤-refl (succ n) = ≤-refl n

≤-trans : (l m n : ℕ) → l ≤ m → m ≤ n → l ≤ n
≤-trans zero m n p q = *
≤-trans (succ l) zero n () q
≤-trans (succ l) (succ m) zero p ()
≤-trans (succ l) (succ m) (succ n) p q = ≤-trans l m n p q

≤-anti : (m n : ℕ) → m ≤ n → n ≤ m → m ≡ n
≤-anti zero zero p q = refl
≤-anti zero (succ n) p ()
≤-anti (succ m) zero () q
≤-anti (succ m) (succ n) p q = ap succ (≤-anti m n p q)

≤-succ : (n : ℕ) → n ≤ succ n
≤-succ zero     = *
≤-succ (succ n) = ≤-succ n

unique-minimal : (n : ℕ) → n ≤ zero → n ≡ zero
unique-minimal zero l = refl
unique-minimal (succ n) ()

≤-split : (m n : ℕ) → m ≤ succ n → (m ≤ n) + (m ≡ succ n)
≤-split zero n l = inl l
≤-split (succ m) zero l = inr (ap succ (unique-minimal m l))
≤-split (succ m) (succ n) l = cases inl (inr ∘ (ap succ)) (≤-split m n l)

≤-join : (m n : ℕ) → (m ≤ n) + (m ≡ succ n) → m ≤ succ n
≤-join m n (inl l) = ≤-trans m n (succ n) l (≤-succ n)
≤-join .(succ n) n (inr refl) = ≤-refl n

_<_ : ℕ → ℕ → U₀ ̇
m < n = succ m ≤ n

not-less-bigger-or-equal : (m n : ℕ) → ¬(n < m) → m ≤ n
not-less-bigger-or-equal zero n u = zero-minimal n
not-less-bigger-or-equal (succ m) zero = double-negation-intro (zero-minimal m)
not-less-bigger-or-equal (succ m) (succ n) = not-less-bigger-or-equal m n

\end{code}

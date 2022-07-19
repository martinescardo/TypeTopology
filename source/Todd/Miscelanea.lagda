
\begin{code}

module Miscelanea where

\end{code}

zero-base : (a : ℕ) → a ℕ^ 0 ≡ 1
zero-base a = refl

prod-of-powers : (n a b : ℕ) → n ℕ^ a * n ℕ^ b ≡ n ℕ^ (a + b)
prod-of-powers n a zero     = refl
prod-of-powers n a (succ b) = I
 where
  I : n ℕ^ a * n ℕ^ succ b ≡ n ℕ^ (a + succ b)
  I = n ℕ^ a * n ℕ^ succ b  ≡⟨ refl ⟩
      n ℕ^ a * (n * n ℕ^ b) ≡⟨ mult-associativity (n ℕ^ a) n (n ℕ^ b) ⁻¹ ⟩
      n ℕ^ a * n * n ℕ^ b   ≡⟨ ap (_* n ℕ^ b) (mult-commutativity (n ℕ^ a) n) ⟩
      n * n ℕ^ a * n ℕ^ b   ≡⟨ mult-associativity n (n ℕ^ a) (n ℕ^ b) ⟩
      n * (n ℕ^ a * n ℕ^ b) ≡⟨ ap (n *_) (prod-of-powers n a b) ⟩
      n * n ℕ^ (a + b)      ≡⟨ refl ⟩
      n ℕ^ succ (a + b)     ≡⟨ refl ⟩
      n ℕ^ (a + succ b) ∎

raise-again : (n a b : ℕ) → (n ℕ^ a) ℕ^ b ≡ n ℕ^ (a * b)
raise-again n a zero     = refl
raise-again n a (succ b) = I
 where
  IH : n ℕ^ a ℕ^ b ≡ n ℕ^ (a * b)
  IH = raise-again n a b
  
  I : n ℕ^ a ℕ^ succ b ≡ n ℕ^ (a * succ b)
  I = n ℕ^ a ℕ^ succ b       ≡⟨ refl ⟩
      n ℕ^ a * (n ℕ^ a) ℕ^ b ≡⟨ ap (n ℕ^ a *_) IH ⟩
      n ℕ^ a * n ℕ^ (a * b)  ≡⟨ prod-of-powers n a (a * b) ⟩
      n ℕ^ (a + a * b)       ≡⟨ refl ⟩
      n ℕ^ (a * succ b)      ∎

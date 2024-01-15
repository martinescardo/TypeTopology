Martin Escardo, 2nd December 2019

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Fin.Variation where

open import UF.Subsingletons

open import Fin.Type
open import MLTT.Spartan
open import Naturals.Order
open import Notation.Order
open import UF.Equiv

\end{code}

An isomorphic copy of the type Fin n:

\begin{code}

Fin' : ℕ → 𝓤₀ ̇
Fin' n = Σ k ꞉ ℕ , k < n

𝟎' : {n : ℕ} → Fin' (succ n)
𝟎' {n} = 0 , zero-least n

suc' : {n : ℕ} → Fin' n → Fin' (succ n)
suc' (k , l) = succ k , l

Fin-unprime : (n : ℕ) → Fin' n → Fin n
Fin-unprime 0        (k , l)      = 𝟘-elim l
Fin-unprime (succ n) (0 , l)      = 𝟎
Fin-unprime (succ n) (succ k , l) = suc (Fin-unprime n (k , l))

Fin-prime : (n : ℕ) → Fin n → Fin' n
Fin-prime 0        i       = 𝟘-elim i
Fin-prime (succ n) (suc i) = suc' (Fin-prime n i)
Fin-prime (succ n) 𝟎       = 𝟎'

ηFin : (n : ℕ) → Fin-prime n ∘ Fin-unprime n ∼ id
ηFin 0        (k , l)      = 𝟘-elim l
ηFin (succ n) (0 , *)      = refl
ηFin (succ n) (succ k , l) = ap suc' (ηFin n (k , l))


εFin : (n : ℕ) → Fin-unprime n ∘ Fin-prime n ∼ id
εFin 0        i       = 𝟘-elim i
εFin (succ n) (suc i) = ap suc (εFin n i)
εFin (succ n) 𝟎       = refl

Fin-prime-is-equiv : (n : ℕ) → is-equiv (Fin-prime n)
Fin-prime-is-equiv n = qinvs-are-equivs (Fin-prime n)
                        (Fin-unprime n , εFin n , ηFin n)


≃-Fin : (n : ℕ) → Fin n ≃ Fin' n
≃-Fin n = Fin-prime n , Fin-prime-is-equiv n

\end{code}

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Vector where

open import MLTT.Spartan
open import MLTT.Fin
open import MLTT.Bool

data Vector (A : 𝓤 ̇ ) : ℕ → 𝓤 ̇ where
 []  : Vector A 0
 _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

head : {A : 𝓤 ̇ } {n : ℕ} → Vector A (succ n) → A
head (x ∷ xs) = x

tail : {A : 𝓤 ̇ } {n : ℕ} → Vector A (succ n) → Vector A n
tail (x ∷ xs) = xs

_!!_ : {X : 𝓤 ̇ } {n : ℕ} → Vector X n → Fin n → X
(x ∷ xs) !! 𝟎     = x
(x ∷ xs) !! suc n = xs !! n

vmap : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
    → (X → Y)
    → {n : ℕ} → Vector X n → Vector Y n
vmap f []       = []
vmap f (x ∷ xs) = f x ∷ vmap f xs


module vector-util
        {𝓤 : Universe}
        {X : 𝓤 ̇ }
        {{_ : Eq X}}
       where

  data _is-in_ : X → {n : ℕ} → Vector X n → 𝓤 ̇ where
   in-head : {x : X}   {n : ℕ} {xs : Vector X n} → x is-in (x ∷ xs)
   in-tail : {x y : X} {n : ℕ} {xs : Vector X n} → x is-in xs → x is-in (y ∷ xs)

  insert : X → {n : ℕ} → Vector X n → Vector X (succ n)
  insert x xs = x ∷ xs

  remove : (x : X) {n : ℕ}
           (xs : Vector X (succ n))
         → x is-in xs
         → Vector X n
  remove x {0}      (_ ∷ []) in-head     = []
  remove x {succ n} (_ ∷ xs) in-head     = xs
  remove x {succ n} (y ∷ xs) (in-tail p) = y ∷ remove x {n} xs p

  has-no-repetitions : {n : ℕ} → Vector X n → 𝓤 ̇
  has-no-repetitions []       = 𝟙
  has-no-repetitions (x ∷ xs) = ¬ (x is-in xs) × has-no-repetitions xs

\end{code}

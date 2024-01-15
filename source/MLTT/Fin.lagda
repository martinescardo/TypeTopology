\begin{code}

{-# OPTIONS --safe --without-K #-} --

module MLTT.Fin where

open import MLTT.Spartan
open import MLTT.List
open import MLTT.Bool
open import Naturals.Properties


data Fin : ℕ → 𝓤₀ ̇  where
 𝟎   : {n : ℕ} → Fin (succ n)
 suc : {n : ℕ} → Fin n → Fin (succ n)

ℕ-to-Fin : (n : ℕ) → Fin (succ n)
ℕ-to-Fin 0        = 𝟎
ℕ-to-Fin (succ n) = suc (ℕ-to-Fin n)

pattern 𝟏 = suc 𝟎
pattern 𝟐 = suc 𝟏
pattern 𝟑 = suc 𝟐
pattern 𝟒 = suc 𝟑
pattern 𝟓 = suc 𝟒
pattern 𝟔 = suc 𝟓
pattern 𝟕 = suc 𝟔
pattern 𝟖 = suc 𝟕
pattern 𝟗 = suc 𝟖

list-Fin : (n : ℕ) → List (Fin n)
list-Fin 0        = []
list-Fin (succ n) = 𝟎 ∷ map suc (list-Fin n)

list-Fin-correct : (n : ℕ) (i : Fin n) → member i (list-Fin n)
list-Fin-correct (succ n) 𝟎       = in-head
list-Fin-correct (succ n) (suc i) = in-tail g
 where
  IH : member i (list-Fin n)
  IH = list-Fin-correct n i

  g : member (suc i) (map suc (list-Fin n))
  g = member-map suc i (list-Fin n) IH

Fin-listed : (n : ℕ) → listed (Fin n)
Fin-listed n = list-Fin n , list-Fin-correct n

Fin-listed⁺ : (n : ℕ) → listed⁺ (Fin (succ n))
Fin-listed⁺ n = 𝟎 , Fin-listed (succ n)

Fin-== : {n : ℕ} → Fin n → Fin n → Bool
Fin-== {succ n} (suc x) (suc y) = Fin-== {n} x y
Fin-== {succ n} (suc x) 𝟎       = false
Fin-== {succ n} 𝟎       (suc y) = false
Fin-== {succ n} 𝟎       𝟎       = true

Fin-refl : {n : ℕ} (x : Fin n) → (Fin-== x x) ＝ true
Fin-refl {succ n} (suc x) = Fin-refl {n} x
Fin-refl {succ n} 𝟎       = refl

module _ {n : ℕ} where
 instance
  eqFin : Eq (Fin n)
  _==_    {{eqFin}} = Fin-== {n}
  ==-refl {{eqFin}} = Fin-refl {n}

\end{code}

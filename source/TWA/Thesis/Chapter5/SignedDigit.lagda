Todd Waugh Ambridge, January 2024

# Ternary signed-digit encodings

\begin{code}
{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import Fin.Type
open import Fin.Bishop
open import UF.Sets

open import TWA.Thesis.Chapter2.Finite
open import TWA.Thesis.Chapter2.Sequences

module TWA.Thesis.Chapter5.SignedDigit where
\end{code}

## Definition

\begin{code}
data 𝟛 : 𝓤₀ ̇ where
  −1 O +1 : 𝟛

𝟛-is-finite : finite-linear-order 𝟛
𝟛-is-finite = 3 , qinveq g (h , η , μ)
 where
  g : 𝟛 → Fin 3
  g −1 = 𝟎
  g  O = 𝟏
  g +1 = 𝟐
  h : Fin 3 → 𝟛
  h 𝟎 = −1
  h 𝟏 =  O
  h 𝟐 = +1
  η : h ∘ g ∼ id
  η −1 = refl
  η  O = refl
  η +1 = refl
  μ : g ∘ h ∼ id
  μ 𝟎 = refl
  μ 𝟏 = refl
  μ 𝟐 = refl
  
𝟛-is-discrete : is-discrete 𝟛
𝟛-is-discrete = finite-is-discrete 𝟛-is-finite

𝟛-is-set : is-set 𝟛
𝟛-is-set = finite-is-set 𝟛-is-finite

𝟛ᴺ : 𝓤₀ ̇ 
𝟛ᴺ = ℕ → 𝟛
\end{code}

## Negation

\begin{code}
flip : 𝟛 → 𝟛
flip −1 = +1
flip  O =  O
flip +1 = −1

neg : 𝟛ᴺ → 𝟛ᴺ
neg = map flip
\end{code}

## Binary midpoint

\begin{code}
data 𝟝 : 𝓤₀ ̇ where
  −2 −1 O +1 +2 : 𝟝

𝟝ᴺ : 𝓤₀ ̇
𝟝ᴺ = ℕ → 𝟝

_+𝟛_ : 𝟛 → 𝟛 → 𝟝
(−1 +𝟛 −1) = −2
(−1 +𝟛  O) = −1
(−1 +𝟛 +1) =  O
( O +𝟛 −1) = −1
( O +𝟛  O) =  O
( O +𝟛 +1) = +1
(+1 +𝟛 −1) =  O
(+1 +𝟛  O) = +1
(+1 +𝟛 +1) = +2

add2 : 𝟛ᴺ → 𝟛ᴺ → 𝟝ᴺ
add2 = zipWith _+𝟛_

div2-aux : 𝟝 → 𝟝 → 𝟛 × 𝟝
div2-aux −2  b = −1 ,  b
div2-aux  O  b =  O ,  b
div2-aux +2  b = +1 ,  b
div2-aux −1 −2 = −1 ,  O
div2-aux −1 −1 = −1 , +1
div2-aux −1  O =  O , −2
div2-aux −1 +1 =  O , −1
div2-aux −1 +2 =  O ,  O
div2-aux +1 −2 =  O ,  O
div2-aux +1 −1 =  O , +1
div2-aux +1  O =  O , +2
div2-aux +1 +1 = +1 , −1
div2-aux +1 +2 = +1 ,  O

div2 : 𝟝ᴺ → 𝟛ᴺ
div2 α 0 = a
 where
  a = pr₁ (div2-aux (α 0) (α 1))
div2 α (succ n) = div2 (b ∷ x) n
 where
  b = pr₂ (div2-aux (α 0) (α 1))
  x = tail (tail α)

mid : 𝟛ᴺ → 𝟛ᴺ → 𝟛ᴺ
mid α β = div2 (add2 α β)
\end{code}

## Infinitary midpoint

\begin{code}
data 𝟡 : 𝓤₀ ̇ where
  −4 −3 −2 −1 O +1 +2 +3 +4 : 𝟡

𝟡ᴺ : 𝓤₀ ̇ 
𝟡ᴺ = ℕ → 𝟡

_+𝟝_ : 𝟝 → 𝟝 → 𝟡
(−2 +𝟝 −2) = −4
(−2 +𝟝 −1) = −3
(−2 +𝟝  O) = −2
(−2 +𝟝 +1) = −1
(−2 +𝟝 +2) = O
(−1 +𝟝 −2) = −3
(−1 +𝟝 −1) = −2
(−1 +𝟝  O) = −1
(−1 +𝟝 +1) = O
(−1 +𝟝 +2) = +1
( O +𝟝 −2) = −2
( O +𝟝 −1) = −1
( O +𝟝  O) = O
( O +𝟝 +1) = +1
( O +𝟝 +2) = +2
(+1 +𝟝 −2) = −1
(+1 +𝟝 −1) = O
(+1 +𝟝  O) = +1
(+1 +𝟝 +1) = +2
(+1 +𝟝 +2) = +3
(+2 +𝟝 −2) = O
(+2 +𝟝 −1) = +1
(+2 +𝟝  O) = +2
(+2 +𝟝 +1) = +3
(+2 +𝟝 +2) = +4

div4-aux : 𝟡 → 𝟡 → 𝟛 × 𝟡
div4-aux −4    = −1 ,_
div4-aux  O    =  O ,_
div4-aux +4    = +1 ,_
div4-aux −3 −4 = −1 , −2
div4-aux −3 −3 = −1 , −1
div4-aux −3 −2 = −1 ,  O
div4-aux −3 −1 = −1 , +1
div4-aux −3  O = −1 , +2
div4-aux −3 +1 = −1 , +3
div4-aux −3 +2 =  O , −4
div4-aux −3 +3 =  O , −3
div4-aux −3 +4 =  O , −2
div4-aux −2 −4 = −1 ,  O
div4-aux −2 −3 = −1 , +1
div4-aux −2 −2 = −1 , +2
div4-aux −2 −1 = −1 , +3
div4-aux −2  O =  O , −4
div4-aux −2 +1 =  O , −3
div4-aux −2 +2 =  O , −2
div4-aux −2 +3 =  O , −1
div4-aux −2 +4 =  O ,  O
div4-aux −1 −4 = −1 , +2
div4-aux −1 −3 = −1 , +3
div4-aux −1 −2 =  O , −4
div4-aux −1 −1 =  O , −3
div4-aux −1  O =  O , −2
div4-aux −1 +1 =  O , −1
div4-aux −1 +2 =  O , O
div4-aux −1 +3 =  O , +1
div4-aux −1 +4 =  O , +2
div4-aux +1 −4 =  O , −2
div4-aux +1 −3 =  O , −1 
div4-aux +1 −2 =  O ,  O
div4-aux +1 −1 =  O , +1
div4-aux +1  O =  O , +2
div4-aux +1 +1 =  O , +3
div4-aux +1 +2 =  O , +4
div4-aux +1 +3 = +1 , −3
div4-aux +1 +4 = +1 , −2
div4-aux +2 −4 =  O ,  O
div4-aux +2 −3 =  O , +1
div4-aux +2 −2 =  O , +2
div4-aux +2 −1 =  O , +3
div4-aux +2  O =  O , +4
div4-aux +2 +1 = +1 , −3
div4-aux +2 +2 = +1 , −2
div4-aux +2 +3 = +1 , −1
div4-aux +2 +4 = +1 ,  O
div4-aux +3 −4 =  O , +2
div4-aux +3 −3 =  O , +3
div4-aux +3 −2 =  O , +4
div4-aux +3 −1 = +1 , −3
div4-aux +3  O = +1 , −2
div4-aux +3 +1 = +1 , −1
div4-aux +3 +2 = +1  , O
div4-aux +3 +3 = +1 , +1
div4-aux +3 +4 = +1 , +2

div4 : 𝟡ᴺ → 𝟛ᴺ
div4 α 0 = a
 where
  a = pr₁ (div4-aux (α 0) (α 1))
div4 α (succ n) = div4 (b ∷ x) n
 where
  b = pr₂ (div4-aux (α 0) (α 1))
  x = tail (tail α)

bigMid' : (ℕ → 𝟛ᴺ) → 𝟡ᴺ
bigMid' zs 0 = (x 0 +𝟛 x 0) +𝟝 (x 1 +𝟛 y 0)
 where x  = zs 0
       y  = zs 1
bigMid' zs (succ n) = bigMid' (mid (tail (tail x)) (tail y) ∷ tail (tail zs)) n
 where x = zs 0
       y = zs 1

bigMid : (ℕ → 𝟛ᴺ) → 𝟛ᴺ
bigMid = div4 ∘ bigMid'
\end{code}

## Multiplication

\begin{code}
_*𝟛_ : 𝟛 → 𝟛 → 𝟛
(−1 *𝟛 x) = flip x
( O *𝟛 x) = O
(+1 *𝟛 x) = x

digitMul : 𝟛 → 𝟛ᴺ → 𝟛ᴺ
digitMul a = map (a *𝟛_)

mul : 𝟛ᴺ → 𝟛ᴺ → 𝟛ᴺ
mul x y = bigMid (zipWith digitMul x (repeat y))
\end{code}

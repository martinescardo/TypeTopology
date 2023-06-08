\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Thesis.Chapter5.SignedDigit where

open import MLTT.Spartan
open import TypeTopology.DiscreteAndSeparated
open import Thesis.Chapter5.Prelude

data 𝟛 : 𝓤₀ ̇ where
  −1 O +1 : 𝟛

𝟛-is-discrete : is-discrete 𝟛
𝟛-is-discrete −1 −1 = inl refl
𝟛-is-discrete −1  O = inr (λ ())
𝟛-is-discrete −1 +1 = inr (λ ())
𝟛-is-discrete  O −1 = inr (λ ())
𝟛-is-discrete  O  O = inl refl
𝟛-is-discrete  O +1 = inr (λ ())
𝟛-is-discrete +1 −1 = inr (λ ())
𝟛-is-discrete +1  O = inr (λ ())
𝟛-is-discrete +1 +1 = inl refl

𝟛ᴺ = ℕ → 𝟛

compl : 𝟛 → 𝟛
compl −1 = +1
compl  O =  O
compl +1 = −1

neg : 𝟛ᴺ → 𝟛ᴺ
neg = map compl

data 𝟝 : 𝓤₀ ̇ where
  −2 −1 O +1 +2 : 𝟝

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
add2 = map2 _+𝟛_

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
div2 α (succ n) = div2 (b ∶∶ x) n
 where
  b = pr₂ (div2-aux (α 0) (α 1))
  x = tail (tail α)

mid : 𝟛ᴺ → 𝟛ᴺ → 𝟛ᴺ
mid α β = div2 (add2 α β)

_*𝟛_ : 𝟛 → 𝟛 → 𝟛
(−1 *𝟛 x) = compl x
( O *𝟛 x) = O
(+1 *𝟛 x) = x

digitMul : 𝟛 → 𝟛ᴺ → 𝟛ᴺ
digitMul a = map (a *𝟛_)

data 𝟡 : 𝓤₀ ̇ where
  −4 −3 −2 −1 O +1 +2 +3 +4 : 𝟡

𝟡ᴺ = ℕ → 𝟡

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
div4 α (succ n) = div4 (b ∶∶ x) n
 where
  b = pr₂ (div4-aux (α 0) (α 1))
  x = tail (tail α)

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

bigMid' : (ℕ → 𝟛ᴺ) → 𝟡ᴺ
bigMid' zs 0 = (x 0 +𝟛 x 0) +𝟝 (x 1 +𝟛 y 0)
 where x  = zs 0
       y  = zs 1
bigMid' zs (succ n) = bigMid' (mid (tail (tail x)) (tail y) ∶∶ tail (tail zs)) n
 where x = zs 0
       y = zs 1

bigMid : (ℕ → 𝟛ᴺ) → 𝟛ᴺ
bigMid = div4 ∘ bigMid'

repeat : {X : 𝓤 ̇ } → X → ℕ → X
repeat α _ = α

mul : 𝟛ᴺ → 𝟛ᴺ → 𝟛ᴺ
mul x y = bigMid (map2 digitMul x (repeat y))

\end{code}

znorm : 𝟛ᴺ → 𝟛ᴺ

znorm' : 𝟛 → 𝟛 → 𝟛ᴺ → 𝟛ᴺ
znorm' O b α zero = O
znorm' O b α (succ n) = znorm' b (head α) (tail α) n
znorm' −1 +1 α zero = O
znorm' −1 +1 α (succ n) = znorm' −1 (head α) (tail α) n
znorm' +1 −1 α zero = O
znorm' +1 −1 α (succ n) = znorm' +1 (head α) (tail α) n
znorm' −1 −1 α = −1 ∶∶ (−1 ∶∶ α)
znorm' −1  O α = −1 ∶∶ ( O ∶∶ α)
znorm' +1  O α = +1 ∶∶ ( O ∶∶ α)
znorm' +1 +1 α = +1 ∶∶ (+1 ∶∶ α)

znorm α = znorm' (head α) (head (tail α)) (tail (tail α))

_−ℕ_ : ℕ → ℕ → ℕ
0 −ℕ _ = 0
succ a −ℕ 0 = succ a
succ a −ℕ succ b = a −ℕ b

negative' : 𝟛 → 𝟛ᴺ → ℕ → ℕ → 𝓤₀ ̇
negative' −1 _ _ _ = 𝟙
negative' +1 _ _ _ = 𝟘
negative'  O _ 0 _ = 𝟘
negative'  O α (succ k) n = negative' (α (n −ℕ succ k)) α k n

negative : 𝟛ᴺ → ℕ → 𝓤₀ ̇
negative α n = negative' (head (znorm α)) (znorm α) n n

smaller : ℕ → 𝟛ᴺ → 𝟛ᴺ → 𝓤₀ ̇
smaller n α β = negative (mid α (neg β)) (succ n)

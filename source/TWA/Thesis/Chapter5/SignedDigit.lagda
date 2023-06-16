\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import TypeTopology.DiscreteAndSeparated
open import UF.Equiv

open import TWA.Thesis.Chapter2.FiniteDiscrete
open import TWA.Thesis.Chapter2.Sequences

module TWA.Thesis.Chapter5.SignedDigit where

-- Definition 5.2.5
data 𝟛 : 𝓤₀ ̇ where
  −1 O +1 : 𝟛

𝟛-finite : finite-discrete 𝟛
pr₁ 𝟛-finite = 3
pr₂ 𝟛-finite = qinveq g (h , η , μ)
 where
  g : 𝔽 3 → 𝟛
  g (inl ⋆)             = −1
  g (inr (inl ⋆))       =  O
  g (inr (inr (inl ⋆))) = +1
  h : 𝟛 → 𝔽 3
  h −1 = inl ⋆
  h  O = inr (inl ⋆)
  h +1 = inr (inr (inl ⋆))
  η : (λ x → h (g x)) ∼ (λ x → x)
  η (inl ⋆)             = refl
  η (inr (inl ⋆))       = refl
  η (inr (inr (inl ⋆))) = refl
  μ : (λ x → g (h x)) ∼ (λ x → x)
  μ −1 = refl
  μ  O = refl
  μ +1 = refl

𝟛-is-discrete : is-discrete 𝟛
𝟛-is-discrete = finite-discrete-is-discrete 𝟛-finite

-- Definition 5.2.6
𝟛ᴺ : 𝓤₀ ̇ 
𝟛ᴺ = ℕ → 𝟛

-- Definition 5.2.11
flip : 𝟛 → 𝟛
flip −1 = +1
flip  O =  O
flip +1 = −1

neg : 𝟛ᴺ → 𝟛ᴺ
neg = map flip

-- Definition 5.2.14
data 𝟝 : 𝓤₀ ̇ where
  −2 −1 O +1 +2 : 𝟝

𝟝ᴺ : 𝓤₀ ̇
𝟝ᴺ = ℕ → 𝟝

-- Definition 5.2.15
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

-- Definition 5.2.16
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

-- Definition 5.2.17
mid : 𝟛ᴺ → 𝟛ᴺ → 𝟛ᴺ
mid α β = div2 (add2 α β)

-- Definition 5.2.23
data 𝟡 : 𝓤₀ ̇ where
  −4 −3 −2 −1 O +1 +2 +3 +4 : 𝟡

𝟡ᴺ : 𝓤₀ ̇ 
𝟡ᴺ = ℕ → 𝟡

-- Definition 5.2.24
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

-- Definition 5.2.25
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

-- Definition 5.2.28
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

-- Definition 5.2.34
_*𝟛_ : 𝟛 → 𝟛 → 𝟛
(−1 *𝟛 x) = flip x
( O *𝟛 x) = O
(+1 *𝟛 x) = x

digitMul : 𝟛 → 𝟛ᴺ → 𝟛ᴺ
digitMul a = map (a *𝟛_)

-- Definition 5.2.35
mul : 𝟛ᴺ → 𝟛ᴺ → 𝟛ᴺ
mul x y = bigMid (zipWith digitMul x (repeat y))

\end{code}

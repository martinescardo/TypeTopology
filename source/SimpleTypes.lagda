Martin Escardo, January 2018

The simple types are the smallest collection of types containing ℕ and
closed under exponentials (function types).  All simple types are
totally separated and retracts of 𝟚. This is used to show that no
simple type is 𝟚-compact, unless WLPO holds. If 𝟚 is included as a
base simple type, then for (X → Y) to be compact it is necessary that
X is discrete and Y is compact. (It is consistent that the converse
holds (Tychonoff Theorem).)

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt
open import UF-PropTrunc

module SimpleTypes (fe : ∀ U V → FunExt U V) (pt : PropTrunc) where

open import UF-Retracts
open import UF-Retracts-FunExt

data simple-type : U₀ ̇ → U₁ ̇ where
 base : simple-type ℕ
 step : {X Y : U₀ ̇} → simple-type X → simple-type Y → simple-type (X → Y)

open import TotallySeparated
open import 2CompactTypes (fe) (pt)
open import DiscreteAndSeparated

𝟚-retract-of-ℕ : retract 𝟚 of ℕ
𝟚-retract-of-ℕ = (r , (s , rs))
 where
  r : ℕ → 𝟚
  r zero = ₀
  r (succ n) = ₁
  
  s : 𝟚 → ℕ
  s ₀ = zero
  s ₁ = succ zero
  
  rs : (n : 𝟚) → r (s n) ≡ n
  rs ₀ = refl
  rs ₁ = refl

ℕ-totally-separated : totally-separated ℕ
ℕ-totally-separated = discrete-totally-separated (ℕ-discrete)

simple-types-totally-separated : {X : U₀ ̇} → simple-type X → totally-separated X
simple-types-totally-separated base       = ℕ-totally-separated
simple-types-totally-separated (step s t) = totally-separated-ideal (fe U₀ U₀)
                                              λ _ → simple-types-totally-separated t

simple-types-pointed : {X : U₀ ̇} → simple-type X → X
simple-types-pointed base       = zero
simple-types-pointed (step s t) = λ x → simple-types-pointed t

simple-types-r : {X A : U₀ ̇} → retract A of ℕ → simple-type X → retract A of X
simple-types-r rn base       = rn
simple-types-r rn (step s t) = retracts-of-closed-under-exponentials
                                 (fe U₀ U₀)
                                 (simple-types-pointed s)
                                 (simple-types-r rn s)
                                 (simple-types-r rn t)

cfdbce : {X Y : U₀ ̇} → simple-type X → simple-type Y
       → 𝟚-compact (X → Y) → discrete X × 𝟚-compact Y
cfdbce s t c = (tscd₀ (simple-types-totally-separated s) (simple-types-r 𝟚-retract-of-ℕ t) c ,
               i2c2c (simple-types-pointed s) c)

\end{code}

TODO: prove that WLPO' is equivalent to WLPO. But notice that WLPO' is
the original formalution of WLPO by Bishop (written in type theory).

\begin{code}

WLPO' : U₀ ̇
WLPO' = 𝟚-compact ℕ

stcwlpo : {X : U₀ ̇} → simple-type X → 𝟚-compact X → WLPO'
stcwlpo base c = c
stcwlpo (step s t) c = stcwlpo t (pr₂ (cfdbce s t c))

\end{code}

But, of course, the last consequence can be proved more directly by
simply showing that ℕ is a retract of every simple type, using the
fact that 𝟚-compactness is inherited by retracts, which doesn't rely
on the notion of total separatedness:

\begin{code}

simple-types-rℕ : {X : U₀ ̇} → simple-type X → retract ℕ of X
simple-types-rℕ = simple-types-r identity-retraction

stcwlpo' : {X : U₀ ̇} → simple-type X → 𝟚-compact X → WLPO'
stcwlpo' s = retract-𝟚-compact (simple-types-rℕ s)

\end{code}

To make this less trivial, we include 𝟚 as a base type in the
definition of simple types:

\begin{code}

data simple-type₂ : U₀ ̇ → U₁ ̇ where
 base₂ : simple-type₂ 𝟚
 base : simple-type₂ ℕ
 step : {X Y : U₀ ̇} → simple-type₂ X → simple-type₂ Y → simple-type₂ (X → Y)

\end{code}

Then now, potentially, there are compact types such as the Cantor
space (ℕ → 𝟚), and more generally (X → Y) with X discrete and Y
compact, if Tychonoff holds (which is consistent but not
provable). The following then says that this is the only possibility:
If X and Y simple types in this generalized sense, for (X → Y) to be
compact, it is necessary that X is discrete and Y is compact.

\begin{code}

simple-types₂-totally-separated : {X : U₀ ̇} → simple-type₂ X → totally-separated X
simple-types₂-totally-separated base₂       = 𝟚-totally-separated
simple-types₂-totally-separated base        = ℕ-totally-separated
simple-types₂-totally-separated (step s t)  = totally-separated-ideal (fe U₀ U₀)
                                               λ _ → simple-types₂-totally-separated t

simple-types₂-pointed : {X : U₀ ̇} → simple-type₂ X → X
simple-types₂-pointed base₂      = ₀
simple-types₂-pointed base       = zero
simple-types₂-pointed (step s t) = λ x → simple-types₂-pointed t

simple-types₂-r𝟚 : {X : U₀ ̇} → simple-type₂ X → retract 𝟚 of X
simple-types₂-r𝟚 base₂      = identity-retraction
simple-types₂-r𝟚 base       = 𝟚-retract-of-ℕ
simple-types₂-r𝟚 (step s t) = retracts-of-closed-under-exponentials
                                 (fe U₀ U₀)
                                 (simple-types₂-pointed s)
                                 (simple-types₂-r𝟚 s)
                                 (simple-types₂-r𝟚 t)

cfdbce₂ : {X Y : U₀ ̇} → simple-type₂ X → simple-type₂ Y
       → 𝟚-compact (X → Y) → discrete X × 𝟚-compact Y
cfdbce₂ s t c = (tscd₀ (simple-types₂-totally-separated s) (simple-types₂-r𝟚 t) c ,
                 i2c2c (simple-types₂-pointed s) c)

\end{code}

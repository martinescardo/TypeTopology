Martin Escardo, January 2018

The simple types are the smallest collection of types containing ℕ and
closed under exponentials (function types).  All simple types are
totally separated and retracts of 𝟚. This is used to show that no
simple type is 𝟚-compact, unless WLPO holds. If 𝟚 is included as a
base simple type, then for (X → Y) to be compact it is necessary that
X is discrete and Y is compact. (It is consistent that the converse
holds (Tychonoff Theorem).)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module TypeTopology.SimpleTypes
        (fe : FunExt)
        (pt : propositional-truncations-exist)
       where

open import TypeTopology.DisconnectedTypes
open import TypeTopology.TotallySeparated
open import TypeTopology.WeaklyCompactTypes fe pt
            renaming (is-Π-compact to is-compact)
open import UF.DiscreteAndSeparated
open import UF.Retracts
open import UF.Retracts-FunExt

data simple-type : 𝓤₀ ̇ → 𝓤₁ ̇ where
 base : simple-type ℕ
 step : {X Y : 𝓤₀ ̇ } → simple-type X → simple-type Y → simple-type (X → Y)


simple-types-are-totally-separated : {X : 𝓤₀ ̇ }
                                   → simple-type X
                                   → is-totally-separated X
simple-types-are-totally-separated base       = ℕ-is-totally-separated
simple-types-are-totally-separated (step s t) = Π-is-totally-separated (fe 𝓤₀ 𝓤₀)
                                                 λ _ → simple-types-are-totally-separated t

simple-types-pointed : {X : 𝓤₀ ̇ } → simple-type X → X
simple-types-pointed base       = zero
simple-types-pointed (step s t) = λ x → simple-types-pointed t

simple-types-r : {X A : 𝓤₀ ̇ } → retract A of ℕ → simple-type X → retract A of X
simple-types-r rn base       = rn
simple-types-r rn (step s t) = retracts-of-closed-under-exponentials
                                 (fe 𝓤₀ 𝓤₀)
                                 (simple-types-pointed s)
                                 (simple-types-r rn s)
                                 (simple-types-r rn t)

cfdbce : {X Y : 𝓤₀ ̇ }
       → simple-type X
       → simple-type Y
       → is-compact (X → Y)
       → is-discrete X × is-compact Y
cfdbce s t c = tscd₀
                (simple-types-are-totally-separated s)
                (simple-types-r ℕ-is-disconnected t) c ,
                 Π-compact-exponential-with-pointed-domain-has-Π-compact-codomain
                (simple-types-pointed s) c
\end{code}

TODO: prove that WLPO' is equivalent to WLPO. But notice that WLPO' is
the original formulation of WLPO by Bishop (written in type theory).

We have that simple types are "not" compact:

\begin{code}

WLPO' : 𝓤₀ ̇
WLPO' = is-compact ℕ

stcwlpo : {X : 𝓤₀ ̇ } → simple-type X → is-compact X → WLPO'
stcwlpo base c = c
stcwlpo (step s t) c = stcwlpo t (pr₂ (cfdbce s t c))

\end{code}

But, of course, the last consequence can be proved more directly by
simply showing that ℕ is a retract of every simple type, using the
fact that compactness is inherited by retracts, which doesn't rely
on the notion of total separatedness:

\begin{code}

ℕ-is-retract-of-any-simple-type : {X : 𝓤₀ ̇ } → simple-type X → retract ℕ of X
ℕ-is-retract-of-any-simple-type = simple-types-r identity-retraction

stcwlpo' : {X : 𝓤₀ ̇ } → simple-type X → is-compact X → WLPO'
stcwlpo' s = retract-is-Π-compact (ℕ-is-retract-of-any-simple-type s)

\end{code}

To make this less trivial, we include 𝟚 as a base type in the
definition of simple types:

\begin{code}

data simple-type₂ : 𝓤₀ ̇ → 𝓤₁ ̇ where
 base₂ : simple-type₂ 𝟚
 base  : simple-type₂ ℕ
 step  : {X Y : 𝓤₀ ̇ } → simple-type₂ X → simple-type₂ Y → simple-type₂ (X → Y)

\end{code}

Then now, potentially, there are compact types such as the Cantor
space (ℕ → 𝟚), and more generally (X → Y) with X discrete and Y
compact, if Tychonoff holds (which is consistent but not
provable). The following then says that this is the only possibility:
If X and Y simple types in this generalized sense, for (X → Y) to be
compact, it is necessary that X is discrete and Y is compact.

\begin{code}

simple-types₂-totally-separated : {X : 𝓤₀ ̇ }
                                → simple-type₂ X
                                → is-totally-separated X
simple-types₂-totally-separated base₂       = 𝟚-is-totally-separated
simple-types₂-totally-separated base        = ℕ-is-totally-separated
simple-types₂-totally-separated (step s t)  =
 Π-is-totally-separated (fe 𝓤₀ 𝓤₀)
  (λ _ → simple-types₂-totally-separated t)

simple-types₂-pointed : {X : 𝓤₀ ̇ } → simple-type₂ X → X
simple-types₂-pointed base₂      = ₀
simple-types₂-pointed base       = zero
simple-types₂-pointed (step s t) = λ x → simple-types₂-pointed t

simple-types₂-disconnected : {X : 𝓤₀ ̇ } → simple-type₂ X → is-disconnected X
simple-types₂-disconnected base₂      = identity-retraction
simple-types₂-disconnected base       = ℕ-is-disconnected
simple-types₂-disconnected (step s t) = retracts-of-closed-under-exponentials
                                         (fe 𝓤₀ 𝓤₀)
                                         (simple-types₂-pointed s)
                                         (simple-types₂-disconnected s)
                                         (simple-types₂-disconnected t)

cfdbce₂ : {X Y : 𝓤₀ ̇ }
        → simple-type₂ X
        → simple-type₂ Y
        → is-compact (X → Y)
        → is-discrete X × is-compact Y
cfdbce₂ s t c =
 tscd₀
  (simple-types₂-totally-separated s)
  (simple-types₂-disconnected t) c ,
   Π-compact-exponential-with-pointed-domain-has-Π-compact-codomain
  (simple-types₂-pointed s)
  c

\end{code}

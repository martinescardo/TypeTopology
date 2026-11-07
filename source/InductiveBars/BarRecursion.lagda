Chuangjie Xu, November 2026

We construct a Spector bar recursor for each bar-continuous control functional.

Following the approach of Paulo Oliva and Silvia Steila in "A direct proof of
Schwichtenberg's bar recursion closure theorem" (2018, Theorem 2.4), we derive
Spector's bar recursion from general bar recursion.

Oliva and Steila construct a System T term for the recursor from a System T
term for the control. Here we construct an Agda term for the recursor from
a witness that the control is bar continuous.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import UF.FunExt using (Fun-Ext ; dfunext)

module InductiveBars.BarRecursion (fe : Fun-Ext) where

open import MLTT.Spartan
open import MLTT.List
open import Naturals.Order
open import UF.Base using (ap₂)
open import UF.Powerset
open import UF.Subsingletons using (is-prop)

open import InductiveBars.Sequences
open import InductiveBars.Basics
open import InductiveBars.Continuity fe

\end{code}

A witness of `V controls-recursion-at s` describes the possible recursive
calls starting at s. Along each branch, recursion stops at the first
extension of s that belongs to V.

\begin{code}

data _controls-recursion-at_ (V : 𝓟 (List ℕ)) : List ℕ → 𝓤₀ ̇ where
 stop     : {s : List ℕ}
          → s ∈ V
          → V controls-recursion-at s
 continue : {s : List ℕ}
          → s ∉ V
          → ((n : ℕ) → V controls-recursion-at (s ++ [ n ]))
          → V controls-recursion-at s

\end{code}

Any two witnesses of `V controls-recursion-at s` are equal. They must
either both stop or both continue.

\begin{code}

controls-recursion-at-is-prop
 : (V : 𝓟 (List ℕ)) (s : List ℕ) → is-prop (V controls-recursion-at s)
controls-recursion-at-is-prop V s (stop p) (stop q)
 = ap stop (∈-is-prop V s p q)
controls-recursion-at-is-prop V s (stop p) (continue q ψ)
 = 𝟘-elim (q p)
controls-recursion-at-is-prop V s (continue p φ) (stop q)
 = 𝟘-elim (p q)
controls-recursion-at-is-prop V s (continue p φ) (continue q ψ)
 = ap₂ continue (∉-is-prop fe V s p q) e
 where
  ih : (n : ℕ) → φ n ＝ ψ n
  ih n = controls-recursion-at-is-prop V (s ++ [ n ]) (φ n) (ψ n)
  e : φ ＝ ψ
  e = dfunext fe ih

\end{code}

For decidable V, if V bars s, then V controls recursion at s.

\begin{code}

bars-implies-controls-recursion-at
 : (V : 𝓟 (List ℕ)) → ((s : List ℕ) → is-decidable (s ∈ V))
 → (s : List ℕ) → V bars s → V controls-recursion-at s
bars-implies-controls-recursion-at V dec s (hit p) = stop p
bars-implies-controls-recursion-at V dec s (step φ) =
 cases stop (λ q → continue q ih) (dec s)
 where
  ih : (n : ℕ) → V controls-recursion-at (s ++ [ n ])
  ih n = bars-implies-controls-recursion-at V dec (s ++ [ n ]) (φ n)

\end{code}

We evaluate recursively on a witness of `V controls-recursion-at s`.
The following definition shows how the witness determines when to stop
and when to continue.

\begin{code}

eval : {X : 𝓤 ̇} {V : 𝓟 (List ℕ)}
     → (List ℕ → X) → (List ℕ → (ℕ → X) → X)
     → (s : List ℕ) → V controls-recursion-at s → X
eval G H s (stop _) = G s
eval G H s (continue _ φ) = H s (λ n → eval G H (s ++ [ n ]) (φ n))

\end{code}

If V controls recursion at every finite sequence, we can construct
a general bar recursor for V in the sense of Oliva and Steila, using
the above evaluation function.

\begin{code}

BarRecursor : 𝓤 ̇ → 𝓤 ̇
BarRecursor X = (List ℕ → X)
              → (List ℕ → (ℕ → X) → X)
              → List ℕ → X

gbr : {X : 𝓤 ̇} {B : 𝓟 (List ℕ)}
    → ((s : List ℕ) → B controls-recursion-at s)
    → BarRecursor X
gbr d G H s = eval G H s (d s)

general-bar-recursor-spec
 : {X : 𝓤 ̇} {B : 𝓟 (List ℕ)} (d : (s : List ℕ) → B controls-recursion-at s)
 → (G : List ℕ → X) (H : List ℕ → (ℕ → X) → X) (s : List ℕ)
 → (s ∈ B → gbr d G H s ＝ G s)
 × (s ∉ B → gbr d G H s ＝ H s (λ n → gbr d G H (s ++ [ n ])))
general-bar-recursor-spec {B = B} d G H s = base-case , step-case
 where
  unique : (e : B controls-recursion-at s) → gbr d G H s ＝ eval G H s e
  unique e = ap (eval G H s) (controls-recursion-at-is-prop B s (d s) e)
  base-case : s ∈ B → gbr d G H s ＝ G s
  base-case p = unique (stop p)
  step-case : s ∉ B → gbr d G H s ＝ H s (λ n → gbr d G H (s ++ [ n ]))
  step-case q = unique (continue q (λ n → d (s ++ [ n ])))

\end{code}

Now we switch to Spector's bar recursion.

Spector's recursion, controlled by a functional Y : (ℕ → ℕ) → ℕ, stops at
input s when Y (pad s) < length s. We call such an s a stopping prefix of Y.

\begin{code}

stopping-prefixes : ((ℕ → ℕ) → ℕ) → 𝓟 (List ℕ)
stopping-prefixes Y s
 = (Y (pad s) <ℕ length s) , <-is-prop-valued (Y (pad s)) (length s)

\end{code}

A bar of determining prefixes gives a bar of stopping prefixes.

This result is due to the fact that, once s determines Y, all extensions
of s by Y (pad s) + 1 entries satisfy the stopping condition.

\begin{code}

determining-prefix-gives-stopping-level
 : (Y : (ℕ → ℕ) → ℕ) (s : List ℕ)
 → s determines Y
 → (t : List ℕ) → length t ＝ succ (Y (pad s))
 → (s ++ t) ∈ stopping-prefixes Y
determining-prefix-gives-stopping-level Y s det t l
 = transport (_≤ℕ length u) e' r
 where
  u : List ℕ
  u = s ++ t
  e : Y (pad u) ＝ Y (pad s)
  e = det (pad u) (pad s)
          (extends-++ (pad u) s t (pad-extends u)) (pad-extends s)
  e' : length t ＝ succ (Y (pad u))
  e' = l ∙ (ap succ e) ⁻¹
  r : length t ≤ℕ length u
  r = length-++-right s t

determining-bar-implies-stopping-bar
 : (Y : (ℕ → ℕ) → ℕ) (s : List ℕ)
 → (determining-prefixes Y) bars s → (stopping-prefixes Y) bars s
determining-bar-implies-stopping-bar Y s (hit det)
 = bars-from-level (stopping-prefixes Y) s (succ (Y (pad s)))
    (determining-prefix-gives-stopping-level Y s det)
determining-bar-implies-stopping-bar Y s (step φ) = step ih
 where
  ih : (n : ℕ) → stopping-prefixes Y bars (s ++ [ n ])
  ih n = determining-bar-implies-stopping-bar Y (s ++ [ n ]) (φ n)

\end{code}

If Y is bar continuous, its stopping prefixes control recursion at every
finite sequence.

\begin{code}

bar-continuity-implies-stopping-prefixes-control-recursion
 : (Y : (ℕ → ℕ) → ℕ) → is-bar-continuous Y
 → (s : List ℕ) → (stopping-prefixes Y) controls-recursion-at s
bar-continuity-implies-stopping-prefixes-control-recursion Y b s =
 bars-implies-controls-recursion-at (stopping-prefixes Y) dec s
  (determining-bar-implies-stopping-bar Y s
    (bar-continuity-implies-bar-continuity″ Y b s))
 where
  dec : (u : List ℕ) → is-decidable (u ∈ stopping-prefixes Y)
  dec u = <-decidable (Y (pad u)) (length u)

\end{code}

Instantiate the general recursor and its equations with Spector's
stopping predicate.

\begin{code}

sbr : {X : 𝓤 ̇} (Y : (ℕ → ℕ) → ℕ) → is-bar-continuous Y → BarRecursor X
sbr Y b = gbr (bar-continuity-implies-stopping-prefixes-control-recursion Y b)

spector-bar-recursor-spec
 : {X : 𝓤 ̇} (Y : (ℕ → ℕ) → ℕ) (b : is-bar-continuous Y)
 → (G : List ℕ → X) (H : List ℕ → (ℕ → X) → X) (s : List ℕ)
 → (Y (pad s) <ℕ length s
      → sbr Y b G H s ＝ G s)
 × (length s ≤ℕ Y (pad s)
      → sbr Y b G H s ＝ H s (λ n → sbr Y b G H (s ++ [ n ])))
spector-bar-recursor-spec {X = X} Y b G H s
 using (base-case , step-case) ←
   general-bar-recursor-spec {X = X}
     (bar-continuity-implies-stopping-prefixes-control-recursion Y b) G H s
 = base-case , step-case'
 where
  step-case' : length s ≤ℕ Y (pad s)
             → sbr Y b G H s ＝ H s (λ n → sbr Y b G H (s ++ [ n ]))
  step-case' q = step-case (bigger-or-equal-not-less (length s) (Y (pad s)) q)

\end{code}

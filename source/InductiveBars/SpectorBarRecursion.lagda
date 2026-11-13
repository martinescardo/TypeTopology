Chuangjie Xu, November 2026

We construct a Spector bar recursor for each bar-continuous control functional.

Following the approach of Paulo Oliva and Silvia Steila in "A direct proof of
Schwichtenberg's bar recursion closure theorem" (2018, Theorem 2.4), we derive
Spector's bar recursion from general bar recursion.

Oliva and Steila construct a System T term for the recursor from a System T
term for the control. Here we construct an Agda term for the recursor from
a witness that the control is bar continuous.

TODO. Investigate whether Spector bar recursors for bar-continuous control
functionals can be obtained more simply from the modified bar recursors
constructed in InductiveBars.ModifiedBarRecursion. Berger and Oliva's
result that Spector's bar recursion is definable from modified bar recursion
("Modified bar recursion", 2006, Theorem 6.5) suggests a possible route.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import MLTT.Spartan hiding (𝓤 ; 𝓦)
open import UF.FunExt using (Fun-Ext ; dfunext)

module InductiveBars.SpectorBarRecursion
 (fe : Fun-Ext)
 {𝓤 : Universe}
 (A : 𝓤 ̇)
 where

open import MLTT.List
open import Naturals.Order

open import InductiveBars.Sequences hiding (pad)
open import InductiveBars.Basics
open import InductiveBars.Continuity A ℕ

\end{code}

A witness of `V controls-recursion-at s` describes the possible recursive
calls starting at s. Along each branch, recursion stops at the first
extension of s that belongs to V.

\begin{code}

data _controls-recursion-at_ {𝓥 : Universe} (V : List A → 𝓥 ̇)
 : List A → 𝓤 ⊔ 𝓥 ̇
 where
 stop     : {s : List A}
          → s ∈ V
          → V controls-recursion-at s
 continue : {s : List A}
          → s ∉ V
          → ((a : A) → V controls-recursion-at (s ++ [ a ]))
          → V controls-recursion-at s

\end{code}

For decidable V, if V bars s, then V controls recursion at s.

\begin{code}

bars-implies-controls-recursion-at
 : (V : List A → 𝓥 ̇) → ((s : List A) → is-decidable (s ∈ V))
 → (s : List A) → V bars s → V controls-recursion-at s
bars-implies-controls-recursion-at V dec s (hit p) = stop p
bars-implies-controls-recursion-at V dec s (step φ) =
 cases stop (λ q → continue q ih) (dec s)
 where
  ih : (a : A) → V controls-recursion-at (s ++ [ a ])
  ih a = bars-implies-controls-recursion-at V dec (s ++ [ a ]) (φ a)

\end{code}

We evaluate recursively on a witness of `V controls-recursion-at s`.
The following definition shows how the witness determines when to stop
and when to continue.

\begin{code}

module _ {𝓦 : Universe} (X : 𝓦 ̇) where

 eval : {V : List A → 𝓥 ̇}
      → (List A → X) → (List A → (A → X) → X)
      → (s : List A) → V controls-recursion-at s → X
 eval G H s (stop _) = G s
 eval G H s (continue _ φ) = H s (λ a → eval G H (s ++ [ a ]) (φ a))

\end{code}

Evaluation is independent of the control witness, even when V is not
proposition-valued, because evaluation does not use the data carried by
stop witnesses. We use this independence to verify the recursion equations.

\begin{code}

 eval-witness-independent
  : {V : List A → 𝓥 ̇}
  → (G : List A → X) (H : List A → (A → X) → X)
  → (s : List A) (c c' : V controls-recursion-at s)
  → eval G H s c ＝ eval G H s c'
 eval-witness-independent G H s (stop p) (stop q) = refl
 eval-witness-independent G H s (stop p) (continue q ψ) = 𝟘-elim (q p)
 eval-witness-independent G H s (continue p φ) (stop q) = 𝟘-elim (p q)
 eval-witness-independent G H s (continue p φ) (continue q ψ)
  = ap (H s) (dfunext fe ih)
  where
   ih : (a : A)
      → eval G H (s ++ [ a ]) (φ a) ＝ eval G H (s ++ [ a ]) (ψ a)
   ih a = eval-witness-independent G H (s ++ [ a ]) (φ a) (ψ a)

\end{code}

If V controls recursion at every finite sequence, we can construct
a general bar recursor for V in the sense of Oliva and Steila, using
the above evaluation function.

\begin{code}

 BarRecursor : 𝓤 ⊔ 𝓦 ̇
 BarRecursor = (List A → X) → (List A → (A → X) → X) → List A → X

 gbr : {B : List A → 𝓥 ̇}
     → ((s : List A) → B controls-recursion-at s)
     → BarRecursor
 gbr d G H s = eval G H s (d s)

 general-bar-recursor-spec
  : {B : List A → 𝓥 ̇} (d : (s : List A) → B controls-recursion-at s)
  → (G : List A → X) (H : List A → (A → X) → X) (s : List A)
  → (s ∈ B → gbr d G H s ＝ G s)
  × (s ∉ B → gbr d G H s ＝ H s (λ a → gbr d G H (s ++ [ a ])))
 general-bar-recursor-spec {B = B} d G H s = base-case , step-case
  where
   unique : (e : B controls-recursion-at s) → gbr d G H s ＝ eval G H s e
   unique e = eval-witness-independent G H s (d s) e
   base-case : s ∈ B → gbr d G H s ＝ G s
   base-case p = unique (stop p)
   step-case : s ∉ B → gbr d G H s ＝ H s (λ a → gbr d G H (s ++ [ a ]))
   step-case q = unique (continue q (λ a → d (s ++ [ a ])))

\end{code}

Now we switch to Spector's bar recursion.

Spector's recursion, controlled by a functional Y : (ℕ → A) → ℕ, stops at
input s when Y (pad s) < length s. Here pad s extends s to an infinite
sequence by repeating a fixed element a₀ : A after its last entry. So we
assume a given a₀ : A throughout the development of Spector bar recursion.

\begin{code}

 module _ (a₀ : A) where

  private
   pad : List A → ℕ → A
   pad = pad-with a₀

  stopping-prefixes : ((ℕ → A) → ℕ) → List A → 𝓤₀ ̇
  stopping-prefixes Y s = Y (pad s) <ℕ length s

\end{code}

A bar of determining prefixes gives a bar of stopping prefixes.

This result is due to the fact that, once s determines Y, all extensions
of s by Y (pad s) + 1 entries satisfy the stopping condition.

\begin{code}

  determining-prefix-gives-stopping-level
   : (Y : (ℕ → A) → ℕ) (s : List A)
   → s determines Y
   → (t : List A) → length t ＝ succ (Y (pad s))
   → (s ++ t) ∈ stopping-prefixes Y
  determining-prefix-gives-stopping-level Y s det t l
   = transport (_≤ℕ length u) e' r
   where
    u : List A
    u = s ++ t
    e : Y (pad u) ＝ Y (pad s)
    e = det (pad u) (pad s)
            (extends-++ (pad u) s t (pad-extends u)) (pad-extends s)
    e' : length t ＝ succ (Y (pad u))
    e' = l ∙ (ap succ e) ⁻¹
    r : length t ≤ℕ length u
    r = length-++-right s t

  determining-bar-implies-stopping-bar
   : (Y : (ℕ → A) → ℕ) (s : List A)
   → (determining-prefixes Y) bars s → (stopping-prefixes Y) bars s
  determining-bar-implies-stopping-bar Y s (hit det)
   = bars-from-level (stopping-prefixes Y) s (succ (Y (pad s)))
      (determining-prefix-gives-stopping-level Y s det)
  determining-bar-implies-stopping-bar Y s (step φ) = step ih
   where
    ih : (a : A) → stopping-prefixes Y bars (s ++ [ a ])
    ih a = determining-bar-implies-stopping-bar Y (s ++ [ a ]) (φ a)

\end{code}

If Y is bar continuous, its stopping prefixes control recursion at every
finite sequence.

\begin{code}

  bar-continuity-implies-stopping-prefixes-control-recursion
   : (Y : (ℕ → A) → ℕ) → is-bar-continuous Y
   → (s : List A) → (stopping-prefixes Y) controls-recursion-at s
  bar-continuity-implies-stopping-prefixes-control-recursion Y b s =
   bars-implies-controls-recursion-at (stopping-prefixes Y) dec s
    (determining-bar-implies-stopping-bar Y s
      (bar-continuity-implies-bar-continuity″ Y b s))
   where
    dec : (u : List A) → is-decidable (u ∈ stopping-prefixes Y)
    dec u = <-decidable (Y (pad u)) (length u)

\end{code}

Instantiate the general recursor and its equations with Spector's
stopping predicate.

\begin{code}

  sbr : (Y : (ℕ → A) → ℕ) → is-bar-continuous Y → BarRecursor
  sbr Y b = gbr (bar-continuity-implies-stopping-prefixes-control-recursion Y b)

  spector-bar-recursor-spec
   : (Y : (ℕ → A) → ℕ) (b : is-bar-continuous Y)
   → (G : List A → X) (H : List A → (A → X) → X) (s : List A)
   → (Y (pad s) <ℕ length s
        → sbr Y b G H s ＝ G s)
   × (length s ≤ℕ Y (pad s)
        → sbr Y b G H s ＝ H s (λ a → sbr Y b G H (s ++ [ a ])))
  spector-bar-recursor-spec Y b G H s
   using (base-case , step-case) ←
     general-bar-recursor-spec
       (bar-continuity-implies-stopping-prefixes-control-recursion Y b) G H s
   = base-case , step-case'
   where
    step-case' : length s ≤ℕ Y (pad s)
               → sbr Y b G H s ＝ H s (λ a → sbr Y b G H (s ++ [ a ]))
    step-case' q = step-case (bigger-or-equal-not-less (length s) (Y (pad s)) q)

\end{code}

Moreover, the above Spector bar recursor is independent of the witness
that the control functional is bar continuous.

\begin{code}

  sbr-witness-independent
   : (Y : (ℕ → A) → ℕ) (b b' : is-bar-continuous Y)
   → (G : List A → X) (H : List A → (A → X) → X) (s : List A)
   → sbr Y b G H s ＝ sbr Y b' G H s
  sbr-witness-independent Y b b' G H s = eval-witness-independent G H s c c'
   where
    c c' : stopping-prefixes Y controls-recursion-at s
    c  = bar-continuity-implies-stopping-prefixes-control-recursion Y b s
    c' = bar-continuity-implies-stopping-prefixes-control-recursion Y b' s

\end{code}

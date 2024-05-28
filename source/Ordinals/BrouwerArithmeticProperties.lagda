--------------------------------------------------------------------------------
authors:      ["Bruno Paiva"]
date-started: 2024-05-22
--------------------------------------------------------------------------------
\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import Ordinals.Brouwer
open import Ordinals.BrouwerArithmetic
open import Ordinals.BrouwerOrdering

module Ordinals.BrouwerArithmeticProperties where

\end{code}

\section{Properties of Addition}

First we see how to extend paths of a single summand to paths of the
sum of two ordinals.

The geometric picture is as follows: given ordinals α and β like

```
 α = (*  *  *  * ...)

 β = (&  &  &  &  &  & ...)
```

their sum will consist of a copy of α followed by a copy of β like

```
 α + β = (*  *  *  * ...)  (&  &  &  &  &  & ...)
```

Hence, we can get paths in α + β from either
 - a path in α by skipping the copy of β
 - a path in β (which will never reach the the copy of α)

\begin{code}

extend-path-left-+B : (b c : B) → PathThroughS b → PathThroughS (b +B c)
extend-path-left-+B b Z     p = p
extend-path-left-+B b (S c) p = continue (extend-path-left-+B b c p)
extend-path-left-+B b (L ϕ) p = pick (λ z → b +B ϕ z) zero (extend-path-left-+B b (ϕ zero) p)

extend-path-left-+B-correct : (b c : B) (p : PathThroughS b)
                            → Path-to-ordinal p ＝ Path-to-ordinal (extend-path-left-+B b c p)
extend-path-left-+B-correct b Z     p = refl
extend-path-left-+B-correct b (S c) p = extend-path-left-+B-correct b c p
extend-path-left-+B-correct b (L x) p = extend-path-left-+B-correct b (x zero) p

extend-path-right-+B : (b c : B) → PathThroughS c → PathThroughS (b +B c)
extend-path-right-+B b (S c) (stop c)     = stop (b +B c)
extend-path-right-+B b (S c) (continue p) = continue (extend-path-right-+B b c p)
extend-path-right-+B b (L ϕ) (pick ϕ n p) = pick (λ i → b +B ϕ i) n (extend-path-right-+B b (ϕ n) p)

extend-path-right-+B-correct : (b c : B) (p : PathThroughS c)
                             → b +B Path-to-ordinal p ＝ Path-to-ordinal (extend-path-right-+B b c p)
extend-path-right-+B-correct b (S c) (stop c)     = refl
extend-path-right-+B-correct b (S c) (continue p) = extend-path-right-+B-correct b c p
extend-path-right-+B-correct b (L ϕ) (pick ϕ n p) = extend-path-right-+B-correct b (ϕ n) p

\end{code}

With these extensions of paths we can see that addition is inflationary
and monotonic in both arguments

\begin{code}

+B-inflationary-right : (b c : B) → c ⊑ b +B c
+B-inflationary-right b Z     = Z-⊑ _
+B-inflationary-right b (S c) = S-⊑ _ _ (stop (b +B c)) (+B-inflationary-right b c)
+B-inflationary-right b (L ϕ) =
 L-⊑ _ _ (λ i → ⊑-trans _ _ _
                 (L-is-upper-bound ϕ i)
                 (L-is-monotonic _ _ (λ j → +B-inflationary-right b (ϕ j))))

+B-inflationary-left : (b c : B) → b ⊑ b +B c
+B-inflationary-left b c =
 sufficient-path-condition-for-⊑ b (b +B c)
  (λ p → extend-path-left-+B b c p , extend-path-left-+B-correct b c p)

+B-monotonic-right : (b c d : B) → c ⊑ d → b +B c ⊑ b +B d
+B-monotonic-right b Z d h = +B-inflationary-left b d
+B-monotonic-right b (S c) d (S-⊑ c d p h) =
 S-⊑ (b +B c) (b +B d) (extend-path-right-+B b d p)
  (transport ((b +B c) ⊑_)
   (extend-path-right-+B-correct b d p)
   (+B-monotonic-right b c (Path-to-ordinal p) h))
+B-monotonic-right b (L ϕ) d h =
 L-⊑ (λ i → b +B ϕ i) (b +B d) (λ i → +B-monotonic-right b (ϕ i) d
   (⊑-trans (ϕ i) (L ϕ) d (L-is-upper-bound ϕ i) h))

+B-monotonic-left : (b c d : B) → b ⊑ d → b +B c ⊑ d +B c
+B-monotonic-left b Z     d h = h
+B-monotonic-left b (S c) d h = S-is-monotonic (b +B c) (d +B c) (+B-monotonic-left b c d h)
+B-monotonic-left b (L ϕ) d h = L-is-monotonic (λ i → b +B ϕ i) (λ i → d +B ϕ i)
 (λ i → +B-monotonic-left b (ϕ i) d h)

\end{code}

Fixing the right summand to be greater than zero, then addition is
strictly inflationary on the left.

The equivalent statement for the right is not true: for example, the sum
`S Z +B ω` is equal to `ω`, even though 'S Z' is strictly greater than 'Z'.

\begin{code}

+B-strictly-inflationary-left : (b c : B) → Z ⊏ c → b ⊏ b +B c
+B-strictly-inflationary-left b c (p , _) =
 extend-path-right-+B b c p ,
 transport (b ⊑_) (extend-path-right-+B-correct b c p) (+B-inflationary-left b (Path-to-ordinal p))

\end{code}

For a similar reason, we can show that addition is strictly monotonic on
the right, but not on the left.

\begin{code}

+B-strictly-monotonic-right : (b c d : B) → c ⊏ d → b +B c ⊏ b +B d
+B-strictly-monotonic-right b c d (p , h) =
 extend-path-right-+B b d p ,
 transport ((b +B c) ⊑_)
  (extend-path-right-+B-correct b d p)
  (+B-monotonic-right b c (Path-to-ordinal p) h)

\end{code}

\section{Properties of Multiplication}

We can build paths from the product of two ordinals from two paths through
each factor.

TODO explain the geometric picture

\begin{code}

join-paths-×B : {b c : B} → PathThroughS b → PathThroughS c  → PathThroughS (b ×B c)
join-paths-×B {b} {S c} p (stop c)     = extend-path-right-+B (b ×B c) b p
join-paths-×B {b} {S c} p (continue q) = extend-path-left-+B (b ×B c) b (join-paths-×B p q)
join-paths-×B {b} {L ϕ} p (pick ϕ n q) = pick (λ i → b ×B ϕ i) n (join-paths-×B p q)

join-paths-×B-correct : {b c : B} (p : PathThroughS b) (q : PathThroughS c)
                      → (b ×B Path-to-ordinal q) +B Path-to-ordinal p ＝ Path-to-ordinal (join-paths-×B p q)
join-paths-×B-correct {b} {S c} p (stop c)     = extend-path-right-+B-correct (b ×B c) b p
join-paths-×B-correct {b} {S c} p (continue q) =
 (b ×B Path-to-ordinal q) +B Path-to-ordinal p
  ＝⟨ join-paths-×B-correct p q ⟩
 Path-to-ordinal (join-paths-×B p q)
  ＝⟨ extend-path-left-+B-correct (b ×B c) b (join-paths-×B p q) ⟩
 Path-to-ordinal (extend-path-left-+B (b ×B c) b (join-paths-×B p q))
  ∎
join-paths-×B-correct {b} {L ϕ} p (pick ϕ n q) = join-paths-×B-correct p q

\end{code}

With these extensions of paths we can that multiplication is inflationary
and monotonic in both arguments, assuming that the other argument is
strictly greater than zero.

\begin{code}

×B-inflationary-right : (b c : B) → Z ⊏ b → c ⊑ b ×B c
×B-inflationary-right b Z     (q , h) = Z-⊑ Z
×B-inflationary-right b (S c) (q , h) = ⊑-trans _ _ _ I II
 where
  I : S c ⊑ c +B b
  I = +B-monotonic-right c (S Z) b (S-⊑ Z b q h)

  II : c +B b ⊑ (b ×B c) +B b
  II = +B-monotonic-left c b (b ×B c) (×B-inflationary-right b c (q , h))
×B-inflationary-right b (L ϕ) (q , h) =
 L-is-monotonic ϕ (λ i → b ×B ϕ i) (λ i → ×B-inflationary-right b (ϕ i) (q , h))


×B-inflationary-left : (b c : B) → Z ⊏ c → b ⊑ b ×B c
×B-inflationary-left b c (q , _) = simulation-implies-⊑ b (b ×B c) aux
 where
  aux : (p : PathThroughS b)
      → Σ q ꞉ PathThroughS (b ×B c) , Path-to-ordinal p ⊑ Path-to-ordinal q
  aux p = join-paths-×B p q ,
          transport (Path-to-ordinal p ⊑_)
           (join-paths-×B-correct p q)
           (+B-inflationary-right (b ×B Path-to-ordinal q) (Path-to-ordinal p))

×B-monotonic-right : (b c d : B) → c ⊑ d → b ×B c ⊑ b ×B d
×B-monotonic-right b Z d h = Z-⊑ (b ×B d)
×B-monotonic-right b (S c) (S d) (S-⊑ c (S d) (stop d)     h) =
 +B-monotonic-left (b ×B c) b (b ×B d) (×B-monotonic-right b c d h)
×B-monotonic-right b (S c) (S d) (S-⊑ c (S d) (continue p) h) =
 +B-monotonic-left (b ×B c) b (b ×B d)
  (×B-monotonic-right b c d
   (⊑-trans c (Path-to-ordinal p) d h (path-to-ordinal-⊑ p)))
×B-monotonic-right b (S c) (L ϕ) (S-⊑ c (L ϕ) (pick ϕ n p) h) =
  ⊑-trans _ _ _ I II
 where
  I : (b ×B c) +B b ⊑ b ×B ϕ n
  I = ×B-monotonic-right b (S c) (ϕ n) (S-⊑ c (ϕ n) p h)

  II : b ×B ϕ n ⊑ L (λ i → b ×B ϕ i)
  II = L-is-upper-bound (λ i → b ×B ϕ i) n
×B-monotonic-right b (L ϕ) d (L-⊑ ϕ d h) =
 L-⊑ (λ i → b ×B ϕ i) (b ×B d) (λ i → ×B-monotonic-right b (ϕ i) d (h i))

×B-monotonic-left : (b c d : B) → b ⊑ d → b ×B c ⊑ d ×B c
×B-monotonic-left b Z d h     = Z-⊑ Z
×B-monotonic-left b (S c) d h = ⊑-trans _ _ _ I II
 where
  I : (b ×B c) +B b ⊑ (d ×B c) +B b
  I = +B-monotonic-left (b ×B c) b (d ×B c) (×B-monotonic-left b c d h)

  II : (d ×B c) +B b ⊑ (d ×B c) +B d
  II = +B-monotonic-right (d ×B c) b d h
×B-monotonic-left b (L ϕ) d h =
 L-is-monotonic (λ i → b ×B ϕ i) (λ i → d ×B ϕ i)
  (λ i → ×B-monotonic-left b (ϕ i) d h)

\end{code}

TODO talk about when ×B is strictly inflationary

\begin{code}

×B-strictly-inflationary-left : (b c : B) → Z ⊏ b → S Z ⊏ c → b ⊏ b ×B c
×B-strictly-inflationary-left b c (p , _) (q , S-⊑ Z _ r h) =
  join-paths-×B p q ,
  transport (b ⊑_) (join-paths-×B-correct p q) (⊑-trans _ _ _ I II)
 where
  I : b ⊑ b ×B Path-to-ordinal q
  I = ×B-inflationary-left b (Path-to-ordinal q) (r , h)

  II : b ×B Path-to-ordinal q ⊑ (b ×B Path-to-ordinal q) +B Path-to-ordinal p
  II = +B-inflationary-left (b ×B Path-to-ordinal q) (Path-to-ordinal p)

\end{code}

TODO talk about when ×B is strictly monotone

\begin{code}

×B-strictly-monotonic-right : (b c d : B) → S Z ⊏ b → c ⊏ d → (b ×B c) ⊏ (b ×B d)
×B-strictly-monotonic-right b c d (p , S-⊑ _ _ q _) (r , l) =
  join-paths-×B p r ,
  transport (b ×B c ⊑_)
   (join-paths-×B-correct p r)
   (⊑-trans _ _ _ I II)
 where
  I : b ×B c ⊑ b ×B Path-to-ordinal r
  I = ×B-monotonic-right b c (Path-to-ordinal r) l

  II : b ×B Path-to-ordinal r ⊑ (b ×B Path-to-ordinal r) +B Path-to-ordinal p
  II = +B-inflationary-left (b ×B Path-to-ordinal r) (Path-to-ordinal p)

\end{code}

\section{Properties of Exponentiation}

TODO talk about results

\begin{code}

-- TODO results about exponentiation go here

\end{code}

\subsection{Fixed Points of Exponentiation}

TODO come up with results we need. make it general for all fixed points?

\begin{code}

--⊏-ε₀-implies-S-⊏-ε₀ : (b : B) → b ⊏ ε₀ → S b ⊏ ε₀
--⊏-ε₀-implies-S-⊏-ε₀ b (pick .ω-tower n p , h) =
-- pick ω-tower (succ n) q , {!!}
-- where
--  q : PathThroughS (ω-tower (succ n))
--  q = {!!}

\end{code}

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

The geometric picture is as follows: given ordinals α and β like

```
 α = (*  *  *  * ...)

 β = (&  &  &  ...)
```

their product will consist of a copy of α for each point of β like

```
   β   = (      &                 &                &                ...)
 α × β = (*  *  *  * ...)  (*  *  *  * ...) (*  *  *  * ...)
```

Hence we can use a path from β to reach a copy of α, and from there use
a path from α.

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

Similarly to addition, fixing the left factor to be greater than 1 makes
multiplication a strictly inflationary function.

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

And fixing the right factor to be greater than 1 turns multiplication into a
strictly monotonic function.

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

TODO talk about linking multiplication and addition

\begin{code}

--L-+B-⊑-+B-L : (b : B) (ϕ : ℕ → B)
--            → L (λ i → b +B ϕ i) ⊑ b +B L ϕ
--L-+B-⊑-+B-L b ϕ = L-⊑ (λ i → b +B ϕ i) (L (λ i → b +B ϕ i)) (L-is-upper-bound (λ i → b +B ϕ i))
--
--+B-L-⊑-L-+B : (b : B) (ϕ : ℕ → B)
--            → b +B L ϕ ⊑ L (λ i → b +B ϕ i)
--+B-L-⊑-L-+B b ϕ = L-⊑ (λ i → b +B ϕ i) (L (λ i → b +B ϕ i)) (L-is-upper-bound (λ i → b +B ϕ i))
--
--L-×B-⊑-×B-L : (b : B) (ϕ : ℕ → B)
--            → L (λ i → b ×B ϕ i) ⊑ b ×B L ϕ
--L-×B-⊑-×B-L b ϕ = L-⊑ (λ i → b ×B ϕ i) (L (λ i → b ×B ϕ i)) (L-is-upper-bound (λ i → b ×B ϕ i))
--
--×B-L-⊑-L-×B : (b : B) (ϕ : ℕ → B)
--            → b ×B L ϕ ⊑ L (λ i → b ×B ϕ i)
--×B-L-⊑-L-×B b ϕ = L-⊑ (λ i → b ×B ϕ i) (L (λ i → b ×B ϕ i)) (L-is-upper-bound (λ i → b ×B ϕ i))

-- b and c both at least 2
+B-⊑-×B : (b c : B) → S Z ⊏ b → S Z ⊏ c → b +B c ⊑ b ×B c
+B-⊑-×B b (S Z) h r = 𝟘-elim (⊏-irrefl (S Z) r)
+B-⊑-×B b (S (S Z)) (p , S-⊑ _ _ q _) r =
 S-⊑ (S b) ((Z +B b) +B b)
  (extend-path-right-+B (Z +B b) b p)
  (S-⊑ b (Path-to-ordinal (extend-path-right-+B (Z +B b) b p))
   (transport PathThroughS
    (extend-path-right-+B-correct (Z +B b) b p)
    (extend-path-right-+B (Z +B b) (Path-to-ordinal p) q))
   (transport (b ⊑_) (aux (Z +B b) b p q) (⊑-trans _ _ _ I II)))
 where
  aux : (a b : B)
        (p : PathThroughS b)
        (q : PathThroughS (Path-to-ordinal p))
      → a +B Path-to-ordinal q ＝
         Path-to-ordinal (transport PathThroughS (extend-path-right-+B-correct a b p) (extend-path-right-+B a (Path-to-ordinal p) q))
  aux a (S b) (stop b)     q = extend-path-right-+B-correct a b q
  aux a (S b) (continue p) q = aux a b p q
  aux a (L ϕ) (pick ϕ n p) q = aux a (ϕ n) p q

  I : b ⊑ Z +B b
  I = +B-inflationary-right Z b

  II : Z +B b ⊑ (Z +B b) +B Path-to-ordinal q
  II = +B-inflationary-left (Z +B b) (Path-to-ordinal q)
+B-⊑-×B b (S (S (S c))) h r =
 ⊑-trans _ _ _ (+B-monotonic-left (S (S (b +B c))) (S Z) (((b ×B c) +B b) +B b) (+B-⊑-×B b (S (S c)) h (stop (S c) , S-⊑ Z (S c) (stop c) (Z-⊑ c)))) II
 where
  IH : S (S (b +B c)) ⊑ ((b ×B c) +B b) +B b
  IH = +B-⊑-×B b (S (S c)) h (stop (S c) , S-⊑ Z (S c) (stop c) (Z-⊑ c))

  I : S (S (b +B c)) +B S Z ⊑ (((b ×B c) +B b) +B b) +B S Z
  I = +B-monotonic-left (S (S (b +B c))) (S Z) (((b ×B c) +B b) +B b) IH

  II :  (((b ×B c) +B b) +B b) +B S Z ⊑ (((b ×B c) +B b) +B b) +B b
  II = +B-monotonic-right _ _ _ (⊏-implies-⊑ _ _ h)
+B-⊑-×B b (S (S (L ϕ))) h (p , S-⊑ _ _ q _) = {!!}
 where
  goal : ((L (λ i → b +B ϕ i)) +B b) +B b ⊑ (L (λ i → b ×B ϕ i) +B b) +B b
  goal = {!!}


  --I : (b +B c) +B S Z ⊑ (b +B c) +B b
  --I = +B-monotonic-right (b +B c) (S Z) b (S-⊑ Z b p (Z-⊑ (Path-to-ordinal p)))
  --II : {!!}
  --II = +B-monotonic-left (b +B c) b (b ×B c) (+B-⊑-×B {b} {c} (p , S-⊑ Z (Path-to-ordinal p) q h) {!!})
+B-⊑-×B b (S (L ϕ)) (p , S-⊑ _ _ q h) (r , S-⊑ _ _ s l) = {!!}
+B-⊑-×B b (L ϕ) (p , S-⊑ _ _ q h) (r , S-⊑ _ _ s l) = {!!}

\end{code}

\section{Properties of Exponentiation}

TODO talk about results

\begin{code}

-- TODO results about exponentiation go here

data PathThroughS_Over_ : B → B → 𝓤₀ ̇ where

 Z-path : (b : B)
        → PathThroughS b Over Z

 S-path : {b c : B}
        → PathThroughS b
        → PathThroughS b Over c
        → PathThroughS b Over (S c)

 L-path : {b : B}
        → PathThroughS b
        → (ϕ : ℕ → B)
        → ((n : ℕ) → PathThroughS b Over (ϕ n))
        → PathThroughS b Over (L ϕ)

join-paths-^B : {b c : B}
              → PathThroughS b Over c
              → PathThroughS c
              → PathThroughS (b ^B c)
join-paths-^B {b} {S c} (S-path p ps)   (stop c)     =
 join-paths-×B {!!} p
join-paths-^B {b} {S c} (S-path p ps)   (continue q) =
 join-paths-×B (join-paths-^B ps q) p
join-paths-^B {b} {L ϕ} (L-path p ϕ ps) (pick ϕ n q) =
 pick (λ i → b ^B ϕ i) n (join-paths-^B (ps n) q)

^B-inflationary-right : (b c : B) → S Z ⊏ b → c ⊑ b ^B c
^B-inflationary-right b Z     h = Z-⊑ (S Z)
^B-inflationary-right b (S c) (p , S-⊑ _ _ q h) =
  {!!}
 where
  I : c +B S Z ⊑ c ×B b
  I = {!!}

  II : c ×B b ⊑ (b ^B c) ×B b
  II = ×B-monotonic-left c b (b ^B c)
        (^B-inflationary-right b c (p , S-⊑ Z (Path-to-ordinal p) q h))
^B-inflationary-right b (L ϕ) h =
 L-⊑ ϕ (L (λ i → b ^B ϕ i))
  (λ i → ⊑-trans _ _ _
   (^B-inflationary-right b (ϕ i) h)
   (L-is-upper-bound (λ i → b ^B ϕ i) i))

\end{code}

\subsection{Fixed Points of Exponentiation}

TODO come up with results we need. make it general for all fixed points?

\begin{code}

-- Not exactly relevant for here, but good to better understand the ordering
outside-S-not-⊑-inside-S : ¬ (S ω ⊑ L (S ∘ finite))
outside-S-not-⊑-inside-S (S-⊑ _ _ (pick _ n (stop _)) (L-⊑ _ _ h)) =
 ⊏-irrefl (finite (succ n)) (⊑-and-⊏-implies-⊏ _ _ _ I II)
 where
  I : finite (succ n) ⊑ finite n
  I = h (succ n)

  II : finite n ⊏ finite (succ n)
  II = S-is-strictly-inflationary (finite n)
outside-S-not-⊑-inside-S (S-⊑ _ _ (pick _ n (continue p)) (L-⊑ _ _ h)) =
 ⊏-irrefl (finite (succ n))
  (⊑-and-⊏-implies-⊏ _ _ _ I (⊑-and-⊏-implies-⊏ _ _ _ II III))
 where
  I : finite (succ n) ⊑ Path-to-ordinal p
  I = h (succ n)

  II : Path-to-ordinal p ⊑ finite n
  II = path-to-ordinal-⊑ p

  III : finite n ⊏ finite (succ n) 
  III = S-is-strictly-inflationary (finite n)

 
--⊏-ε₀-implies-S-⊏-ε₀ : (b : B) → b ⊏ ε₀ → S b ⊏ ε₀
--⊏-ε₀-implies-S-⊏-ε₀ b (pick .ω-tower n p , h) =
-- pick ω-tower (succ n) q , {!!}
-- where
--  q : PathThroughS (ω-tower (succ n))
--  q = {!!}

\end{code}

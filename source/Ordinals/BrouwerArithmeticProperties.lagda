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
open import UF.Equiv
open import UF.FunExt

module Ordinals.BrouwerArithmeticProperties where

\end{code}

\section{Properties of Addition}

First we see how to get strict subtrees of the sum of two ordinals.

The geometric picture is as follows: given ordinals α and β like

```
 α = (*  *  *  * ...)

 β = (&  &  &  &  &  & ...)
```

their sum will consist of a copy of α followed by a copy of β like

```
 α + β = (*  *  *  * ...)  (&  &  &  &  &  & ...)
```

Hence, we can get subtrees in α + β from either
 - a subtree in α
 - a subtree in β by pasting α at the leaf nodes

\begin{code}

subtree-of-+B-left : (c d b : B) → b ◂ c → b ◂ (c +B d)
subtree-of-+B-left c Z     b h = h
subtree-of-+B-left c (S d) b h = ◂-continue (subtree-of-+B-left c d b h)
subtree-of-+B-left c (L ϕ) b h = ◂-pick (λ i → c +B ϕ i) 0 (subtree-of-+B-left c (ϕ 0) b h)

subtree-of-+B-right : (c d b : B) → b ◂ d → (c +B b) ◂ (c +B d)
subtree-of-+B-right c (S d) b (◂-stop h) = ◂-stop (+B-respects-≈-right c b d h)
subtree-of-+B-right c (S d) b (◂-continue h) =
 ◂-continue (subtree-of-+B-right c d b h)
subtree-of-+B-right c (L ϕ) b (◂-pick ϕ n h) =
 ◂-pick (λ z → c +B ϕ z) n (subtree-of-+B-right c (ϕ n) b h)

\end{code}

With these extensions of paths we can see that addition is inflationary
and monotonic in both arguments

\begin{code}

+B-inflationary-right : (b c : B) → c ⊑ b +B c
+B-inflationary-right b Z     = Z-⊑ _
+B-inflationary-right b (S c) =
 S-⊑ c (b +B c) (S (b +B c)) (+B-inflationary-right b c) (◂-stop (≈-refl (b +B c)))
+B-inflationary-right b (L ϕ) =
 L-⊑ _ _ (λ i → ⊑-trans _ _ _
                 (L-is-upper-bound ϕ i)
                 (L-is-monotonic _ _ (λ j → +B-inflationary-right b (ϕ j))))

+B-inflationary-left : (b c : B) → b ⊑ b +B c
+B-inflationary-left b c =
 share-subtrees-implies-⊑ b (b +B c) (subtree-of-+B-left b c)

+B-monotonic-right : (b c d : B) → c ⊑ d → b +B c ⊑ b +B d
+B-monotonic-right b Z d h = +B-inflationary-left b d
+B-monotonic-right b (S c) d (S-⊑ c e d h l) =
 S-⊑ (b +B c) (b +B e) (b +B d)
  (+B-monotonic-right b c e h)
  (subtree-of-+B-right b d e l)
+B-monotonic-right b (L ϕ) d h =
 L-⊑ (λ i → b +B ϕ i) (b +B d)
  λ i → +B-monotonic-right b (ϕ i) d
         (⊑-trans (ϕ i) (L ϕ) d (L-is-upper-bound ϕ i) h)

+B-monotonic-left : (b c d : B) → b ⊑ d → b +B c ⊑ d +B c
+B-monotonic-left b Z     d h = h
+B-monotonic-left b (S c) d h = S-is-monotonic (b +B c) (d +B c) (+B-monotonic-left b c d h)
+B-monotonic-left b (L ϕ) d h = L-is-monotonic (λ i → b +B ϕ i) (λ i → d +B ϕ i)
 (λ i → +B-monotonic-left b (ϕ i) d h)

+B-preserves-⊒⊑-right : (b c d : B)
                     → c ⊒⊑ d
                     → b +B c ⊒⊑ b +B d
+B-preserves-⊒⊑-right b c d (h , l) = +B-monotonic-right b c d h ,
                                      +B-monotonic-right b d c l

+B-preserves-⊒⊑-left : (b c d : B)
                     → b ⊒⊑ d
                     → b +B c ⊒⊑ d +B c
+B-preserves-⊒⊑-left b c d (h , l) = +B-monotonic-left b c d h ,
                                     +B-monotonic-left d c b l

\end{code}

Fixing the right summand to be greater than zero, then addition is
strictly inflationary on the left.

The equivalent statement for the right is not true: for example, the sum
`S Z +B ω` is equal to `ω`, even though 'S Z' is strictly greater than 'Z'.

\begin{code}

+B-strictly-inflationary-left : (b c : B) → Z ⊏ c → b ⊏ b +B c
+B-strictly-inflationary-left b c (d , h , l) =
 b +B d , +B-inflationary-left b d , subtree-of-+B-right b c d l

\end{code}

For a similar reason, we can show that addition is strictly monotonic on
the right, but not on the left.

\begin{code}

+B-strictly-monotonic-right : (b c d : B) → c ⊏ d → b +B c ⊏ b +B d
+B-strictly-monotonic-right b c d (e , h , l) =
 b +B e , +B-monotonic-right b c e h , subtree-of-+B-right b d e l

\end{code}

Addition is not commutative, for example `1 + ω` is strictly smaller
(and hence distinct) from `ω + 1`. This is related to why addition is
not strictly inflationary fixing the left summand.

\begin{code}

1+ω-less-than-ω+1 : S Z +B ω ⊏ ω +B S Z
1+ω-less-than-ω+1 =
 ω ,
 L-⊑ (λ i → S Z +B finite i) ω
  (λ n → ⊑-trans _ _ _ (aux n) (L-is-upper-bound finite (succ n))) ,
 ◂-stop (≈-refl ω)
 where
  aux : (n : ℕ) → S Z +B finite n ⊑ finite (succ n)
  aux zero     = S-⊑ Z Z (S Z) (Z-⊑ Z) (◂-stop Z≈)
  aux (succ n) = S-⊑ (S Z +B finite n) (S (finite n)) (S (S (finite n)))
                  (aux n)
                  (◂-stop (S≈ (≈-refl (finite n))))

\end{code}

\section{Properties of Multiplication}

TODO write something

\begin{code}

0-left-zero-×B : (b : B) → Z ×B b ⊒⊑ Z
0-left-zero-×B Z     = Z-⊑ Z , Z-⊑ Z
0-left-zero-×B (S b) = 0-left-zero-×B b
0-left-zero-×B (L ϕ) = L-⊑ (λ i → Z ×B ϕ i) Z (λ i → pr₁ (0-left-zero-×B (ϕ i))) ,
                       Z-⊑ (L (λ i → Z ×B ϕ i))

1-left-unit-×B : (b : B) → b ≈ S Z ×B b
1-left-unit-×B Z     = Z≈
1-left-unit-×B (S b) = S≈ (1-left-unit-×B b)
1-left-unit-×B (L ϕ) = L≈ ϕ (λ i → S Z ×B ϕ i) (λ n → 1-left-unit-×B (ϕ n))

\end{code}

We can build strict subtrees of the product of two ordinals from
a subtree of each factor.

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

Hence we can use a subtree of β to reach a copy of α, and from there use
the subtree of α.

\begin{code}

subtree-of-×B : (b c d e : B) → d ◂ b → e ◂ c → ((b ×B e) +B d) ◂ (b ×B c)
subtree-of-×B b (S c) d e h (◂-stop l) =
 ≈-preserves-◂-right
  (subtree-of-+B-right (b ×B e) b d h)
  (+B-respects-≈-left (b ×B e) b (b ×B c) (×B-respects-≈-right b e c l))
subtree-of-×B b (S c) d e h (◂-continue l) =
 subtree-of-+B-left (b ×B c) b ((b ×B e) +B d) (subtree-of-×B b c d e h l)
subtree-of-×B b (L ϕ) d e h (◂-pick ϕ n l) =
 ◂-pick (λ i → b ×B ϕ i) n (subtree-of-×B b (ϕ n) d e h l)

\end{code}

With these extensions of paths we can that multiplication is inflationary
and monotonic in both arguments, assuming that the other argument is
strictly greater than zero.

\begin{code}

×B-inflationary-right : (b c : B) → Z ⊏ b → c ⊑ b ×B c
×B-inflationary-right b Z h = Z-⊑ Z
×B-inflationary-right b (S c) (d , h , l) = ⊑-trans _ _ _ I II
 where
  I : S c ⊑ c +B b
  I = +B-monotonic-right c (S Z) b (S-⊑ Z d b (Z-⊑ d) l)

  II : c +B b ⊑ (b ×B c) +B b
  II = +B-monotonic-left c b (b ×B c) (×B-inflationary-right b c (d , h , l))
×B-inflationary-right b (L ϕ) h =
 L-is-monotonic ϕ (λ i → b ×B ϕ i) (λ i → ×B-inflationary-right b (ϕ i) h)

×B-inflationary-left : (b c : B) → Z ⊏ c → b ⊑ b ×B c
×B-inflationary-left b c (d , _ , h) = simulation-implies-⊑ b (b ×B c) sim
 where
  sim : b simulates (b ×B c)
  sim e l = (b ×B d) +B e ,
            subtree-of-×B b c e d l h ,
            +B-inflationary-right (b ×B d) e

×B-monotonic-right : (b c d : B) → c ⊑ d → b ×B c ⊑ b ×B d
×B-monotonic-right b Z d h = Z-⊑ (b ×B d)
×B-monotonic-right b (S c) (S d) (S-⊑ c e (S d) h (◂-stop l)) =
 +B-monotonic-left (b ×B c) b (b ×B d)
  (≈-preserves-⊑-right
   (×B-monotonic-right b c e h)
   (×B-respects-≈-right b e d l))
×B-monotonic-right b (S c) (S d) (S-⊑ c e (S d) h (◂-continue l)) =
 +B-monotonic-left (b ×B c) b (b ×B d)
  (×B-monotonic-right b c d (⊑-trans _ _ _ h (◂-implies-⊑ l)))
×B-monotonic-right b (S c) (L ϕ) (S-⊑ c e (L ϕ) h (◂-pick ϕ n l)) =
  ⊑-trans ((b ×B c) +B b) (b ×B ϕ n) (L (λ i → b ×B ϕ i))
   (×B-monotonic-right b (S c) (ϕ n) (S-⊑ c e (ϕ n) h l))
   (L-is-upper-bound (λ i → b ×B ϕ i) n)
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

×B-preserves-⊒⊑-right : (b c d : B)
                     → c ⊒⊑ d
                     → b ×B c ⊒⊑ b ×B d
×B-preserves-⊒⊑-right b c d (h , l) = ×B-monotonic-right b c d h ,
                                      ×B-monotonic-right b d c l

×B-preserves-⊒⊑-left : (b c d : B)
                     → b ⊒⊑ d
                     → b ×B c ⊒⊑ d ×B c
×B-preserves-⊒⊑-left b c d (h , l) = ×B-monotonic-left b c d h ,
                                     ×B-monotonic-left d c b l
\end{code}

Similarly to addition, fixing the right factor to be greater than 1 makes
multiplication a strictly inflationary function for inputs greater than 0.

\begin{code}

×B-strictly-inflationary-left : (b c : B) → Z ⊏ b → S Z ⊏ c → b ⊏ b ×B c
×B-strictly-inflationary-left b c (d , _ , h) (e , S-⊑ Z f e r l , m) =
  (b ×B e) +B d , ⊑-trans _ _ _ I II , subtree-of-×B b c d e h m
 where
  I : b ⊑ b ×B e
  I = ×B-inflationary-left b e (f , Z-⊑ f , l)

  II : b ×B e ⊑ (b ×B e) +B d
  II = +B-inflationary-left (b ×B e) d

\end{code}

And fixing the right factor to be greater than 0 turns multiplication into a
strictly monotonic function.

\begin{code}

×B-strictly-monotonic-right : (b c d : B) → Z ⊏ b → c ⊏ d → (b ×B c) ⊏ (b ×B d)
×B-strictly-monotonic-right b c d (e , _ , m) (g , n , o) =
  (b ×B g) +B e , ⊑-trans _ _ _ I II , subtree-of-×B b d e g m o
 where
  I : b ×B c ⊑ b ×B g
  I = ×B-monotonic-right b c g n

  II : b ×B g ⊑ (b ×B g) +B e
  II = +B-inflationary-left (b ×B g) e

\end{code}

TODO talk about linking multiplication and addition

\begin{code}

increment-⊑-×B : (b c : B)
               → Z ⊏ b
               → S Z ⊏ c
               → S b ⊑ b ×B c
increment-⊑-×B b (S c) h l = ⊑-trans _ _ _ I II
 where
  I : S b ⊑ S (b ×B c)
  I = S-is-monotonic b (b ×B c) (×B-inflationary-left b c (S-reflects-⊏ Z c l))

  II : S (b ×B c) ⊑ (b ×B c) +B b
  II = +B-monotonic-right (b ×B c) (S Z) b (⊏-implies-S-⊑ Z b h)
increment-⊑-×B b (L ϕ) h (e , m , ◂-pick ϕ i n) =
  ⊑-trans _ _ _ I II
 where
  I : S b ⊑ b ×B ϕ i
  I = increment-⊑-×B b (ϕ i) h (e , m , n)

  II : b ×B ϕ i ⊑ L (λ i → b ×B ϕ i)
  II = L-is-upper-bound (λ i → b ×B ϕ i) i

\end{code}

\section{Properties of Exponentiation}

TODO talk about results

\begin{code}

0-powers-are-1 : (b : B) → S Z ≈ b ^B Z
0-powers-are-1 Z     = S≈ Z≈
0-powers-are-1 (S b) = 0-powers-are-1 b
0-powers-are-1 (L ϕ) = 0-powers-are-1 (ϕ zero)

--foo : (b c : B) → Z ⊒⊑ c → S Z ⊒⊑ b ^B c
--foo b Z     h = S-⊑ Z Z (S Z) (Z-⊑ Z) (◂-stop Z≈) , S-⊑ Z Z (S Z) (pr₁ h) (◂-stop Z≈)
--foo b (S c) h = 𝟘-elim {!!}
--foo b (L ϕ) h = {!!}

data SubtreeOf_IndexedBy_ (b : B) : B → 𝓤₀ ̇ where
 1-tree : (c : B)
        → c ◂ b
        → SubtreeOf b IndexedBy (S Z)

 S-tree : {c : B} (d : B)
        → SubtreeOf b IndexedBy c
        → d ◂ b
        → SubtreeOf b IndexedBy (S c)

 L-tree : (ϕ : ℕ → B)
          (n : ℕ)
        → SubtreeOf b IndexedBy (ϕ n)
        → SubtreeOf b IndexedBy (L ϕ)

join-subtrees : {b c : B} → SubtreeOf b IndexedBy c → B
join-subtrees {b}       (1-tree d h)    = d
join-subtrees {b} {S c} (S-tree d ds h) = ((b ^B c) ×B d) +B join-subtrees ds
join-subtrees {b}       (L-tree ϕ n ts) = join-subtrees ts

join-subtrees-⊏-^B : {b c : B}
                   → (ts : SubtreeOf b IndexedBy c)
                   → join-subtrees ts ◂ (b ^B c)
join-subtrees-⊏-^B {b} (1-tree c h) = ≈-preserves-◂-right h (1-left-unit-×B b)
join-subtrees-⊏-^B {b} {S c} (S-tree d ds h) =
 subtree-of-×B (b ^B c) b (join-subtrees ds) d (join-subtrees-⊏-^B ds) h
join-subtrees-⊏-^B (L-tree ϕ n ts) =
 ◂-pick _ n (join-subtrees-⊏-^B ts)

0⊏-is-decidable : B → 𝓤₀ ̇
0⊏-is-decidable b = (c : B) → c ◂ b → Z ⊏ c + Z ⊒⊑ c

--^B-inflationary-right : (b c : B)
--                      → 0⊏-is-decidable c
--                      → S Z ⊏ b
--                      → c ⊑ b ^B c
--^B-inflationary-right b Z     h l = Z-⊑ (S Z)
--^B-inflationary-right b (S c) h l =
--  cases
--   (λ m → ⊑-trans _ _ _ (I1 m) II1)
--   {!!}
--   (h c (◂-stop (≈-refl c)))
-- where
--  h' : 0⊏-is-decidable c
--  h' c m = h c (◂-continue m)
--
--  I1 : Z ⊏ c → S c ⊑ c ×B b
--  I1 m = increment-⊑-×B c b m l
--
--  II1 : c ×B b ⊑ (b ^B c) ×B b
--  II1 = ×B-monotonic-left c b (b ^B c)
--         (^B-inflationary-right b c h' l)
--
--  I2 : Z ⊒⊑ c → S c ⊑ (b ^B c) ×B b
--  I2 m = {!!}
--   where
--    I : S c ⊑ S Z
--    I = S-is-monotonic _ _ (pr₂ m)
--
--    II : S Z ⊑ b
--    II = ⊏-implies-⊑ _ _ l
--
--    III : b ⊑ S Z ×B b
--    III = ≈-preserves-⊑-left (⊑-refl (S Z ×B b)) (≈-sym (1-left-unit-×B b))
--
--    IV : S Z ×B b ⊑ (b ^B c) ×B b
--    IV = ×B-monotonic-left (S Z) b (b ^B c)
--          (⊑-trans _ _ _ {!!} {!!})

--^B-inflationary-right b (L ϕ) h l =
--  L-⊑ ϕ (L (λ i → b ^B ϕ i))
--   (λ i → ⊑-trans _ _ _
--    (^B-inflationary-right b (ϕ i) (h' i) l)
--    (L-is-upper-bound (λ i → b ^B ϕ i) i))
-- where
--  h' : (i : ℕ) → 0⊏-is-decidable (ϕ i)
--  h' i d m = h d (◂-pick ϕ i m)

-- IDEA: define "subtype" of brouwer trees with only limits of strictly
-- increasing trees. All arithmetic operations should preserve this. So namely
-- all towers of ω will obey this and this might help in proofs.
--
-- (due to Nicolai Kraus)

\end{code}

\subsection{Fixed Points of Exponentiation}

TODO come up with results we need. make it general for all fixed points?

\begin{code}

{--

S-preserves-⊏-ε₀ : (b : B) → b ⊏ ε₀ → S b ⊏ ε₀
S-preserves-⊏-ε₀ b (pick _ n p , h) =
  ⊏-and-⊑-implies-⊏ _ _ _ III IV
  where
   ω-greater-than-1 : S Z ⊏ ω
   ω-greater-than-1 = pick finite 2 (stop (S Z)) , S-⊑ Z (S Z) (stop Z) (Z-⊑ Z)

   I : S b ⊑ ω-tower n
   I = ⊏-implies-S-⊑ _ _ (⊑-and-⊏-implies-⊏ _ _ _ h (path-to-ordinal-⊏ p))

   II : ω-tower n ⊏ ω ^B ω-tower n
   II = {!!}

   III : S b ⊏ ω-tower (succ n)
   III = ⊑-and-⊏-implies-⊏ _ _ _ I II

   IV : ω-tower (succ n) ⊑ ε₀
   IV = L-is-upper-bound ω-tower (succ n)

--}

\end{code}

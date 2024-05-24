--------------------------------------------------------------------------------
authors:      ["Bruno Paiva"]
date-started: 2024-05-22
--------------------------------------------------------------------------------
\begin{code}

{-# OPTIONS --allow-unsolved-metas --without-K #-}

open import MLTT.Spartan
open import Ordinals.Brouwer
open import Ordinals.BrouwerArithmetic
open import Ordinals.BrouwerOrdering

module Ordinals.BrouwerArithmeticProperties where

\end{code}

First we see how to extend paths of a single summand to paths of the
sum of two ordinals.

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

With these extensions of paths we can then prove monotonicity of addition.

\begin{code}

Z-left-unit-+B : (b : B) → b ＝ Z +B b
Z-left-unit-+B Z     = refl
Z-left-unit-+B (S b) = ap S (Z-left-unit-+B b)
Z-left-unit-+B (L ϕ) = ap L {!!} -- requires function extensionality

Z-right-unit-+B : (b : B) → b ＝ b +B Z
Z-right-unit-+B b = refl

+B-inflationary-right : (b c : B) → c ⊑ (b +B c)
+B-inflationary-right b Z     = Z-⊑ _
+B-inflationary-right b (S c) = S-⊑ _ _ (stop (b +B c)) (+B-inflationary-right b c)
+B-inflationary-right b (L ϕ) =
 L-⊑ _ _ (λ i → ⊑-trans _ _ _
                 (L-is-upper-bound ϕ i)
                 (L-is-monotonic _ _ (λ j → +B-inflationary-right b (ϕ j))))

+B-inflationary-left : (b c : B) → b ⊑ (b +B c)
+B-inflationary-left b c =
 sufficient-path-condition-for-⊑ b (b +B c)
  (λ p → extend-path-left-+B b c p , extend-path-left-+B-correct b c p)

+B-strictly-inflationary-right : (b c : B) → Z ⊏ c → b ⊏ (b +B c)
+B-strictly-inflationary-right b c (p , _) =
 extend-path-right-+B b c p ,
 transport (b ⊑_) (extend-path-right-+B-correct b c p) (+B-inflationary-left b (Path-to-ordinal p))

+B-monotonic-left : (b c d : B) → c ⊑ d → (b +B c) ⊑ (b +B d)
+B-monotonic-left b Z d h = +B-inflationary-left b d
+B-monotonic-left b (S c) d (S-⊑ c d p h) =
 S-⊑ (b +B c) (b +B d) (extend-path-right-+B b d p)
  (transport ((b +B c) ⊑_)
   (extend-path-right-+B-correct b d p)
   (+B-monotonic-left b c (Path-to-ordinal p) h))
+B-monotonic-left b (L ϕ) d h =
 L-⊑ (λ i → b +B ϕ i) (b +B d)
  (λ i → +B-monotonic-left b (ϕ i) d
   (⊑-trans (ϕ i) (L ϕ) d (L-is-upper-bound ϕ i) h))

+B-strictly-monotonic-left : (b c d : B) → c ⊏ d → (b +B c) ⊏ (b +B d)
+B-strictly-monotonic-left b c d (p , h) =
 extend-path-right-+B b d p ,
 transport ((b +B c) ⊑_)
  (extend-path-right-+B-correct b d p)
  (+B-monotonic-left b c (Path-to-ordinal p) h)

-- TODO +B-monotonic-right

\end{code}

Multiplication

\begin{code}

extend-path-left-×B : (b c : B) → PathThroughS b → Z ⊏ c  → PathThroughS (b ×B c)
extend-path-left-×B b (S Z)     p h = extend-path-right-+B Z b p
extend-path-left-×B b (S (S c)) p h =
 extend-path-left-+B ((b ×B c) +B b) b
  (extend-path-left-×B b (S c) p (stop c , Z-⊑ c))
extend-path-left-×B b (S (L ϕ)) p (stop (L ϕ) , h) =
 extend-path-right-+B (L (λ i → b ×B ϕ i)) b p -- bad because we cannot decide if L ϕ is 'equal' to 0
extend-path-left-×B b (S (L ϕ)) p (continue (pick ϕ n q) , h) =
 extend-path-left-+B (L (λ i → b ×B ϕ i)) b
  (pick (λ i → b ×B ϕ i) n (extend-path-left-×B b (ϕ n) p (q , h)))
extend-path-left-×B b (L ϕ) p (pick ϕ n q , h) =
 pick (λ i → b ×B ϕ i) n (extend-path-left-×B b (ϕ n) p (q , h))

-- Cannot guarantee that we will get exactly Path-to-ordinal p as that would
-- require being able to decide when L ϕ represents the same ordinal as Z
extend-path-left-×B-correct : (b c : B) (p : PathThroughS b) (h : Z ⊏ c)
                            → Path-to-ordinal p ⊑ Path-to-ordinal (extend-path-left-×B b c p h)
extend-path-left-×B-correct b (S Z) p h =
 transport (Path-to-ordinal p ⊑_)
  (extend-path-right-+B-correct Z b p)
  (+B-inflationary-right Z (Path-to-ordinal p))
extend-path-left-×B-correct b (S (S c)) p h =
 transport (Path-to-ordinal p ⊑_)
  (extend-path-left-+B-correct ((b ×B c) +B b) b
   (extend-path-left-×B b (S c) p (stop c , Z-⊑ c)))
  (extend-path-left-×B-correct b (S c) p (stop c , Z-⊑ c))
extend-path-left-×B-correct b (S (L ϕ)) p (stop (L ϕ) , h) =
 transport (Path-to-ordinal p ⊑_)
  (extend-path-right-+B-correct (L (λ i → b ×B ϕ i)) b p)
  (+B-inflationary-right (L (λ i → b ×B ϕ i)) (Path-to-ordinal p))
extend-path-left-×B-correct b (S (L ϕ)) p (continue (pick ϕ n q) , h) =
 transport (Path-to-ordinal p ⊑_)
  (extend-path-left-+B-correct (L (λ i → b ×B ϕ i)) b
   (pick (λ i → b ×B ϕ i) n (extend-path-left-×B b (ϕ n) p (q , h))))
  (extend-path-left-×B-correct b (ϕ n) p (q , h))
extend-path-left-×B-correct b (L ϕ) p (pick ϕ n q , h) =
 extend-path-left-×B-correct b (ϕ n) p (q , h)

extend-path-right-×B : (b c : B) → PathThroughS c → Z ⊏ b → PathThroughS (b ×B c)
extend-path-right-×B b (S c) (stop c) (q , h) =
 extend-path-right-+B (b ×B c) b q
extend-path-right-×B b (S c) (continue p) h =
 extend-path-left-+B (b ×B c) b (extend-path-right-×B b c p h)
extend-path-right-×B b (L ϕ) (pick ϕ n p) h =
 pick (λ i → b ×B ϕ i) n (extend-path-right-×B b (ϕ n) p h)

-- Also cannot guarantee a correctness result involving ＝ but we can use ⊑
-- instead
extend-path-right-×B-correct : (b c : B) (p : PathThroughS c) (h : Z ⊏ b)
                             →  b ×B Path-to-ordinal p ⊑ Path-to-ordinal (extend-path-right-×B b c p h)
extend-path-right-×B-correct b (S c) (stop c) (q , h) =
 transport (b ×B c ⊑_)
  (extend-path-right-+B-correct (b ×B c) b q)
  (+B-inflationary-left (b ×B c) (Path-to-ordinal q))
extend-path-right-×B-correct b (S c) (continue p) h =
 transport (b ×B Path-to-ordinal p ⊑_)
  (extend-path-left-+B-correct (b ×B c) b (extend-path-right-×B b c p h))
  (extend-path-right-×B-correct b c p h)
extend-path-right-×B-correct b (L ϕ) (pick ϕ n p) h =
 extend-path-right-×B-correct b (ϕ n) p h

×B-monotonic-left : (b c d : B) → c ⊑ d → (b ×B c) ⊑ (b ×B d)
×B-monotonic-left b Z     d h = Z-⊑ (b ×B d)
×B-monotonic-left b (S c) d h = {!!}
×B-monotonic-left b (L ϕ) d h = {!!}


\end{code}

Results we need for the logical relation

\begin{code}

⊏-ε₀-implies-S-⊏-ε₀ : (b : B) → b ⊏ ε₀ → S b ⊏ ε₀
⊏-ε₀-implies-S-⊏-ε₀ b (pick .ω-tower n p , h) =
 pick ω-tower (succ n) q , {!!}
 where
  q : PathThroughS (ω-tower (succ n))
  q = {!!}

\end{code}

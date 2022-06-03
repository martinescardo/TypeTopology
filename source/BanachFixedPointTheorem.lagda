Todd Waugh Ambridge, 5th October 2020.

A version of the Banach fixed-point theorem for ultracloseness spaces.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-FunExt

module BanachFixedPointTheorem (fe : FunExt) where

open import SpartanMLTT
open import GenericConvergentSequence hiding (min)
open import CoNaturalsArithmetic fe
open import Closeness fe
open import NaturalsOrder
open import UF-Miscelanea
open import NaturalNumbers-Properties
open import OrderNotation
open import CanonicalMapNotation

\end{code}

(*) Definitions.

First we define a 'ultracloness space', which is a type equipped with
a cometric, but rather than triangle equality we have the ultrametric
property.

 A ultracloness space is a type X,
 equipped with a binary function c ꞉ X → X → ℕ∞,
 such that:

  (i)   Indistinguishable elements of X are equal,
        i.e. ∀ x y , c x y ≡ ∞ → x ≡ y

  (ii)  Every element of X is self-indistinguishable,
        i.e. ∀ x , c x x ≡ ∞

  (iii) The binary function is symmetric,
        i.e. ∀ x y , c x y ≡ c y x

  (iv)  The ultrametric property holds,
        i.e. ∀ x y z , min (c x y , c y z) ≤ c x z

In the code, we refer to the underlying type of a ultracloness
space (CUT) C as ⟨ C ⟩.
A CUT C is nonempty simply if we can exhibit a single element of ⟨ C ⟩.

\begin{code}

ClosenessSpace : 𝓤 ⁺ ̇
ClosenessSpace {𝓤} = Σ X ꞉ 𝓤 ̇ , Σ c ꞉ (X → X → ℕ∞) , is-closeness c

⟨_⟩ CUT-Nonempty : ClosenessSpace → 𝓤 ̇
⟨ X , _ ⟩ = X
CUT-Nonempty = ⟨_⟩

\end{code}

Given a CUT C, the definition of a Cauchy sequence is as expected.

 A sequence s ꞉ (ℕ → ⟨ C ⟩) is Cauchy if for all ε ꞉ ℕ, there is an N ꞉ ℕ,
 such that for all m,n < N, we have ε < c s(m) s(n).

\begin{code}

CUT-CauchySequence : ClosenessSpace → 𝓤 ̇
CUT-CauchySequence (X , c , _) = Σ s ꞉ (ℕ → X) , Π ε ꞉ ℕ , Σ N ꞉ ℕ
                                 , ∀ m n → (N < m) × (N < n) → ι ε ≺ c (s m) (s n)

\end{code}

A CUT C is complete if every Cauchy sequence on C has a limit.

\begin{code}

has-limit : {X : 𝓤 ̇ } → (ℕ → X) → 𝓤 ̇
has-limit {X} s = Σ i ꞉ ℕ , Π n ꞉ ℕ , (i ≤ n → s n ≡ s i)

CUT-Complete : ClosenessSpace → 𝓤 ̇
CUT-Complete C = Π (s , _) ꞉ CUT-CauchySequence C , has-limit s

\end{code}

Finally, we give the definition of a contractive mapping for CUTs.

A map X → X' of metric spaces (X,d) and (X',d') is contractive if
there is r ∈ [0,1) such that for all x,y:X, we have

  d'(fx,fy) ≤ r·d(x,y).

Now, given a cometric space (X,c), we get a metric space (X,d) with d defined by

  d(x,y) = 2^{-c(x,y)}

with the usual convention that 2^{-∞} = 0. The converse is not always
possible. But, if (X,d) is ultrametric, then we can define a cometric
c from d by

 c(x,y) = sup { n:ℕ∞ | d(x,y)<2^{-n} }.

So, to translate the definition of contractibility to metric to
cometric, we need:

 (1) Restrict to particular contraction factors, namely of the form
     r=2^{-n}.

 (2) Define an operation (this set of contraction factors)×ℕ∞ → ℕ∞
     corresponding to multiplication. But actually, division by 2 is
     enough. And division by two corresponds to the successor function
     on ℕ∞.

     0  1   2   3   4   ⋯ ∞
     1 1/2 1/4 1/8 1/16   0

So the definition of contractive map for cometric spaces is
that there is an n > 0 such that,

 c(fx,fy) ≽ succ^{n} c(x,y).

\begin{code}

CUT-ContractionMapping : ClosenessSpace → 𝓤 ̇
CUT-ContractionMapping (X , c , _)
 = Σ T ꞉ (X → X) , Σ n ꞉ ℕ , (0 < n) × (∀ x y → (Succ ^ n) (c x y) ≼ c (T x) (T y))

\end{code}

(*) Lemma.

Given a type X, if the  sequence consisting of
iterations of f : X → X with starting point
x₀ ꞉ X has a limit, then it has a fixed point.

\begin{code}

iter : {X : 𝓤 ̇ } → X → (X → X) → (ℕ → X)
iter x₀ f n = (f ^ n) x₀

has-fixed-point : {X : 𝓤 ̇ } → (X → X) → 𝓤 ̇
has-fixed-point {𝓤} {X} f = Σ x* ꞉ X , f x* ≡ x*

limits-yield-fixed-points : {X : 𝓤 ̇ }
                          → (f : X → X)
                          → (x₀ : X)
                          → has-limit (iter x₀ f)
                          → has-fixed-point f
limits-yield-fixed-points f x₀ (n , l) = iter x₀ f n
                                       , l (succ n) (≤-succ n)

\end{code}

(*) Theorem.

We now prove the CUT version of the Banach fixed-point theorem.

The proof amounts to showing that the sequence of iterations of
a contraction mapping with some starting point in a complete CUT
has a limit. This is done by using the completeness property to
show that such a sequence is Cauchy.

\begin{code}

BanachFixedPointTheorem : (C : ClosenessSpace {𝓤})
                        → CUT-Nonempty C
                        → CUT-Complete C
                        → ((T , _) : CUT-ContractionMapping C)
                        → has-fixed-point T
BanachFixedPointTheorem (X , c , p) x₀ complete (T , succ k , _ , r)
 = limits-yield-fixed-points T x₀ limit
 where
  s : ℕ → X
  s = iter x₀ T
  limit : has-limit s
  limit = complete (s , λ ε → ε , γ ε)
   where
    γ : Π ε ꞉ ℕ , ((m n : ℕ) → (ε < m) × (ε < n) → ι ε ≺ c (s m) (s n))
    γ ε (succ m) (succ n) (ε<sm , ε<sn)
      = ≺≼-gives-≺ (ι ε) ((Succ ^ succ k) (c (s m) (s n))) (c (T (s m)) (T (s n)))
                   (q k ε (ε<sm , ε<sn)) (r (s m) (s n))
     where
      q : (k : ℕ) (ε : ℕ) → (ε < succ m) × (ε < succ n)
        → ι ε ≺ (Succ ^ succ k) (c (s m) (s n))
      q 0 0 _ = 0 , refl , refl
      q 0 (succ ε) (ε<sm , ε<sn)
       = ≺-Succ (ι ε) (c (s m) (s n)) (γ ε m n (ε<sm , ε<sn))
      q (succ k) ε ε<
       = ≺-Succ-r (ι ε) ((Succ ^ succ k) (c (s m) (s n))) (q k ε ε<)

\end{code}

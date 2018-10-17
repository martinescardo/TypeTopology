Martin Escard0, 11th October 2018.

The following is based on a well-known argument,

 Thierry Coquand, The paradox of trees in type theory
 BIT Numerical Mathematics, March 1992, Volume 32, Issue 1, pp 10–14
 https://pdfs.semanticscholar.org/f2f3/30b27f1d7ca99c2550f96581a4400c209ef8.pdf

(see also http://www.cs.nott.ac.uk/~psztxa/g53cfr/l20.html/l20.html),
but phrased in terms of LFPT.

\begin{code}

{-# OPTIONS --without-K --type-in-type --exact-split #-}

module Type-in-Type-False where

open import SpartanMLTT
open import LawvereFPT

Y : {X : Set} → (X → X) → X
Y {X} f = pr₁ (γ f)
 where
  data 𝕎 : Set where
   sup : (T : Set) → (T → 𝕎) → 𝕎
  e : 𝕎 → 𝕎 → Set
  e (sup T φ) w = Σ \(t : T) → φ t ≡ w
  R : 𝕎
  R = sup (Σ \(w : 𝕎) → e w w → X) pr₁
  A : Set
  A = e R R
  r : A → (A → X)
  r ((.R , f) , refl) = f
  s : (A → X) → A
  s f = (R , f) , refl
  rs : (f : A → X) → r (s f) ≡ f
  rs f = refl
  γ : (f : X → X) → Σ \(x : X) → x ≡ f x
  γ = retract-version.LFPT (r , s , rs)

\end{code}

Then Y is a definitional fixed-point combinator (because the function
s is a definitional section of the function r):

\begin{code}

Y-is-fp-combinator : {X : Set} (f : X → X) → f (Y f) ≡ Y f
Y-is-fp-combinator f = refl

contradiction' : 𝟘
contradiction' = Y id

\end{code}

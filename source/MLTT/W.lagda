W-types.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module MLTT.W where

open import MLTT.Spartan

data W {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
 ssup : (x : X) → (A x → W X A) → W X A

module _ {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } where

 W-root : W X A → X
 W-root (ssup x f) = x

 W-forest : (w : W X A) → A (W-root w) → W X A
 W-forest (ssup x f) = f

 W-induction : (P : W X A → 𝓥 ̇ )
             → ((x : X) (f : A x → W X A)
                       → ((a : A x) → P (f a)) → P (ssup x f))
             → (w : W X A) → P w
 W-induction P g = h
  where
   h : (w : W X A) → P w
   h (ssup x f) = g x f (λ x → h (f x))

\end{code}

The record version of W in case we need it:

\begin{code}

record W' {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
 inductive
 constructor
  ssup
 field
  pr₁ : X
  pr₂ : A pr₁ → W' X A

\end{code}

Indexed version of W:

\begin{code}

data Wᵢ {𝓤 𝓥 𝓦 : Universe}
        (I : 𝓦 ̇ )
        (A : 𝓤 ̇ )
        (t : A → I)
        (B : A → 𝓥 ̇ )
        (s : (a : A) → B a → I)
      : I → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 where
 ssup : (a : A) → ((b : B a) → Wᵢ I A t B s (s a b)) → Wᵢ I A t B s (t a)

\end{code}

E.g. for typed terms:

  I    type of "types"
  A    type of operations
  t    type of the result
  B    arity assignment
  s    type of arguments

W-types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module W where

open import SpartanMLTT

data W {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
 sup : (x : X) → (A x → W X A) → W X A

\end{code}

The record version of W in case we need it:

\begin{code}

record W' {𝓤 𝓥 : Universe} (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇ where
 inductive
 constructor
  sup
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
 sup : (a : A) → ((b : B a) → Wᵢ I A t B s (s a b)) → Wᵢ I A t B s (t a)

\end{code}

E.g. for typed terms:

  I    type of "types"
  A    type of operations
  t    type of the result
  B    arity assignment
  s    type of arguments

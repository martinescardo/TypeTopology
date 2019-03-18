W-types.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module W where

open import SpartanMLTT

data W {𝓤 𝓥 : Universe} {X : 𝓤 ̇} (Y : X → 𝓥 ̇ ) : 𝓤 ⊔ 𝓥 ̇  where
 sup : {x : X} → (Y x → W Y) → W Y

\end{code}

Indexed version:

\begin{code}

data W' {𝓤 𝓥 𝓦 : Universe}
        (I : 𝓦 ̇ )
        (A : 𝓤 ̇ )
        (t : A → I)
        (B : A → 𝓥 ̇ )
        (s : (a : A) → B a → I)
      : I → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 where
 sup : (a : A) → ((b : B a) → W' I A t B s (s a b)) → W' I A t B s (t a)

\end{code}

For typed terms:

  I    type of "types"
  A    type of operations
  t    type of the result
  B    arity assignment
  s    type of arguments

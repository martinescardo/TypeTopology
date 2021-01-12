Martin Escardo.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-FunExt-Properties where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-LeftCancellable
open import UF-FunExt
open import UF-UniverseEmbedding

\end{code}

Taken from the MGS 2019 lecture notes:

\begin{code}

lower-dfunext : ∀ 𝓦 𝓣 𝓤 𝓥 → DN-funext (𝓤 ⊔ 𝓦) (𝓥 ⊔ 𝓣) → DN-funext 𝓤 𝓥
lower-dfunext 𝓦 𝓣 𝓤 𝓥 fe {X} {A} {f} {g} h = p
 where
  A' : Lift 𝓦 X → 𝓥 ⊔ 𝓣 ̇
  A' y = Lift 𝓣 (A (lower y))

  f' g' : Π A'
  f' y = lift 𝓣 (f (lower y))
  g' y = lift 𝓣 (g (lower y))

  h' : f' ∼ g'
  h' y = ap (lift 𝓣) (h (lower y))

  p' : f' ≡ g'
  p' = fe h'

  p : f ≡ g
  p = ap (λ f' x → lower (f' (lift 𝓦 x))) p'

\end{code}

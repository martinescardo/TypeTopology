Martin Escardo 25th October 2018.

The type of partial elements of a type (or lifting). Constructions and
properties of lifting are discussed in other modules.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import SpartanMLTT

module Lifting (𝓣 : Universe) where

open import UF-Subsingletons hiding (⊥)

𝓛 : 𝓤 ̇ → 𝓤 ⊔ 𝓣 ⁺ ̇
𝓛 X = Σ \(P : 𝓣 ̇) → (P → X) × is-prop P

is-defined : {X : 𝓤 ̇} → 𝓛 X → 𝓣 ̇

is-defined (P , i , φ) = P

being-defined-is-a-prop : {X : 𝓤 ̇} (l : 𝓛  X) → is-prop (is-defined l)
being-defined-is-a-prop (P , φ , i) = i

value : {X : 𝓤 ̇} (l : 𝓛  X) → is-defined l → X
value (P , φ , i) = φ

\end{code}

The "total" elements of 𝓛 X:

\begin{code}

η : {X : 𝓤 ̇} → X → 𝓛 X
η x = 𝟙 , (λ _ → x) , 𝟙-is-prop

\end{code}

Its "undefined" element:

\begin{code}

⊥ : {X : 𝓤 ̇} → 𝓛 X
⊥ = 𝟘 , unique-from-𝟘 , 𝟘-is-prop

\end{code}

Size matters.

As one can see from the definition of 𝓛, we have:

\begin{code}

the-universe-of-𝓛 : (X : 𝓤 ̇) → universe-of (𝓛 X) ≡ 𝓣 ⁺ ⊔ 𝓤
the-universe-of-𝓛 X = refl

\end{code}

So 𝓛 increases the size of its argument, in general. However, if the
argument is in 𝓣 ⁺ ⊔ 𝓤, then the size doesn't increase:

\begin{code}

𝓛-universe-preservation : (X : 𝓣 ⁺ ⊔ 𝓤 ̇) → universe-of (𝓛 X) ≡ universe-of X
𝓛-universe-preservation X = refl

\end{code}

In particular, after the first application of 𝓛, further applications
don't increase the size:

\begin{code}

the-universe-of-𝓛𝓛 : (X : 𝓤 ̇) → universe-of(𝓛(𝓛 X)) ≡ universe-of (𝓛 X)
the-universe-of-𝓛𝓛 X = refl

\end{code}

TODO. Assuming weak propositional resizing ...

\begin{code}

open import UF-Resizing
open import UF-Equiv

\end{code}

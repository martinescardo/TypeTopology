We define the notation for type universes used in the MGS notes.

Probably you should try to understand this only after you used
universes for a while as in the MGS-2019-Univalent-Mathematics notes.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module Univalent-Mathematics-in-Agda-Universes where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to 𝓤₀             -- Our first universe is called 𝓤₀
          ; lsuc to _⁺              -- The universe after 𝓤 is 𝓤 ⁺
          ; Level to Universe       -- We speak of universes rather than of levels.
          ; Setω to 𝓤ω
          )

\end{code}

The elements of Universe are universe names. Given a name 𝓤, the
universe itself will be written 𝓤 ̇ with a deliberately almost
invisible superscript dot (if you are not seeing it, that's great.

We actually need to define this notation, because traditionally in
Agda if one uses ℓ for a universe level, then Set ℓ is the type of
types of level ℓ. However, this notation is not good for univalent
foundations, because not all types are sets.

The following should be the only use of the Agda keyword 'Set' in
these notes.

\begin{code}

Type = λ ℓ → Set ℓ

_̇ : (𝓤 : Universe) → Type (𝓤 ⁺)
𝓤 ̇ = Type 𝓤

\end{code}

This says that given the universe level 𝓤, we get the type universe 𝓤 ̇,
which lives in the next next type universe universe Type (𝓤 ⁺). So the
superscript dot notation is just a synonym for Type, which is just a
synonym for Set, which means type in Agda. If you find this confusing,
it is because it is confusing.

We name a few of the initial few universes:

\begin{code}

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺

\end{code}

The following is sometimes useful:

\begin{code}

universe-of : {𝓤 : Universe} (X : 𝓤 ̇) → Universe
universe-of {𝓤} X = 𝓤

\end{code}

Fixities:

\begin{code}

infix  1 _̇

\end{code}

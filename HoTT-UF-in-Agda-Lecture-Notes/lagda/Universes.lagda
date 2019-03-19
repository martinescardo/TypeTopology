---
layout: default
title : Universes (Introduction to Univalent Foundations of Mathematics with Agda)
date : 2019-03-04
---
## <a name="lecturenotes">Introduction to Univalent Foundations of Mathematics with Agda</a>

[<sub>Table of contents ⇑</sub>](toc.html#contents)
## Universes

We define our notation for type universes used in these notes, which
is different from the standard Agda notation, but closer the standard
notation in HoTT/UF.

Readers unfamiliar with Agda should probably try to understand this
only after doing some [MLTT in Agda](MLTT-Agda) and [HoTT/UF in
Agda](HoTT-UF-Agda).

\begin{code}
{-# OPTIONS --without-K --exact-split --safe #-}

module Universes where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to 𝓤₀       -- Our first universe is called 𝓤₀
          ; lsuc to _⁺        -- The universe after 𝓤 is 𝓤 ⁺
          ; Level to Universe -- We speak of universes rather than of levels.
          ; Setω to 𝓤ω        -- There is a universe 𝓤ω strictly above 𝓤₀ 𝓤₁ ⋯ 𝓤ₙ ⋯
          )
\end{code}

The elements of `Universe` are universe names. Given a name `𝓤`, the
universe itself will be written `𝓤 ̇` &nbsp; in these notes, with a
deliberately almost invisible superscript dot.

We actually need to define this notation, because traditionally in
Agda if one uses `ℓ` for a universe level, then `Set ℓ` is the type of
types of level `ℓ`. However, this notation is not good for univalent
foundations, because not all types are sets.

The following should be the only use of the Agda keyword `Set` in
these notes.

\begin{code}
Type = λ ℓ → Set ℓ

_̇   : (𝓤 : Universe) → Type (𝓤 ⁺)

𝓤 ̇  = Type 𝓤
\end{code}

This says that given the universe level `𝓤`, we get the type universe
`𝓤 ̇`, which lives in the next next type universe universe `𝓤 ⁺`. So
the superscript dot notation is just a (postfix) synonym for (prefix)
`Type`, which is just a synonym for `Set`, which means type in Agda.

We name a few of the initial few universes:

\begin{code}
𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺
\end{code}

The following is sometimes useful:

\begin{code}
universe-of : {𝓤 : Universe} (X : 𝓤 ̇ ) → Universe
universe-of {𝓤} X = 𝓤
\end{code}

Fixities:

\begin{code}
infix  1 _̇
\end{code}

[<sub>Table of contents ⇑</sub>](toc.html#contents)

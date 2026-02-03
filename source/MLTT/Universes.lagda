Martin Escardo, original date unknown.

This file defines our notation for type universes.

Our convention for type universes here is the following.

When the HoTT book writes

  X : 𝓤

we write

  X : 𝓤 ̇

although we wish we could use the same notation as the HoTT book. This
would be possible if Agda had implicit coercions like other proof
assistants such as Coq and we declared upperscript dot as an implicit
coercion.

Our choice of an almost invisible upperscript dot is deliberate. If
you don't see it, then that's better.

Officially, in our situation, 𝓤 is a so-called universe level, with
corresponding universe

  𝓤 ̇

but we rename `Level` to `Universe` so that we can write e.g.

  foo : {𝓤 : Universe} (X : 𝓤 ̇ ) → X ＝ X

Moreover, we declare

  𝓤 𝓥 𝓦 𝓣 𝓤' 𝓥' 𝓦' 𝓣'

as `variables` so that the above can be shortened to the following
with exactly the same meaning:

  foo : (X : 𝓤 ̇ ) → X ＝ X

Then the definition of `foo` can be

  foo X = refl

using the conventions for the identity type in another file in this
development, or, if we want to be explicit (or need, in similar
definitions, to refer to 𝓤), it can be

  foo {𝓤} X = refl {𝓤} {X}

**Important**. We also have the problem of *visualizing* this notation
in both emacs and the html rendering of our Agda files in web
browsers.

First of all, we define upperscript dot as a postfix operator.
Therefore, it is necessary to write a space between 𝓤 and the
upperscript dot following it, by the conventions adopted by Agda.

Secondly, it is the nature of unicode that upperscript dot is (almost)
always displayed at the *top* of the previous character, which in our
case is a space. Therefore, there is no visible space between 𝓤 and
the upperscript dot in

  𝓤 ̇

but it does have to be typed, as otherwise we get

  𝓤̇

both in emacs and the html rendering, which Agda interprets as a
single token.

Moreover, Agda doesn't require the upperscript dot to have a space
when it is followed by a closing bracket. Compare

  (X : 𝓤 ̇)

and

  (X : 𝓤 ̇ )

in both emacs and their html rendering

  https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Universes.html

which here are typed, respectively, as

  open bracket, X, colon, 𝓤, space, upperscript dot, close bracket

and

  open bracket, X, colon, 𝓤, space, upperscript dot, space, close bracket.

You will see that the dot is placed at the top the closing bracket in
the second example in its html version, but not in its emacs version.

So we always need a space between the upperscript dot and the closing
bracket.

Another pitfall is that some TypeTopology contributors, including
yours truly, often end up accidentally writing **two spaces** before
the closing brackets, to avoid this, which we don't want, due to the
above weirdness. Make sure you type exactly one space after the dot
and before the closing bracket. More precisely, we want the first
option, namely

  open bracket, X, colon, 𝓤, space, upperscript dot, close bracket

I really wish Agda had implicit coercions and we could write 𝓤 rather
than the more cumbersome 𝓤 ̇. We can't really blame unicode here.

If you are a TypeTopology contributor, make sure you read the above
both in emacs in its agda version and in a web browser in its html
version.

  https://www.cs.bham.ac.uk/~mhe/TypeTopology/MLTT.Universes.html

to understand this visualization problem and its solution in practice.

Not all web browsers exhibit the same problem, though, which is even
more annoying. The current solution works for all browsers I tested
on 5th September 2024 (Firefox, Chrome, Chromium, Safari).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module MLTT.Universes where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to 𝓤₀
          ; lsuc to _⁺
          ; Level to Universe
          ; Setω to 𝓤ω
          )

variable
 𝓤 𝓥 𝓦 𝓣
  𝓤' 𝓥' 𝓦' 𝓣'
  𝓥₀ 𝓦₀ 𝓣₀
  𝓥₁ 𝓦₁ 𝓣₁
  𝓥₂ 𝓦₂ 𝓣₂ : Universe

\end{code}

The following should be the only use of the Agda keyword `Set` in this
development:

\begin{code}

_̇ : (𝓤 : Universe) → Set (𝓤 ⁺)
𝓤 ̇ = Set 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

\end{code}

Precedences:

\begin{code}

infix  1 _̇

\end{code}

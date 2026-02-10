Lane Biocini
21 January 2026

The generators s (order 2) and r (order 3) as functions on PSL2Z.
These are defined by pattern matching on the Cayley graph structure,
and the key relations emerge definitionally:

  s (s x) computes to x    (s² = 1)
  r (r (r x)) computes to x (r³ = 1)

The main payoff of the mutual inductive encoding is that the group
relations hold by computation rather than requiring explicit proofs
and transport.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Groups.ModularGroup.Base where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import UF.Base
open import Groups.ModularGroup.Type

s : PSL2Z → PSL2Z
s (η e₀) = η e₁
s (η e₁) = η e₀
s (s∙ re) = θ re
s (θ re)  = s∙ re

r : PSL2Z → PSL2Z
r (η e₀)  = r∙ e₀
r (η e₁)  = r∙ e₁
r (s∙ re) = r∙ cross re
r (r∙ se) = r²∙ se
r (r²∙ se) = η se

\end{code}

Derived operations for common generator combinations. These are used
throughout the development for readability.

\begin{code}

r² sr rs : PSL2Z → PSL2Z
r² x = r (r x)
sr x = s (r x)
rs x = r (s x)

srs rsr r²s sr² : PSL2Z → PSL2Z
srs x = s (r (s x))
rsr x = r (s (r x))
r²s x = r (r (s x))
sr² x = s (r (r x))

sr²s rsr² r²sr r²sr² : PSL2Z → PSL2Z
sr²s x = s (r (r (s x)))
rsr² x = r (s (r (r x)))
r²sr x = r (r (s (r x)))
r²sr² x = r (r (s (r (r x))))

\end{code}

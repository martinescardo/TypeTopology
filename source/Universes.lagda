\begin{code}

module Universes where

open import Agda.Primitive public
  using (_⊔_)
  renaming (lzero to U₀
          ; lsuc to _′
          ; Level to Universe
          ; Setω to Uω
          )

variable
 U V W : Universe

\end{code}

The following should be the only use of the Agda keyword 'Set' in this
development:

\begin{code}

_̇ : (U : Universe) → _
U ̇ = Set U

U₁ = U₀ ′
U₂ = U₁ ′

\end{code}

Lift a type X in the universe U to a type X ↑ in the universe U ⊔
V. An element of X is of the form x ↥ for x an element of X.

\begin{code}

record _↑ {U V} (X : U ̇) : U ⊔ V ̇ where
 constructor _↥
 field _↧ : X
 infix 0 _↧

open _↑ public

infix 0 _↑
infix 0 _↥

\end{code}

precedences:

\begin{code}

infix  1 _̇

\end{code}

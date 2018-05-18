\begin{code}

module Universes where

open import Agda.Primitive using (_⊔_) renaming (lzero to U₀ ; lsuc to _′ ; Level to Universe) public

infix  0 _̇

_̇ : (U : Universe) → _
U ̇ = Set U -- This should be the only use of the Agda keyword 'Set' in this development.

U₁ = U₀ ′
U₂ = U₁ ′

\end{code}

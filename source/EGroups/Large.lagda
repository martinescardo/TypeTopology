Martin Escardo, July 2026.

This is the egroup counterpart of Groups.Large.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module EGroups.Large where

open import MLTT.Spartan
open import MLTT.List
open import UF.Size
open import Groups.Free using (module free-group-construction)
open import EGroups.Type
open import EGroups.FreeOnType

free-egroup-carrier-small-gives-generators-small :
   (A : 𝓤 ̇ )
 → ⟨ free-egroup A ⟩ is 𝓤 small
 → A is 𝓤 small
free-egroup-carrier-small-gives-generators-small {𝓤} A =
 size-contravariance η (η-has-any-size 𝓤)
 where
  open free-group-construction A

\end{code}

Notice that in the above A is assumed to live in 𝓤, while in the
following it is assumed to live in 𝓤⁺.

\begin{code}

free-egroup-is-large :
   (A : 𝓤 ⁺ ̇ )
 → is-large A
 → is-large ⟨ free-egroup A ⟩
free-egroup-is-large {𝓤} A =
 large-covariance η (η-has-any-size 𝓤)
 where
  open free-group-construction A

\end{code}

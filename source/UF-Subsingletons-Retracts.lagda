(Do we need this module?)

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Subsingletons-Retracts where

open import UF-Base
open import UF-Subsingletons
open import UF-Retracts

retract-of-singleton : ∀ {U V} {X : U ̇} {Y : V ̇} (r : X → Y)
                    → hasSection r → isSingleton X → isSingleton Y
retract-of-singleton {U} {V} {X} {Y} r (s , rs) (x , i) = r x , λ y → r x ≡⟨ ap r (i (s y)) ⟩ r (s y) ≡⟨ rs y ⟩ y ∎

\end{code}

In univalent logic, as opposed to Curry-Howard logic, a proposition is
a subsingleton or a type such that any two of its elements are
identified.

https://www.newton.ac.uk/files/seminar/20170711100011001-1009756.pdf
https://unimath.github.io/bham2017/uf.pdf

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Subsingleton-Retracts where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts

retract-of-singleton : ∀ {U V} {X : U ̇} {Y : V ̇} (r : X → Y)
                    → hasSection r → isSingleton X → isSingleton Y
retract-of-singleton {U} {V} {X} {Y} r (s , rs) (x , i) = r x , λ y → r x ≡⟨ ap r (i (s y)) ⟩ r (s y) ≡⟨ rs y ⟩ y ∎

\end{code}

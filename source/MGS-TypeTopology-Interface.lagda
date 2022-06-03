Martin Escardo. 13th January 2021

This is to be be able to call the MGS lectures notes code from
TypeTopology. This will grow as the need arises.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module MGS-TypeTopology-Interface where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv

import MGS-Equivalences
import MGS-FunExt-from-Univalence

MGS-equivs-are-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → MGS-Equivalences.is-equiv f
                      → is-equiv f
MGS-equivs-are-equivs = vv-equivs-are-equivs

equivs-are-MGS-equivs : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
                      → is-equiv f
                      → MGS-Equivalences.is-equiv f
equivs-are-MGS-equivs = equivs-are-vv-equivs

happly'-is-MGS-happly : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A)
                      → happly' f g ∼ MGS-FunExt-from-Univalence.happly f g
happly'-is-MGS-happly f g refl = refl

\end{code}

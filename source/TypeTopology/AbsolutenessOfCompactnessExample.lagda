Andrew Swan, started 13th February 2024

We demonstrate the upwards absoluteness of compactness, by using it to
give an alternative proof of the propositional Tychonoff theorem (as
proved in the module TypeTopology.PropTychonoff).

\begin{code}

{-# OPTIONS --safe --without-K #-}
open import MLTT.Spartan

import Modal.Open
import Modal.SigmaClosedReflectiveSubuniverse

import TypeTopology.AbsolutenessOfCompactness
open import TypeTopology.CompactTypes

open import UF.Base
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.PropIndexedPiSigma
open import UF.Subsingletons

module TypeTopology.AbsolutenessOfCompactnessExample
 (fe : funext 𝓤 𝓤)
 (P : 𝓤 ̇ )
 (P-is-prop : is-prop P)
 where

\end{code}

We are given a proposition P as a parameter and function
extensionality. We use this in a sequence of module imports.

First of all, we give P to the open modality module, as well as
function extensionality to get results about the open modality on P.

\begin{code}

open Modal.Open fe P P-is-prop

\end{code}

The open modality module gives us proofs that the open modality is
reflective and Σ-closed. We hand these off to the
SigmaClosedReflectiveSubuniverse module.

\begin{code}

open Modal.SigmaClosedReflectiveSubuniverse
 open-subuniverse open-is-reflective open-is-sigma-closed

\end{code}

We also hand off the open modality as a parameter to the
AbsolutenessOfCompactness module.

\begin{code}

open TypeTopology.AbsolutenessOfCompactness
 open-subuniverse open-is-reflective

\end{code}

Finally, we recall that AbsolutenessOfCompactness has a submodule that
requires the extra assumptions of function extensionality and that the
reflective subuniverse is Σ-closed and replete. We have all of these,
so we pass them on as parameters to the submodule.

\begin{code}

open WithFunExtAndRepleteSigmaClosed
 fe open-is-sigma-closed open-is-replete

\end{code}

If we apply the theorems in AbsolutenessOfCompactness directly, the
best we can get is the following non dependent version of
propositional Tychonoff.

\begin{code}

non-dependent-prop-tychonoff
 : (A : 𝓤 ̇ )
 → (P → is-compact∙ A)
 → is-compact∙ (P → A)
non-dependent-prop-tychonoff = modalities-preserve-compact

\end{code}

In order to get a new proof of propositional Tychonoff, we need to
show how to derive it from the non-dependent version.

\begin{code}

prop-tychonoff₂
 : (A : P → 𝓤 ̇ )
 → ((z : P) → is-compact∙ (A z))
 → is-compact∙ (Π A)
prop-tychonoff₂ A A-compact = ΠA-compact
 where

\end{code}

We are given a family of types A : P → 𝓤 ̇  and we aim to apply the
non-dependent version above to the product Π A. In order to do this,
there are two things to check. Firstly, we have to show that P implies
Π A is compact. This allows us to apply the non-dependent version
above, which shows that P → Π A is compact. We then need to deduce
from this that in fact Π A is compact.

The first step, of showing that P implies Π A compact, is copied
straight from the original propositional Tychonoff proof. Namely, if P
is true, as witnessed by an inhabitant z, then Π A is equivalent to A
z, and so is compact.

\begin{code}

  𝕗 : (z : P) → Π A ≃ A z
  𝕗 = prop-indexed-product fe P-is-prop

  product-locally-compact : P → is-compact∙ (Π A)
  product-locally-compact z =
   compact∙-types-are-closed-under-equiv
    (≃-sym (𝕗 z)) (A-compact z)

\end{code}

We can now apply the non dependent version above to show that P → Π A
is compact.

\begin{code}

  P→ΠA-compact : is-compact∙ (P → Π A)
  P→ΠA-compact =
   non-dependent-prop-tychonoff (Π A) product-locally-compact

\end{code}

To deduce that Π A is compact, it suffices to show that it is
equivalent to P → Π A. This can be shown directly, but we will give a
slightly more abstract proof using general results about
modalities.

First note that given z : P, we known that P is true and so every type
is modal for the open modality on P. Hence, in particular A z is
modal.

\begin{code}

  A-modal : (z : P) → is-modal (A z)
  A-modal z = P-true-implies-all-modal z (A z)

\end{code}

Since A is a family of modal types its product Π A is also modal.

\begin{code}

  ΠA-modal : is-modal (Π A)
  ΠA-modal =
   products-of-modal-types-are-modal
    fe open-is-replete P A A-modal

\end{code}

However, the fact that Π A is modal precisely tells us that the unit
map of the modality Π A → (P → Π A) is an equivalence.

Putting this together with the earlier proof that P → Π A is modal
allows us to complete the proof of the theorem.

\begin{code}

  ΠA-compact : is-compact∙ (Π A)
  ΠA-compact =
   compact∙-types-are-closed-under-equiv
    (≃-sym ((open-unit (Π A)) , ΠA-modal))
    P→ΠA-compact

\end{code}

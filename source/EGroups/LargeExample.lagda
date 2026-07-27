Martin Escardo, July 2026.

An example of a large egroup, which is what the EGroups development is for.

We instantiate the largeness theorem of the module Large with the
universe 𝓤, taken as a setoid under type equivalence _≃_. This gives
an egroup in the next universe 𝓤⁺ that is isomorphic to no egroup in
the universe 𝓤, in a Spartan MLTT with no HoTT/UF assumptions.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

module EGroups.LargeExample (𝓤 : Universe) where

open import UF.Equiv hiding (_≅_)
open import Various.LawvereFPT
open import EGroups.Setoid
open import EGroups.Type
open import EGroups.Size
open import EGroups.Large
      (𝓤 ̇ ) _≃_ ≃-refl (λ X Y → ≃-sym) (λ X Y Z → _●_)
     renaming (𝔸 to 𝕌)

\end{code}

The universe setoid 𝕌 = (𝓤 ̇ , _≃_) is large.

\begin{code}

universe-setoid-is-large : is-large-setoid 𝓤 𝕌
universe-setoid-is-large (T , iso) =
 generalized-Coquand.Lemma₂ ∣ T ∣
  (_≅ˢ_.from iso) (_≅ˢ_.to iso) (_≅ˢ_.from-to iso)

\end{code}

Therefore the free egroup on the universe setoid, which lives in the
next universe, is isomorphic to no egroup whose underlying type and
equivalence relation are both small.

\begin{code}

large-egroup-in-the-next-universe
 : Σ 𝓕 ꞉ EGroup (𝓤 ⁺) (𝓤 ⁺) , ((𝓖 : EGroup 𝓤 𝓤) → ¬ (𝓖 ≅ 𝓕))
large-egroup-in-the-next-universe
 = there-is-a-large-egroup universe-setoid-is-large

\end{code}

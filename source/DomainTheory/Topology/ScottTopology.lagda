Ayberk Tosun, 14 June 2023.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.Topology.ScottTopology
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥  : Universe)
         where

open PropositionalTruncation pt

open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import Posets.Poset fe
open import UF.ImageAndSurjection pt
open import UF.Powerset
open import Slice.Family

open import UF.Logic
open Universal fe
open Existential pt
open Implication fe
open Conjunction

open import DomainTheory.Basics.Dcpo pt fe 𝓥

underlying-orderₚ : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → Ω 𝓣
underlying-orderₚ 𝓓 x y = (x ⊑⟨ 𝓓 ⟩ y) , prop-valuedness 𝓓 x y

syntax underlying-orderₚ 𝓓 x y = x ⊑⟨ 𝓓 ⟩ₚ y

_∈imageₚ_ : {X : 𝓤  ̇} {Y : 𝓦  ̇} → Y → (X → Y) → Ω (𝓤 ⊔ 𝓦)
y ∈imageₚ f = y ∈image f , ∃-is-prop

\end{code}

We define the notion of a Scott-open subset in the following module. The DCPO
`𝓓` taken as an argument has a carrier set living in 𝓤 and order living in 𝓣.
The parameter `𝓦` is for the universe of the subsets for which Scott-openness is
defined. In other words, we define what it means for a subset `P : ⟨ 𝓓 ⟩ → Ω 𝓦`
to be Scott-open.

\begin{code}

module DefnOfScottTopology (𝓓 : DCPO {𝓤} {𝓣}) (𝓦 : Universe) where

\end{code}

I find it convenient to define the type of directed families.

\begin{code}

 Fam↑ : 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓣  ̇
 Fam↑ = Σ S ꞉ Fam 𝓥 ⟨ 𝓓 ⟩ , is-Directed 𝓓 (S [_])

 ⋁_ : Fam↑ → ⟨ 𝓓 ⟩
 ⋁ (S , δ) =
  the-sup (underlying-order 𝓓) (directed-completeness 𝓓 (index S) (S [_]) δ )

 is-upwards-closed : (⟨ 𝓓 ⟩ → Ω 𝓦) → Ω (𝓤 ⊔ 𝓣 ⊔ 𝓦)
 is-upwards-closed P = Ɐ x ꞉ ⟨ 𝓓 ⟩ , Ɐ y ꞉ ⟨ 𝓓 ⟩ , P x ⇒ x ⊑⟨ 𝓓 ⟩ₚ y ⇒ P y

 is-inaccessible-by-directed-joins : (⟨ 𝓓 ⟩ → Ω 𝓦) → Ω (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦)
 is-inaccessible-by-directed-joins P =
  Ɐ (S , δ) ꞉ Fam↑ , P (⋁ (S , δ)) ⇒ (Ǝ i ꞉ index S , P (S [ i ]) holds)

 is-scott-open : (⟨ 𝓓 ⟩ → Ω 𝓦) → Ω (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦)
 is-scott-open P = is-upwards-closed P ∧ is-inaccessible-by-directed-joins P

\end{code}

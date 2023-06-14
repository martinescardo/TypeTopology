Ayberk Tosun, 14 June 2023.

\begin{code}

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

open import UF.Logic
open Universal fe
open Existential pt
open Implication fe
open Conjunction

open import DomainTheory.Basics.Dcpo pt fe 𝓥

Fam : (𝓤 : Universe) → 𝓦  ̇ → 𝓤 ⁺ ⊔ 𝓦  ̇
Fam 𝓤 A = Σ I ꞉ 𝓤  ̇ , (I → A)

index : {A : 𝓤  ̇ } → Fam 𝓦 A → 𝓦  ̇
index (I , _) = I

_[_] : {A : 𝓤 ̇ } → (U : Fam 𝓥 A) → index U → A
(_ , f) [ i ] = f i

infix 9 _[_]

underlying-orderₚ : (𝓓 : DCPO {𝓤} {𝓣}) → ⟨ 𝓓 ⟩ → ⟨ 𝓓 ⟩ → Ω 𝓣
underlying-orderₚ 𝓓 x y = (x ⊑⟨ 𝓓 ⟩ y) , prop-valuedness 𝓓 x y

syntax underlying-orderₚ 𝓓 x y = x ⊑⟨ 𝓓 ⟩ₚ y

_∈imageₚ_ : {X : 𝓤  ̇} {Y : 𝓦  ̇} → Y → (X → Y) → Ω (𝓤 ⊔ 𝓦)
y ∈imageₚ f = y ∈image f , ∃-is-prop

module DefnOfScottTopology (𝓓 : DCPO {𝓤} {𝓣}) where

 Fam↑ : 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓣  ̇
 Fam↑ = Σ S ꞉ Fam 𝓥 ⟨ 𝓓 ⟩ , is-Directed 𝓓 (S [_])

 ⋁_ : Fam↑ → ⟨ 𝓓 ⟩
 ⋁ (S , δ) =
  the-sup (underlying-order 𝓓) (directed-completeness 𝓓 (index S) (S [_]) δ )

 is-upwards-closed : 𝓟 ⟨ 𝓓 ⟩ → Ω (𝓤 ⊔ 𝓣)
 is-upwards-closed P = Ɐ x ꞉ ⟨ 𝓓 ⟩ , Ɐ y ꞉ ⟨ 𝓓 ⟩ , P x ⇒ x ⊑⟨ 𝓓 ⟩ₚ y ⇒ P y  

 is-inaccessible-by-directed-joins : 𝓟 ⟨ 𝓓 ⟩ → Ω (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓣)
 is-inaccessible-by-directed-joins P =
  Ɐ (S , δ) ꞉ Fam↑ , P (⋁ (S , δ)) ⇒ (Ǝ i ꞉ index S , P (S [ i ]) holds)

 is-scott-open : 𝓟 ⟨ 𝓓 ⟩ → Ω (𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓣)
 is-scott-open P = is-upwards-closed P ∧ is-inaccessible-by-directed-joins P

\end{code}

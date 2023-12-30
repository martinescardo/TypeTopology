Ayberk Tosun, 14 June 2023.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.Topology.ScottTopology
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥  : Universe)
         where

open PropositionalTruncation pt

open import OrderedTypes.Poset fe
open import Slice.Family
open import UF.ImageAndSurjection pt
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.SubtypeClassifier
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

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

 ⋁-is-sup : (S : Fam↑) → is-sup (underlying-order 𝓓) (⋁ S) (S .pr₁ [_])
 ⋁-is-sup (S , δ) =
  sup-property (underlying-order 𝓓) (directed-completeness 𝓓 (index S) (S [_]) δ)

 ⋁-is-upperbound : (S : Fam↑) → is-upperbound (underlying-order 𝓓) (⋁ S) (S .pr₁ [_])
 ⋁-is-upperbound S = pr₁ (⋁-is-sup S)

 is-upwards-closed : 𝓟 {𝓦} ⟨ 𝓓 ⟩ → Ω (𝓤 ⊔ 𝓣 ⊔ 𝓦)
 is-upwards-closed P = Ɐ x ꞉ ⟨ 𝓓 ⟩ , Ɐ y ꞉ ⟨ 𝓓 ⟩ , P x ⇒ x ⊑⟨ 𝓓 ⟩ₚ y ⇒ P y

 is-inaccessible-by-directed-joins : 𝓟 {𝓦} ⟨ 𝓓 ⟩ → Ω (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦)
 is-inaccessible-by-directed-joins P =
  Ɐ (S , δ) ꞉ Fam↑ , P (⋁ (S , δ)) ⇒ (Ǝ i ꞉ index S , P (S [ i ]) holds)

 is-scott-open : 𝓟 {𝓦} ⟨ 𝓓 ⟩ → Ω (𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ⊔ 𝓦)
 is-scott-open P = is-upwards-closed P ∧ is-inaccessible-by-directed-joins P

 𝒪ₛ : 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓣  ̇
 𝒪ₛ = Σ P ꞉ (⟨ 𝓓 ⟩ → Ω 𝓦) , is-scott-open P holds

 _∈ₛ_ : ⟨ 𝓓 ⟩ → 𝒪ₛ → Ω 𝓦
 x ∈ₛ U = U .pr₁ x

\end{code}

\begin{code}

 record 𝒪ₛᴿ : 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓥 ⁺ ⊔ 𝓣  ̇ where
  field
   pred : ⟨ 𝓓 ⟩ → Ω 𝓦

   pred-is-upwards-closed : is-upwards-closed pred holds
   pred-is-inaccessible-by-dir-joins : is-inaccessible-by-directed-joins pred holds

 to-𝒪ₛᴿ : 𝒪ₛ → 𝒪ₛᴿ
 to-𝒪ₛᴿ (P , υ , ι) = record
                       { pred                              = P
                       ; pred-is-upwards-closed            = υ
                       ; pred-is-inaccessible-by-dir-joins = ι
                       }

 from-𝒪ₛᴿ : 𝒪ₛᴿ → 𝒪ₛ
 from-𝒪ₛᴿ 𝔘 =
  𝔘 .pred , 𝔘 .pred-is-upwards-closed , 𝔘 .pred-is-inaccessible-by-dir-joins
   where
    open 𝒪ₛᴿ

\end{code}

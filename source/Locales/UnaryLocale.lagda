Ayberk Tosun, 21 August 2023

\begin{code}[hide]

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons
open import UF.Logic
open import MLTT.Spartan
open import UF.Size

module Locales.UnaryLocale (pt : propositional-truncations-exist)
                           (fe : Fun-Ext)                          where

open import Locales.Frame       pt fe
open import Locales.Compactness pt fe
open Locale

open import Slice.Family

open AllCombinators pt fe

\end{code}

\begin{code}

positive : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
positive {_} {_} {𝓦} X U =
 Ɐ S ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ , U ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] S) ⇒ ∥ index S ∥Ω

is-super-compact-open : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-super-compact-open {_} {_} {𝓦} X U =
 Ɐ U ꞉ ⟨ 𝒪 X ⟩ , Ɐ S ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ ,
  U ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] S) ⇒
   (Ǝ i ꞉ index S , (U ≤[ poset-of (𝒪 X) ] (S [ i ])) holds)

consists-of-super-compact-opens : (X : Locale 𝓤 𝓥 𝓦)
                                   → Fam 𝓦 ⟨ 𝒪 X ⟩
                                   → Ω (𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺))
consists-of-super-compact-opens X S =
 Ɐ i ꞉ index S , is-super-compact-open X (S [ i ])

\end{code}

\begin{code}

unaryᴰ : Locale 𝓤 𝓥 𝓦 → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ̇
unaryᴰ {𝓤 = 𝓤} {𝓥} {𝓦} X =
 Σ ℬ ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ , is-directed-basis (𝒪 X) ℬ
                     × consists-of-super-compact-opens X ℬ holds


\end{code}

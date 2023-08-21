Ayberk Tosun, 21 August 2023

These used to live in the `CompactRegular` module which is now deprecated and
will be broken down into smaller modules.

\begin{code}[hide]

open import UF.PropTrunc
open import UF.FunExt
open import UF.Subsingletons
open import UF.Logic
open import MLTT.Spartan
open import UF.Size

module Locales.SmallBasis (pt : propositional-truncations-exist)
                          (fe : Fun-Ext)                          where

open import Locales.Frame       pt fe
open import Locales.Compactness pt fe
open import Locales.Spectrality pt fe
open import Slice.Family

open AllCombinators pt fe

open Locale

\end{code}

In `spectralₛᴰ`, we give the old definition of a spectral locale that bakes in
the small basis assumption. We use the `ₛ` subscript to differentiate it from
the new one.

\begin{code}

contains-top : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
contains-top F U = Ǝ t ꞉ index U , is-top F (U [ t ]) holds

closed-under-binary-meets : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
closed-under-binary-meets F 𝒮 =
 Ɐ i ꞉ index 𝒮 , Ɐ j ꞉ index 𝒮 ,
  Ǝ k ꞉ index 𝒮 , ((𝒮 [ k ]) is-glb-of (𝒮 [ i ] , 𝒮 [ j ])) holds
   where
    open Meets (λ x y → x ≤[ poset-of F ] y)

closed-under-finite-meets : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦)
closed-under-finite-meets F S = contains-top F S ∧ closed-under-binary-meets F S

spectralₛᴰ : Locale 𝓤 𝓥 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
spectralₛᴰ {_} {_} {𝓦} X =
  Σ ℬ ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ ,
     is-directed-basis (𝒪 X) ℬ
   × consists-of-compact-opens X ℬ holds
   × closed-under-finite-meets (𝒪 X) ℬ holds

\end{code}

The previous definition of spectrality was the truncation of `spectralₛᴰ`:

\begin{code}

is-spectralₛ : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-spectralₛ X = ∥ spectralₛᴰ X ∥Ω

\end{code}

One of the things that we show in this module is that this truncation was
unnecessary as the basis is unique in the presence of a small basis.

We now define the following crucial predicate expressing what it means for the
type of compact opens of a locale to be small:

\begin{code}

has-small-𝒦 : Locale 𝓤 𝓥 𝓦 → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)  ̇
has-small-𝒦 {_} {_} {𝓦} X = 𝒦 X is 𝓦 small

\end{code}

\begin{code}

spectral-and-has-small-𝒦-gives-spectralₛ : (X : Locale 𝓤 𝓥 𝓦)
                                         → is-spectral X holds
                                         → has-small-𝒦 X
                                         → spectralₛᴰ X
spectral-and-has-small-𝒦-gives-spectralₛ {_} {_} {𝓦} X σ (𝒦₀ , (s , r)) =
 ℬ , β , κ , {!!}
  where
   ℬ : Fam 𝓦 ⟨ 𝒪 X ⟩
   ℬ = 𝒦₀ , pr₁ ∘ s

   δ : is-basis-for (𝒪 X) ℬ
   δ U = {!!}

   β : is-directed-basis (𝒪 X) ℬ
   β = δ , {!!}

   κ : {!!}
   κ = {!!}

\end{code}

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

open PropositionalTruncation pt

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

Compact opens are basic:

\begin{code}

is-basic : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → has-directed-basis₀ (𝒪 X) → Ω (𝓤 ⊔ 𝓦)
is-basic X U (ℬ , β) = Ǝ i ꞉ index ℬ , U ＝ ℬ [ i ]

compact-opens-are-basic-in-compact-locales : (X : Locale 𝓤 𝓥 𝓦)
                                           → (b : has-directed-basis₀ (𝒪 X))
                                           → (K : ⟨ 𝒪 X ⟩)
                                           → is-compact-open X K holds
                                           → is-basic X K b holds
compact-opens-are-basic-in-compact-locales {_} {_} {𝓦} X (ℬ , β) K κ =
 ∥∥-rec ∃-is-prop † (κ ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ d q)
  where
   β₀ : is-basis-for (𝒪 X) ℬ
   β₀ = pr₁ β

   𝒥 : Fam 𝓦 (index ℬ)
   𝒥 = covering-index-family (𝒪 X) ℬ β₀ K

   p : K ＝ ⋁[ 𝒪 X ] ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆
   p = covers (𝒪 X) ℬ β₀ K

   d : is-directed (𝒪 X) ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ holds
   d = covers-are-directed (𝒪 X) (ℬ , β) K

   q : (K ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆)) holds
   q = reflexivity+ (poset-of (𝒪 X)) p

   † : Σ j ꞉ index 𝒥 , (K ≤[ poset-of (𝒪 X) ] ℬ [ 𝒥 [ j ] ]) holds
     → is-basic X K (ℬ , β) holds
   † (j , φ) = ∣ 𝒥 [ j ] , ≤-is-antisymmetric (poset-of (𝒪 X)) φ ψ ∣
    where
     open PosetReasoning (poset-of (𝒪 X))

     Ⅰ = ⋁[ 𝒪 X ]-upper ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ j
     Ⅱ = reflexivity+ (poset-of (𝒪 X)) (p ⁻¹)

     ψ : (ℬ [ 𝒥 [ j ] ] ≤[ poset-of (𝒪 X) ] K) holds
     ψ = ℬ [ 𝒥 [ j ] ] ≤⟨ Ⅰ ⟩ ⋁[ 𝒪 X ] ⁅ ℬ [ j ] ∣ j ε 𝒥 ⁆ ≤⟨ Ⅱ ⟩ K ■

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

spectral-and-has-small-𝒦-gives-basis : (X : Locale 𝓤 𝓥 𝓦)
                                     → is-spectral X holds
                                     → has-small-𝒦 X
                                     → spectralₛᴰ X
spectral-and-has-small-𝒦-gives-basis {_} {_} {𝓦} X σ 𝕤 =
 ℬ , d , {!!} , {!!}
  where
   ℬ : Fam 𝓦 ⟨ 𝒪 X ⟩
   ℬ = resize-family (ℬ-compact X) 𝕤

   β : is-basis-for (𝒪 X) ℬ
   β U = ∥∥-rec {!!} {!!} {!!}

   d : is-directed-basis (𝒪 X) ℬ
   d = β , {!!}

\end{code}

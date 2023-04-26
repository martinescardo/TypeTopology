Ayberk Tosun, started 7th December 2022

\begin{code}[hide]

{-# OPTIONS --without-K --exact-split --safe --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.Size
open import UF.Equiv renaming (_■ to _𝔔𝔈𝔇)
open import UF.Retracts
open import UF.Embeddings
open import UF.PropTrunc
open import MLTT.List hiding ([_])

module Locales.UniversalPropertyOfPatch
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
       where

open import UF.Subsingletons
open import UF.Logic
open import UF.Subsingletons-FunExt

open AllCombinators pt fe
open import UF.ImageAndSurjection
-- open UF.ImageAndSurjection pt

open import Locales.Frame pt fe
open import Locales.CompactRegular pt fe
open import Locales.BooleanAlgebra pt fe
open import Locales.PatchLocale pt fe
open import Locales.PatchProperties pt fe
open import Locales.HeytingImplication pt fe
open import Locales.GaloisConnection pt fe
open import Locales.AdjointFunctorTheoremForFrames pt fe

open PropositionalTruncation pt

\end{code}

\begin{code}

open Locale

module UniversalProperty (A : Locale (𝓤 ⁺) 𝓤 𝓤) (σ : is-spectral (𝒪 A) holds) where

 open PatchConstruction A σ renaming (Patch to Patch-A)
 open ClosedNucleus     A σ
 open OpenNucleus       A σ

\end{code}

\section{Proof of the Universal Property}

\begin{code}

 ump-of-patch : (X : Locale (𝓤 ⁺) 𝓤 𝓤)
              → is-stone (𝒪 X) holds
              → (𝒻 : X ─c→ A)
              → is-spectral-map (𝒪 A) (𝒪 X) 𝒻 holds
              → ∃! 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻ .pr₁ ‘ x ’)
 ump-of-patch X 𝕤 𝒻 μ = ∥∥-rec₂ (being-singleton-is-prop fe) γ σ (pr₂ 𝕤)
  where
   γ : spectralᴰ (𝒪 A)
     → zero-dimensionalᴰ (𝒪 X)
     → ∃! 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻ .pr₁ ‘ x ’)
   γ σᴰ 𝕫ᴰ = ((f⁻⋆ , {!!} , {!!} , {!!}) , {!!}) , {!!}
    where
     open SmallPatchConstruction A σᴰ using (≼-implies-≼ᵏ; ≼ᵏ-implies-≼; _≼ᵏ_) renaming (SmallPatch to Patchₛ-A)
     open ContinuousMapNotation X A

     X-has-basis : has-basis (𝒪 X) holds
     X-has-basis = ∣ pr₁ 𝕫ᴰ , pr₁ (pr₁ (pr₂ 𝕫ᴰ)) ∣

     A-has-basis : has-basis (𝒪 A) holds
     A-has-basis = ∣ pr₁ σᴰ , pr₁ (pr₁ (pr₂ σᴰ)) ∣

     open HeytingImplicationConstruction X X-has-basis

     Bₐ : 𝓤  ̇
     Bₐ = pr₁ (pr₁ σᴰ)

     β : Bₐ → ⟨ 𝒪 A ⟩
     β = pr₂ (pr₁ σᴰ)

     βₖ : Bₐ → 𝒦
     βₖ m = β m , pr₁ (pr₂ (pr₂ σᴰ)) m

     ¬𝒻⋆ : Bₐ → ⟨ 𝒪 X ⟩
     ¬𝒻⋆ m = (𝒻 ⋆∙ β m) ==> 𝟎[ 𝒪 X ]

     𝕃 : ⟨ 𝒪 Patch-A ⟩ → Bₐ → Bₐ → Ω 𝓤
     𝕃 𝒿 m n = (‘ β m ’ ∧[ 𝒪 Patch-A ] ¬‘ βₖ n ’) ≼ᵏ 𝒿

     f⁻⋆ : ⟨ 𝒪 Patchₛ-A ⟩ → ⟨ 𝒪 X ⟩
     f⁻⋆ j =
      ⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ n
                 ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝕃 j m n holds ⁆

     f⁻⋆-is-monotone : is-monotonic
                        (poset-of (𝒪 Patchₛ-A))
                        (poset-of (𝒪 X))
                        f⁻⋆
                       holds
     f⁻⋆-is-monotone (𝒿 , 𝓀) p = cofinal-implies-join-covered (𝒪 X) 𝒮 𝒯 †
      where
       𝒮 : Fam 𝓤 ⟨ 𝒪 X ⟩
       𝒮 = ⁅ (𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ n
             ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝕃 𝒿 m n holds ⁆

       𝒯 : Fam 𝓤 ⟨ 𝒪 X ⟩
       𝒯 = ⁅ (𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ n
             ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝕃 𝓀 m n holds ⁆

       † : cofinal-in (𝒪 X) 𝒮 𝒯 holds
       † (m , n , q) = ∣ (m , n , ‡) , ♣ ∣
        where
         open PosetReasoning (poset-of (𝒪 Patch-A))

         ‡₁ : ((‘ β m ’ ∧[ 𝒪 Patch-A ] ¬‘ βₖ n ’) ≼ 𝓀) holds
         ‡₁ = ‘ β m ’ ∧[ 𝒪 Patch-A ] ¬‘ βₖ n ’    ≤⟨ Ⅰ ⟩
              𝒿                                   ≤⟨ Ⅱ ⟩
              𝓀                                   ■
               where
                Ⅰ = ≼ᵏ-implies-≼ (‘ β m ’ ∧[ 𝒪 Patch-A ] ¬‘ βₖ n ’) 𝒿 q
                Ⅱ = ≼ᵏ-implies-≼ 𝒿 𝓀 p

         ‡ : 𝕃 𝓀 m n holds
         ‡ = ≼-implies-≼ᵏ (‘ β m ’ ∧[ 𝒪 Patch-A ] ¬‘ βₖ n ’) 𝓀 ‡₁

         ♣ : (_ ≤[ poset-of (𝒪 X) ] _) holds
         ♣ = ≤-is-reflexive (poset-of (𝒪 X)) ((𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ n)

     𝒻⁻⋆ₘ : poset-of (𝒪 Patchₛ-A) ─m→ poset-of (𝒪 X)
     𝒻⁻⋆ₘ = f⁻⋆ , f⁻⋆-is-monotone

     open PatchStoneᴰ A σᴰ

     Patchₛ-A-has-basis : has-basis (𝒪 Patchₛ-A) holds
     Patchₛ-A-has-basis = spectral-frames-have-bases
                           (𝒪 Patchₛ-A)
                           patchₛ-is-spectral

     open AdjointFunctorTheorem X Patchₛ-A Patchₛ-A-has-basis
     open AdjointFunctorTheorem X A A-has-basis
      using ()
      renaming (right-adjoint-of to right-adjoint-ofₓ;
                adjunction-inequality-forward to adjunction-inequality-forwardₓ)
     open GaloisConnectionBetween (poset-of (𝒪 Patchₛ-A)) (poset-of (𝒪 X))

     𝒻* : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 A ⟩
     𝒻* = pr₁ (right-adjoint-ofₓ 𝒻)

     open ClosedNucleus X (stone-locales-are-spectral (𝒪 X) 𝕤)
      using ()
      renaming (‘_’ to ‘_’ₓ)

     -- Igor's definition.
     closed-image : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 A ⟩ → ⟨ 𝒪 A ⟩
     closed-image U = 𝒻* ∘ ‘ U ’ₓ .pr₁ ∘ 𝒻 ⋆∙_

     closed-image-is-inflationary : (U : ⟨ 𝒪 X ⟩) (V : ⟨ 𝒪 A ⟩)
                                  → (V ≤[ poset-of (𝒪 A) ] closed-image U V) holds
     closed-image-is-inflationary U V =
      adjunction-inequality-forwardₓ 𝒻 (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V) V †
       where
        † : (𝒻 ⋆∙ V ≤[ poset-of (𝒪 X) ] (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V)) holds
        † = ∨[ 𝒪 X ]-upper₂ U (𝒻 ⋆∙ V)

     f⁻⋆-preserves-joins : is-join-preserving (𝒪 Patchₛ-A) (𝒪 X) f⁻⋆ holds
     f⁻⋆-preserves-joins = aft-forward 𝒻⁻⋆ₘ †
      where
       f⁻* : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 Patchₛ-A ⟩
       f⁻* U = {!!}

       † : has-right-adjoint 𝒻⁻⋆ₘ
       † = (f⁻* , {!!}) , {!!}

\end{code}

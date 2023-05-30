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

open import Locales.Frame pt fe
open import Locales.CompactRegular pt fe
open import Locales.BooleanAlgebra pt fe
open import Locales.PatchLocale pt fe
open import Locales.PatchProperties pt fe
open import Locales.HeytingImplication pt fe
open import Locales.GaloisConnection pt fe
open import Locales.AdjointFunctorTheoremForFrames pt fe
open import Locales.Nucleus pt fe

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

 module UniversalPropertyOfPatch (X  : Locale (𝓤 ⁺) 𝓤 𝓤)
                                 (σᴰ : spectralᴰ (𝒪 A))
                                 (𝕫ᴰ : zero-dimensionalᴰ (𝒪 X))
                                 (𝕜  : is-compact (𝒪 X) holds)
                                 (𝒻 : X ─c→ A)
                                 (μ : is-spectral-map (𝒪 A) (𝒪 X) 𝒻 holds) where

  open SmallPatchConstruction A σᴰ
   using (𝟎-is-id; ≼-implies-≼ᵏ; ≼ᵏ-implies-≼; _≼ᵏ_)
   renaming (SmallPatch to Patchₛ-A)
  open ContinuousMapNotation X A

  X-has-basis : has-basis (𝒪 X) holds
  X-has-basis = ∣ pr₁ 𝕫ᴰ , pr₁ (pr₁ (pr₂ 𝕫ᴰ)) ∣

  Bₐ : 𝓤  ̇
  Bₐ = pr₁ (pr₁ σᴰ)

  β : Bₐ → ⟨ 𝒪 A ⟩
  β = pr₂ (pr₁ σᴰ)

  Bₓ : 𝓤  ̇
  Bₓ = pr₁ (pr₁ 𝕫ᴰ)

  βₓ : Bₓ → ⟨ 𝒪 X ⟩
  βₓ = pr₂ (pr₁ 𝕫ᴰ)

  β-is-directed-basis : is-directed-basis (𝒪 A) (Bₐ , β)
  β-is-directed-basis = pr₁ (pr₂ σᴰ)

  β-is-basis-for-A : is-basis-for (𝒪 A) (Bₐ , β)
  β-is-basis-for-A = pr₁ β-is-directed-basis

  A-has-basis : has-basis (𝒪 A) holds
  A-has-basis = spectral-frames-have-bases (𝒪 A) σ

  open HeytingImplicationConstruction X X-has-basis
  open HeytingImplicationConstruction A A-has-basis
   using ()
   renaming (_==>_ to _==>ₐ_; H₈ to H₈ₐ;
             heyting-implication-identity to heyting-implication-identityₐ;
             ==>-right-monotone to ==>ₐ-right-monotone;
             ex-falso-quodlibet to ex-falso-quodlibetₐ)

  βₖ : Bₐ → 𝒦
  βₖ m = β m , pr₁ (pr₂ (pr₂ σᴰ)) m

  ¬𝒻⋆ : ⟨ 𝒪 A ⟩ → ⟨ 𝒪 X ⟩
  ¬𝒻⋆ U = (𝒻 ⋆∙ U) ==> 𝟎[ 𝒪 X ]

  ¬𝒻⋆𝟎-is-𝟏 : ¬𝒻⋆ 𝟎[ 𝒪 A ] ＝ 𝟏[ 𝒪 X ]
  ¬𝒻⋆𝟎-is-𝟏 = only-𝟏-is-above-𝟏 (𝒪 X) (¬𝒻⋆ 𝟎[ 𝒪 A ]) †
   where
    open PosetReasoning (poset-of (𝒪 X))

    ‡ : ((𝟏[ 𝒪 X ] ∧[ 𝒪 X ] 𝒻 ⋆∙ 𝟎[ 𝒪 A ]) ≤[ poset-of (𝒪 X) ] 𝟎[ 𝒪 X ]) holds
    ‡ = 𝟏[ 𝒪 X ] ∧[ 𝒪 X ] 𝒻 ⋆∙ 𝟎[ 𝒪 A ]    ≤⟨ Ⅰ  ⟩
        𝒻 ⋆∙ 𝟎[ 𝒪 A ]                      ＝⟨ Ⅱ ⟩ₚ
        𝟎[ 𝒪 X ]                           ■
         where
          Ⅰ = ∧[ 𝒪 X ]-lower₂ 𝟏[ 𝒪 X ] (𝒻 ⋆∙ 𝟎[ 𝒪 A ])
          Ⅱ = frame-homomorphisms-preserve-bottom (𝒪 A) (𝒪 X) 𝒻

    † : (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] ¬𝒻⋆ 𝟎[ 𝒪 A ]) holds
    † = heyting-implication₁ (𝒻 ⋆∙ 𝟎[ 𝒪 A ]) 𝟎[ 𝒪 X ] 𝟏[ 𝒪 X ] ‡

  𝕃 : ⟨ 𝒪 Patch-A ⟩ → Bₐ → Bₐ → Ω 𝓤
  𝕃 𝒿 m n = (‘ β m ’ ∧[ 𝒪 Patch-A ] ¬‘ βₖ n ’) ≼ᵏ 𝒿

  f⁻⁺ : ⟨ 𝒪 Patchₛ-A ⟩ → ⟨ 𝒪 X ⟩
  f⁻⁺ j =
   ⋁[ 𝒪 X ]
    ⁅ (𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝕃 j m n holds ⁆

  f⁻⁺₂ : ⟨ 𝒪 Patchₛ-A ⟩ → ⟨ 𝒪 X ⟩
  f⁻⁺₂ 𝒿@(j , _) = ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆

  f⁻⁺₂-equiv-f⁻⁺₁ : (𝒿 : ⟨ 𝒪 Patchₛ-A ⟩) → f⁻⁺ 𝒿 ＝ f⁻⁺₂ 𝒿
  f⁻⁺₂-equiv-f⁻⁺₁ 𝒿@(j , _) = ≤-is-antisymmetric (poset-of (𝒪 X)) †′ ‡
   where
    S : Fam 𝓤 ⟨ 𝒪 X ⟩
    S = ⁅ (𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝕃 𝒿 m n holds ⁆

    T : Fam 𝓤 ⟨ 𝒪 X ⟩
    T = ⁅ 𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆

    † : cofinal-in (𝒪 X) S T holds
    † (m , n , p) = ∣ n , ※ ∣
     where
      q : (β m ≤[ poset-of (𝒪 A) ] j (β n)) holds
      q = β m                                                ≤⟨ Ⅰ     ⟩
          β m ∨[ 𝒪 A ] β n                                   ＝⟨ Ⅱ    ⟩ₚ
          (β m ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] 𝟏[ 𝒪 A ]               ＝⟨ Ⅲ    ⟩ₚ
          (β m ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] (β n ==>ₐ β n)         ＝⟨ refl ⟩ₚ
          (β m ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] (¬‘ βₖ n ’ .pr₁ (β n)) ＝⟨ refl ⟩ₚ
          (‘ β m ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) .pr₁ (β n)     ≤⟨ p n   ⟩
          j (β n)                                            ■
       where
        open PosetReasoning (poset-of (𝒪 A))

        Ⅰ = ∨[ 𝒪 A ]-upper₁ (β m) (β n)
        Ⅱ = 𝟏-right-unit-of-∧ (𝒪 A) (β m ∨[ 𝒪 A ] β n) ⁻¹
        Ⅲ = ap
             (λ - → (β m ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] -)
             (heyting-implication-identityₐ (β n) ⁻¹)

      ※ : ((𝒻 ⋆∙ β m ∧[ 𝒪 X ] ¬𝒻⋆ (β n))
            ≤[ poset-of (𝒪 X) ]
           (𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] (¬𝒻⋆ (β n)))) holds
      ※ = ∧[ 𝒪 X ]-left-monotone
           (frame-morphisms-are-monotonic
             (𝒪 A)
             (𝒪 X)
             (𝒻 ⋆∙_)
             (𝒻 .pr₂)
             (β m , j (β n)) q)
       where
        open PosetReasoning (poset-of (𝒪 X))

    †′ : ((⋁[ 𝒪 X ] S) ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] T)) holds
    †′ = cofinal-implies-join-covered (𝒪 X) S T †

    ‡ : ((⋁[ 𝒪 X ] T) ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] S)) holds
    ‡ = ⋁[ 𝒪 X ]-least T ((⋁[ 𝒪 X ] S) , ξ)
     where
      open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

      ξ : ((⋁[ 𝒪 X ] S) is-an-upper-bound-of T) holds
      ξ n =
       let
        open PosetReasoning (poset-of (𝒪 X))
       in
        𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)                          ＝⟨ Ⅰ  ⟩ₚ
        𝒻 ⋆∙ (⋁[ 𝒪 A ] ⁅ β i ∣ i ε 𝒥 ⁆) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)       ＝⟨ Ⅱ  ⟩ₚ
        (⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (β i) ∣ i ε 𝒥 ⁆) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)     ＝⟨ Ⅲ  ⟩ₚ
        ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (β i) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ i ε 𝒥 ⁆       ≤⟨ Ⅳ   ⟩
        ⋁[ 𝒪 X ] S                                           ■
       where
        𝒥 : Fam 𝓤 Bₐ
        𝒥 = pr₁ (pr₁ (pr₁ (pr₂ σᴰ)) (j (β n)))

        ※ : ((⋁[ 𝒪 X ] S)
              is-an-upper-bound-of
             ⁅ 𝒻 ⋆∙ (β i) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ i ε 𝒥 ⁆) holds
        ※ i = ⋁[ 𝒪 X ]-upper S (𝒥 [ i ] , n , foo)
               where
                open PosetReasoning (poset-of (𝒪 A))
                open NucleusHeytingImplicationLaw A A-has-basis (nucleus-of 𝒿)

                foo : 𝕃 𝒿 (𝒥 [ i ]) n holds
                foo m =
                 (‘ β (𝒥 [ i ]) ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) .pr₁ (β m)      ＝⟨ refl ⟩ₚ
                 ((β (𝒥 [ i ]) ∨[ 𝒪 A ] β m) ∧[ 𝒪 A ] (β n ==>ₐ β m))        ≤⟨ Ⅰ     ⟩
                 (j (β n) ∨[ 𝒪 A ] β m) ∧[ 𝒪 A ] (β n ==>ₐ β m)              ≤⟨ Ⅱ     ⟩
                 (j (β n) ∨[ 𝒪 A ] β m) ∧[ 𝒪 A ] (β n ==>ₐ j (β m))          ＝⟨ Ⅲ    ⟩ₚ
                 (j (β n) ∨[ 𝒪 A ] β m) ∧[ 𝒪 A ] (j (β n) ==>ₐ j (β m))      ≤⟨ Ⅳ     ⟩
                 (j (β n) ∨[ 𝒪 A ] j (β m)) ∧[ 𝒪 A ] (j (β n) ==>ₐ j (β m))  ＝⟨ Ⅴ    ⟩ₚ
                 (j (β m) ∨[ 𝒪 A ] j (β n)) ∧[ 𝒪 A ] (j (β n) ==>ₐ j (β m))  ＝⟨ Ⅵ    ⟩ₚ
                 j (β m)                                                     ■
                  where
                   ♣ = β (𝒥 [ i ]) ≤⟨ 𝕒 ⟩ ⋁[ 𝒪 A ] ⁅ β i ∣ i ε 𝒥 ⁆  ＝⟨ 𝕓 ⟩ₚ j (β n) ■
                        where
                         𝕒 = ⋁[ 𝒪 A ]-upper ⁅ β i ∣ i ε 𝒥 ⁆ i
                         𝕓 = covers (𝒪 A) (Bₐ , β) β-is-basis-for-A (j (β n)) ⁻¹

                   Ⅰ = ∧[ 𝒪 A ]-left-monotone (∨[ 𝒪 A ]-left-monotone ♣)
                   Ⅱ = ∧[ 𝒪 A ]-right-monotone
                        (==>ₐ-right-monotone (𝓃₁ (𝒪 A) (nucleus-of 𝒿) (β m)))
                   Ⅲ = ap
                        (λ - → (j (β n) ∨[ 𝒪 A ] β m) ∧[ 𝒪 A ] -)
                        (nucleus-heyting-implication-law (β n) (β m))
                   Ⅳ = ∧[ 𝒪 A ]-left-monotone (∨[ 𝒪 A ]-right-monotone (𝓃₁ (𝒪 A) (nucleus-of 𝒿) (β m)))
                   Ⅴ = ap
                        (λ - → - ∧[ 𝒪 A ] (j (β n) ==>ₐ j (β m)))
                        (∨[ 𝒪 A ]-is-commutative (j (β n)) (j (β m)))
                   Ⅵ = H₈ₐ (j (β m)) (j (β n)) ⁻¹

        Ⅰ = ap
             (λ - → 𝒻 ⋆∙ - ∧[ 𝒪 X ] ¬𝒻⋆ (β n))
             (covers (𝒪 A) (Bₐ , β) β-is-basis-for-A (j (β n)))
        Ⅱ = ap
             (λ - → - ∧[ 𝒪 X ] ¬𝒻⋆ (β n))
             (frame-homomorphisms-preserve-all-joins
               (𝒪 A)
               (𝒪 X)
               𝒻
               ⁅ β i ∣ i ε 𝒥 ⁆)
        Ⅲ = distributivity′-right (𝒪 X) (¬𝒻⋆ (β n)) ⁅ 𝒻 ⋆∙ (β i) ∣ i ε 𝒥 ⁆
        Ⅳ = ⋁[ 𝒪 X ]-least
             ⁅ 𝒻 ⋆∙ (β i) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ i ε 𝒥 ⁆
             ((⋁[ 𝒪 X ] S) , ※)

  f⁻⁺-is-monotone : is-monotonic (poset-of (𝒪 Patchₛ-A)) (poset-of (𝒪 X)) f⁻⁺
                     holds
  f⁻⁺-is-monotone (𝒿 , 𝓀) p = cofinal-implies-join-covered (𝒪 X) 𝒮 𝒯 †
   where
    𝒮 : Fam 𝓤 ⟨ 𝒪 X ⟩
    𝒮 = ⁅ (𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)
          ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝕃 𝒿 m n holds ⁆

    𝒯 : Fam 𝓤 ⟨ 𝒪 X ⟩
    𝒯 = ⁅ (𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)
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
      ♣ = ≤-is-reflexive (poset-of (𝒪 X)) ((𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))

  𝒻⁻⋆ₘ : poset-of (𝒪 Patchₛ-A) ─m→ poset-of (𝒪 X)
  𝒻⁻⋆ₘ = f⁻⁺ , f⁻⁺-is-monotone

  open PatchStoneᴰ A σᴰ

  Patchₛ-A-has-basis : has-basis (𝒪 Patchₛ-A) holds
  Patchₛ-A-has-basis = spectral-frames-have-bases
                        (𝒪 Patchₛ-A)
                        patchₛ-is-spectral

  open AdjointFunctorTheorem X Patchₛ-A Patchₛ-A-has-basis hiding (f₊-is-right-adjoint-of-f⁺)
  open AdjointFunctorTheorem Patchₛ-A X X-has-basis
   using ()
   renaming (adjunction-inequality-forward to adjunction-inequality-forward₀)
  open AdjointFunctorTheorem X A A-has-basis
   using (f₊-is-right-adjoint-of-f⁺)
   renaming (right-adjoint-of to right-adjoint-ofₓ;
             f₊-preserves-binary-meets to f₊-preserves-binary-meetsₓ;
             adjunction-inequality-forward to adjunction-inequality-forwardₓ;
             adjunction-inequality-backward to adjunction-inequality-backwardₓ)
  open GaloisConnectionBetween (poset-of (𝒪 Patchₛ-A)) (poset-of (𝒪 X))
  open GaloisConnectionBetween (poset-of (𝒪 X)) (poset-of (𝒪 A))
   using () renaming (counit to counitₓ)
  open GaloisConnectionBetween (poset-of (𝒪 A)) (poset-of (𝒪 X))
   using () renaming (counit to counitₐ)

  𝒻₊ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 A ⟩
  𝒻₊ = pr₁ (right-adjoint-ofₓ 𝒻)

  𝒻⁺ₘ : poset-of (𝒪 A) ─m→ poset-of (𝒪 X)
  𝒻⁺ₘ = pr₁ 𝒻 , frame-morphisms-are-monotonic (𝒪 A) (𝒪 X) (𝒻 ⋆∙_) (pr₂ 𝒻)

  𝒻₊ₘ : poset-of (𝒪 X) ─m→ poset-of (𝒪 A)
  𝒻₊ₘ = right-adjoint-ofₓ 𝒻

  𝒻⁻-α : f⁻⁺ 𝟏[ 𝒪 Patchₛ-A ] ＝ 𝟏[ 𝒪 X ]
  𝒻⁻-α = only-𝟏-is-above-𝟏 (𝒪 X) (f⁻⁺ 𝟏[ 𝒪 Patchₛ-A ]) †
   where
    open PosetReasoning (poset-of (𝒪 X))

    † : (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] f⁻⁺ 𝟏[ 𝒪 Patchₛ-A ]) holds
    † = ∥∥-rec
         (holds-is-prop (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] f⁻⁺ 𝟏[ 𝒪 Patchₛ-A ]))
         ‡
         (compact-opens-are-basic-in-compact-frames
           (𝒪 A)
           (Bₐ , β)
           (pr₁ (pr₂ σᴰ))
           (spectral-implies-compact (𝒪 A) σ)
           𝟎[ 𝒪 A ]
           (𝟎-is-compact (𝒪 A)))
         where
          ‡ : Σ i ꞉ Bₐ , 𝟎[ 𝒪 A ] ＝ β i
            → (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] f⁻⁺ 𝟏[ 𝒪 Patchₛ-A ]) holds
          ‡ (i , p) =
           𝟏[ 𝒪 X ]                                            ＝⟨ Ⅰ    ⟩ₚ
           𝟏[ 𝒪 X ] ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                          ＝⟨ Ⅱ    ⟩ₚ
           𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                     ＝⟨ Ⅲ    ⟩ₚ
           𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] ¬𝒻⋆ (β i)                    ≤⟨  Ⅳ    ⟩
           ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆  ＝⟨ refl ⟩ₚ
           f⁻⁺₂ 𝟏[ 𝒪 Patchₛ-A ]                                ＝⟨ Ⅴ    ⟩ₚ
           f⁻⁺  𝟏[ 𝒪 Patchₛ-A ]                                ■
            where
             𝕒   = heyting-implication-identity 𝟎[ 𝒪 X ] ⁻¹
             𝕓   = ap
                    (λ - → - ==> 𝟎[ 𝒪 X ])
                    (frame-homomorphisms-preserve-bottom (𝒪 A) (𝒪 X) 𝒻 ⁻¹)
             𝕔   = ap (λ - → (𝒻 ⋆∙ -) ==> 𝟎[ 𝒪 X ]) p

             Ⅰ   = ∧[ 𝒪 X ]-is-idempotent 𝟏[ 𝒪 X ]
             Ⅲ   = ap
                    (λ - → 𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] -)
                    (𝟏[ 𝒪 X ]                     ＝⟨ 𝕒    ⟩
                     𝟎[ 𝒪 X ] ==> 𝟎[ 𝒪 X ]        ＝⟨ 𝕓    ⟩
                     (𝒻 ⋆∙ 𝟎[ 𝒪 A ]) ==> 𝟎[ 𝒪 X ] ＝⟨ 𝕔    ⟩
                     (𝒻 ⋆∙ (β i)) ==> 𝟎[ 𝒪 X ]    ＝⟨ refl ⟩
                     ¬𝒻⋆ (β i)                    ∎)
             Ⅳ   = ⋁[ 𝒪 X ]-upper ⁅ 𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆ i
             Ⅱ   = ap
                    (λ - → - ∧[ 𝒪 X ] 𝟏[ 𝒪 X ])
                    (frame-homomorphisms-preserve-top (𝒪 A) (𝒪 X) 𝒻 ⁻¹)
             Ⅴ   = f⁻⁺₂-equiv-f⁻⁺₁ 𝟏[ 𝒪 Patchₛ-A ] ⁻¹

  𝒻⁻-β : preserves-binary-meets (𝒪 Patch-A) (𝒪 X) f⁻⁺ holds
  𝒻⁻-β 𝒿@(j , _) 𝓀@(k , _) =
   f⁻⁺ (𝒿 ∧[ 𝒪 Patch-A ] 𝓀)                                                                                              ＝⟨ Ⅰ    ⟩
   f⁻⁺₂ (𝒿 ∧[ 𝒪 Patch-A ] 𝓀)                                                                                             ＝⟨ refl ⟩
   ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (j (β n) ∧[ 𝒪 A ] k (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆                                                  ＝⟨ Ⅱ    ⟩
   ⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆                                             ＝⟨ Ⅲ    ⟩
   ⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ j (β n)  ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ∣ n ∶ Bₐ ⁆                           ＝⟨ Ⅳ    ⟩
   ⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ j (β m)  ∧[ 𝒪 X ] ¬𝒻⋆ (β m)) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ∣ (m , n) ∶ Bₐ × Bₐ ⁆                ＝⟨ foo  ⟩
   (⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ j (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆)  ∧[ 𝒪 X ] (⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ k (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆) ＝⟨ refl ⟩
   f⁻⁺₂ 𝒿 ∧[ 𝒪 X ] f⁻⁺₂ 𝓀                                                                                                ＝⟨ Ⅴ    ⟩
   f⁻⁺ 𝒿 ∧[ 𝒪 X ] f⁻⁺ 𝓀                                                                                                  ∎
    where
     Ⅰ = f⁻⁺₂-equiv-f⁻⁺₁ (𝒿 ∧[ 𝒪 Patch-A ] 𝓀)
     Ⅱ = ap
          (λ - → ⋁[ 𝒪 X ] (Bₐ , -))
          (dfunext fe λ n →
            ap
             (λ - → - ∧[ 𝒪 X ] ¬𝒻⋆ (β n))
             (frame-homomorphisms-preserve-meets (𝒪 A) (𝒪 X) 𝒻 (j (β n)) (k (β n))))
     Ⅲ = ap
          (λ - → ⋁[ 𝒪 X ] (Bₐ , -))
          (dfunext fe λ n →
            let
             𝕒 = ap
                  (λ - → (𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (β n)) ∧[ 𝒪 X ] -)
                  (∧[ 𝒪 X ]-is-idempotent (¬𝒻⋆ (β n)))
             𝕓 = ∧[ 𝒪 X ]-is-associative
                  (𝒻 ⋆∙ j (β n))
                  (𝒻 ⋆∙ k (β n))
                  (¬𝒻⋆ (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ⁻¹
             𝕔 = ap
                  (λ - → 𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] -)
                  (∧[ 𝒪 X ]-is-associative (𝒻 ⋆∙ k (β n)) (¬𝒻⋆ (β n)) (¬𝒻⋆ (β n)))
             𝕕 = ap
                  (λ - → 𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] (- ∧[ 𝒪 X ] ¬𝒻⋆ (β n)))
                  (∧[ 𝒪 X ]-is-commutative (𝒻 ⋆∙ k (β n)) (¬𝒻⋆ (β n)))
             𝕖 = ap
                  (λ - → 𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] -)
                  (∧[ 𝒪 X ]-is-associative (¬𝒻⋆ (β n)) (𝒻 ⋆∙ k (β n)) (¬𝒻⋆ (β n)) ⁻¹)
             𝕗 = ∧[ 𝒪 X ]-is-associative
                  (𝒻 ⋆∙ j (β n))
                  (¬𝒻⋆ (β n))
                  (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] (¬𝒻⋆ (β n)))
            in
             𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)                      ＝⟨ 𝕒 ⟩
             𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] (¬𝒻⋆ (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))     ＝⟨ 𝕓 ⟩
             𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] (¬𝒻⋆ (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)))   ＝⟨ 𝕔 ⟩
             𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] (((𝒻 ⋆∙ k (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ＝⟨ 𝕕 ⟩
             𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] ((¬𝒻⋆ (β n) ∧[ 𝒪 X ] 𝒻 ⋆∙ (k (β n))) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ＝⟨ 𝕖 ⟩
             𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] (¬𝒻⋆ (β n) ∧[ 𝒪 X ] ((𝒻 ⋆∙ k (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))) ＝⟨ 𝕗 ⟩
             (𝒻 ⋆∙ j (β n)  ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))  ∎)
     lhs₁ = ⁅ (𝒻 ⋆∙ j (β n)  ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ∣ n ∶ Bₐ ⁆
     rhs₁ = ⁅ (𝒻 ⋆∙ j (β m)  ∧[ 𝒪 X ] ¬𝒻⋆ (β m)) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ∣ (m , n) ∶ Bₐ × Bₐ ⁆

     Ⅳ   = bicofinal-implies-same-join (𝒪 X) lhs₁ rhs₁ † ‡
            where
             † : cofinal-in (𝒪 X) lhs₁ rhs₁ holds
             † n = ∣ (n , n) , ≤-is-reflexive (poset-of (𝒪 X)) (lhs₁ [ n ]) ∣

             ‡ : cofinal-in (𝒪 X) rhs₁ lhs₁ holds
             ‡ (m , n) = ∥∥-rec ∃-is-prop ϡ ※
              where
               ϡ : (Σ o ꞉ Bₐ , β o ＝ β m ∨[ 𝒪 A ] β n)
                 → ∃ o ꞉ Bₐ ,
                    (rhs₁ [ (m , n) ] ≤[ poset-of (𝒪 X) ] lhs₁ [ o ]) holds
               ϡ (o , p) = ∣ o , ϟ ∣
                where
                 𝕒₁ = ∧[ 𝒪 X ]-is-associative
                       (𝒻 ⋆∙ j (β m))
                       (¬𝒻⋆ (β m))
                       (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ⁻¹
                 𝕒₂ = ap
                       (λ - → 𝒻 ⋆∙ j (β m) ∧[ 𝒪 X ] -)
                       (∧[ 𝒪 X ]-is-associative (¬𝒻⋆ (β m)) (𝒻 ⋆∙ k (β n)) (¬𝒻⋆ (β n)))
                 𝕒₃ = ap
                       (λ - → 𝒻 ⋆∙ j (β m) ∧[ 𝒪 X ] (- ∧[ 𝒪 X ] ¬𝒻⋆ (β n)))
                       (∧[ 𝒪 X ]-is-commutative (¬𝒻⋆ (β m)) (𝒻 ⋆∙ k (β n)))
                 𝕒₄ = ap
                       (λ - → 𝒻 ⋆∙ j (β m) ∧[ 𝒪 X ] -)
                       (∧[ 𝒪 X ]-is-associative (𝒻 ⋆∙ k (β n)) (¬𝒻⋆ (β m)) (¬𝒻⋆ (β n)) ⁻¹)
                 𝕒₅ = ∧[ 𝒪 X ]-is-associative
                       (𝒻 ⋆∙ j (β m))
                       (𝒻 ⋆∙ k (β n))
                       (¬𝒻⋆ (β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))
                 𝕒₆ = ap
                       (λ - → - ∧[ 𝒪 X ] (¬𝒻⋆ (β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)))
                       (frame-homomorphisms-preserve-meets (𝒪 A) (𝒪 X) 𝒻 (j (β m)) (k (β n)) ⁻¹)

                 𝕒  = (𝒻 ⋆∙ j (β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β m)) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))     ＝⟨ 𝕒₁ ⟩
                      𝒻 ⋆∙ j (β m) ∧[ 𝒪 X ] (¬𝒻⋆ (β m) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)))     ＝⟨ 𝕒₂ ⟩
                      𝒻 ⋆∙ j (β m) ∧[ 𝒪 X ] ((¬𝒻⋆ (β m) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))     ＝⟨ 𝕒₃ ⟩
                      𝒻 ⋆∙ j (β m) ∧[ 𝒪 X ] (𝒻 ⋆∙ (k (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))     ＝⟨ 𝕒₄ ⟩
                      𝒻 ⋆∙ j (β m) ∧[ 𝒪 X ] (𝒻 ⋆∙ (k (β n)) ∧[ 𝒪 X ] (¬𝒻⋆ (β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)))   ＝⟨ 𝕒₅ ⟩
                      (𝒻 ⋆∙ j (β m) ∧[ 𝒪 X ] 𝒻 ⋆∙ (k (β n))) ∧[ 𝒪 X ] (¬𝒻⋆ (β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))   ＝⟨ 𝕒₆ ⟩
                      (𝒻 ⋆∙ (j (β m) ∧[ 𝒪 A ] k (β n))) ∧[ 𝒪 X ] (¬𝒻⋆ (β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))        ∎
                 𝕓₁ = j (β m) ∧[ 𝒪 A ] k (β n)   ≤⟨ ∧[ 𝒪 A ]-lower₁ (j (β m)) (k (β n)) ⟩
                      j (β m)                    ≤⟨ ♠                                   ⟩
                      j (β m ∨[ 𝒪 A ] β n)       ＝⟨ ap j p ⁻¹                          ⟩ₚ
                      j (β o)                    ■
                       where
                        open PosetReasoning (poset-of (𝒪 A))
                        ♠ = nuclei-are-monotone
                             (𝒪 A)
                             (nucleus-of 𝒿)
                             (_ , _)
                             (∨[ 𝒪 A ]-upper₁ (β m) (β n))
                 𝕓₂ = j (β m) ∧[ 𝒪 A ] k (β n) ≤⟨ ∧[ 𝒪 A ]-lower₂ (j (β m)) (k (β n)) ⟩
                      k (β n)                  ≤⟨ ♠                                   ⟩
                      k (β m ∨[ 𝒪 A ] β n)     ＝⟨ ap k p ⁻¹ ⟩ₚ
                      k (β o)                  ■
                       where
                        open PosetReasoning (poset-of (𝒪 A))

                        ♠ = nuclei-are-monotone
                             (𝒪 A)
                             (nucleus-of 𝓀)
                             (_ , _)
                             (∨[ 𝒪 A ]-upper₂ (β m) (β n))
                 𝕓  = ∧[ 𝒪 X ]-left-monotone
                       (frame-morphisms-are-monotonic
                         (𝒪 A)
                         (𝒪 X)
                         (pr₁ 𝒻)
                         (pr₂ 𝒻)
                         ((j (β m) ∧[ 𝒪 A ] k (β n)) , (j (β o) ∧[ 𝒪 A ] k (β o)))
                         (∧[ 𝒪 A ]-greatest (j (β o)) (k (β o)) (meet-of (𝒪 A) (j (β m)) (k (β n))) 𝕓₁ 𝕓₂))

                 ♣ : ((¬𝒻⋆ (β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ≤[ poset-of (𝒪 X) ] ¬𝒻⋆ (β o)) holds
                 ♣ = ¬𝒻⋆ (β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)                                          ＝⟨ refl ⟩ₚ
                     ((𝒻 ⋆∙ β m) ==> 𝟎[ 𝒪 X ]) ∧[ 𝒪 X ] ((𝒻 ⋆∙ β n) ==> 𝟎[ 𝒪 X ])  ＝⟨ 𝟏    ⟩ₚ
                     ((𝒻 ⋆∙ (β m) ∨[ 𝒪 X ] (𝒻 ⋆∙ (β n))) ==> 𝟎[ 𝒪 X ])             ＝⟨ 𝟐    ⟩ₚ
                     ((𝒻 ⋆∙ (β m ∨[ 𝒪 A ] β n)) ==> 𝟎[ 𝒪 X ])                      ＝⟨ 𝟑    ⟩ₚ
                     ¬𝒻⋆ (β o)                                                         ■
                      where
                       open PosetReasoning (poset-of (𝒪 X))

                       𝟏 = ==>-left-reverses-joins (𝒻 ⋆∙ (β m)) (𝒻 ⋆∙ (β n)) 𝟎[ 𝒪 X ]
                       𝟐 = ap
                            (λ - → - ==> 𝟎[ 𝒪 X ])
                            (frame-homomorphisms-preserve-binary-joins (𝒪 A) (𝒪 X) 𝒻 (β m) (β n) ⁻¹)
                       𝟑 = ap (λ - → (𝒻 ⋆∙ -) ==> 𝟎[ 𝒪 X ]) (p ⁻¹)

                 𝕔 = ∧[ 𝒪 X ]-right-monotone ♣
                 𝕕 = ap
                      (λ - → - ∧[ 𝒪 X ] ¬𝒻⋆ (β o))
                      (frame-homomorphisms-preserve-meets
                        (𝒪 A)
                        (𝒪 X)
                        𝒻
                        (j (β o))
                        (k (β o)))
                 𝕖 =
                  (𝒻 ⋆∙ j (β o) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (β o)) ∧[ 𝒪 X ] ¬𝒻⋆ (β o)                  ＝⟨ 𝟏 ⟩
                  (𝒻 ⋆∙ j (β o) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (β o)) ∧[ 𝒪 X ] (¬𝒻⋆ (β o) ∧[ 𝒪 X ] ¬𝒻⋆ (β o)) ＝⟨ 𝟐 ⟩
                  𝒻 ⋆∙ j (β o) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β o) ∧[ 𝒪 X ] (¬𝒻⋆ (β o) ∧[ 𝒪 X ] ¬𝒻⋆ (β o))) ＝⟨ 𝟑 ⟩
                  𝒻 ⋆∙ j (β o) ∧[ 𝒪 X ] ((𝒻 ⋆∙ k (β o) ∧[ 𝒪 X ] ¬𝒻⋆ (β o)) ∧[ 𝒪 X ] ¬𝒻⋆ (β o)) ＝⟨ 𝟒 ⟩
                  𝒻 ⋆∙ j (β o) ∧[ 𝒪 X ] ((¬𝒻⋆ (β o) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (β o)) ∧[ 𝒪 X ] ¬𝒻⋆ (β o)) ＝⟨ 𝟓 ⟩
                  𝒻 ⋆∙ j (β o) ∧[ 𝒪 X ] (¬𝒻⋆ (β o) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β o) ∧[ 𝒪 X ] ¬𝒻⋆ (β o))) ＝⟨ 𝟔 ⟩
                  (𝒻 ⋆∙ j (β o) ∧[ 𝒪 X ] ¬𝒻⋆ (β o)) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β o) ∧[ 𝒪 X ] ¬𝒻⋆ (β o)) ∎
                   where
                    𝟏 = ap
                         (λ - → (𝒻 ⋆∙ j (β o) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (β o)) ∧[ 𝒪 X ] -)
                         (∧[ 𝒪 X ]-is-idempotent (¬𝒻⋆ (β o)))
                    𝟐 = ∧[ 𝒪 X ]-is-associative
                         (𝒻 ⋆∙ j (β o))
                         (𝒻 ⋆∙ k (β o))
                         (¬𝒻⋆ (β o) ∧[ 𝒪 X ] ¬𝒻⋆ (β o)) ⁻¹
                    𝟑 = ap
                         (λ - → 𝒻 ⋆∙ (j (β o)) ∧[ 𝒪 X ] -)
                         (∧[ 𝒪 X ]-is-associative (𝒻 ⋆∙ k (β o)) (¬𝒻⋆ (β  o)) (¬𝒻⋆ (β o)))
                    𝟒 = ap
                         (λ - → 𝒻 ⋆∙ j (β o) ∧[ 𝒪 X ] (- ∧[ 𝒪 X ] ¬𝒻⋆ (β o)))
                         (∧[ 𝒪 X ]-is-commutative (𝒻 ⋆∙ k (β o)) (¬𝒻⋆ (β o)))
                    𝟓 = ap
                         (λ - → 𝒻 ⋆∙ j (β o) ∧[ 𝒪 X ] -)
                         (∧[ 𝒪 X ]-is-associative (¬𝒻⋆ (β o)) (𝒻 ⋆∙ k (β o)) (¬𝒻⋆ (β o)) ⁻¹)
                    𝟔 = ∧[ 𝒪 X ]-is-associative
                         (𝒻 ⋆∙ j (β o))
                         (¬𝒻⋆ (β o))
                         (𝒻 ⋆∙ k (β o) ∧[ 𝒪 X ] ¬𝒻⋆ (β o))

                 open PosetReasoning (poset-of (𝒪 X))

                 ϟ = (𝒻 ⋆∙ j (β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β m)) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ＝⟨ 𝕒 ⟩ₚ
                     (𝒻 ⋆∙ (j (β m) ∧[ 𝒪 A ] k (β n))) ∧[ 𝒪 X ] (¬𝒻⋆ (β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))    ≤⟨ 𝕓  ⟩
                     𝒻 ⋆∙ (j (β o) ∧[ 𝒪 A ] k (β o)) ∧[ 𝒪 X ] (¬𝒻⋆ (β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))      ≤⟨ 𝕔  ⟩
                     𝒻 ⋆∙ (j (β o) ∧[ 𝒪 A ] k (β o)) ∧[ 𝒪 X ] ¬𝒻⋆ (β o)                           ＝⟨ 𝕕 ⟩ₚ
                     (𝒻 ⋆∙ j (β o) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (β o)) ∧[ 𝒪 X ] ¬𝒻⋆ (β o)                      ＝⟨ 𝕖 ⟩ₚ
                     (𝒻 ⋆∙ j (β o) ∧[ 𝒪 X ] ¬𝒻⋆ (β o)) ∧[ 𝒪 X ] (𝒻 ⋆∙ k (β o) ∧[ 𝒪 X ] ¬𝒻⋆ (β o)) ■

               ※ : ∃ o ꞉ Bₐ , β o ＝ β m ∨[ 𝒪 A ] β n
               ※ = ∥∥-rec
                    ∃-is-prop
                    (λ { (o , p) → ∣ o , (p ⁻¹) ∣ })
                    (compact-opens-are-basic-in-compact-frames
                      (𝒪 A)
                      (Bₐ , β)
                      (pr₁ (pr₂ σᴰ))
                      (spectral-implies-compact (𝒪 A) σ)
                      (β m ∨[ 𝒪 A ] β n)
                      (compacts-are-closed-under-joins
                        (𝒪 A)
                        (β m)
                        (β n)
                        (pr₂ (βₖ m))
                        (pr₂ (βₖ n))))

     foo = distributivity+
            (𝒪 X)
            ⁅ (𝒻 ⋆∙ j (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆
            ⁅ (𝒻 ⋆∙ k (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆ ⁻¹
     Ⅴ = ap₂
          (λ x y → x ∧[ 𝒪 X ] y)
          (f⁻⁺₂-equiv-f⁻⁺₁ 𝒿 ⁻¹)
          (f⁻⁺₂-equiv-f⁻⁺₁ 𝓀 ⁻¹)

  open ClosedNucleus X (stone-locales-are-spectral (𝒪 X) (𝕜 , ∣ 𝕫ᴰ ∣))
   using    ()
   renaming (‘_’ to ‘_’ₓ)

  -- Igor's definition.
  closed-image : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 A ⟩ → ⟨ 𝒪 A ⟩
  closed-image U = (𝒻₊ ∘ ‘ U ’ₓ .pr₁) ∘ 𝒻 ⋆∙_

  closed-image-is-inflationary : (U : ⟨ 𝒪 X ⟩) (V : ⟨ 𝒪 A ⟩)
                               → (V ≤[ poset-of (𝒪 A) ] closed-image U V) holds
  closed-image-is-inflationary U V =
   adjunction-inequality-forwardₓ 𝒻 (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V) V †
    where
     † : (𝒻 ⋆∙ V ≤[ poset-of (𝒪 X) ] (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V)) holds
     † = ∨[ 𝒪 X ]-upper₂ U (𝒻 ⋆∙ V)

  closed-image-is-idempotent : (U : ⟨ 𝒪 X ⟩)
                             → is-idempotent (𝒪 A) (closed-image U) holds
  closed-image-is-idempotent U V =
   let
    open PosetReasoning (poset-of (𝒪 A))
   in
    closed-image U (closed-image U V)                    ＝⟨ refl    ⟩ₚ
    𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ (𝒻₊ (U ∨[ 𝒪 X ] (𝒻 ⋆∙ V))))      ≤⟨ †        ⟩
    𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V)                               ＝⟨ refl    ⟩ₚ
    closed-image U V                                     ■
   where
     ‡ : (𝒻 ⋆∙ 𝒻₊ (U ∨[ 𝒪 X ] (𝒻 ⋆∙ 𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V)))
           ≤[ poset-of (𝒪 X) ]
          (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V)) holds
     ‡ = 𝒻 ⋆∙ 𝒻₊ (U ∨[ 𝒪 X ] (𝒻 ⋆∙ 𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V)))  ≤⟨ Ⅰ   ⟩
         U ∨[ 𝒪 X ] (𝒻 ⋆∙ 𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V))            ≤⟨ Ⅱ   ⟩
         U ∨[ 𝒪 X ] (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V)                      ＝⟨ Ⅲ  ⟩ₚ
         (U ∨[ 𝒪 X ] U) ∨[ 𝒪 X ] 𝒻 ⋆∙ V                      ＝⟨ Ⅳ  ⟩ₚ
         U ∨[ 𝒪 X ] 𝒻 ⋆∙ V                                   ■
      where
       open PosetReasoning (poset-of (𝒪 X))

       Ⅰ = counitₐ
            𝒻⁺ₘ
            𝒻₊ₘ
            (f₊-is-right-adjoint-of-f⁺ 𝒻)
            (U ∨[ 𝒪 X ] (𝒻 ⋆∙ 𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V)))
       Ⅱ = ∨[ 𝒪 X ]-right-monotone
            (counitₐ 𝒻⁺ₘ 𝒻₊ₘ (f₊-is-right-adjoint-of-f⁺ 𝒻) (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V))
       Ⅲ = ∨[ 𝒪 X ]-assoc U U (𝒻 ⋆∙ V) ⁻¹
       Ⅳ = ap (λ - → - ∨[ 𝒪 X ] 𝒻 ⋆∙ V) (∨[ 𝒪 X ]-is-idempotent U ⁻¹)

     † = adjunction-inequality-forwardₓ
          𝒻
          (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V)
          (𝒻₊ (U ∨[ 𝒪 X ] (𝒻 ⋆∙ 𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V))))
          ‡

  closed-image-preserves-meets : (U : ⟨ 𝒪 X ⟩)
                               → preserves-binary-meets (𝒪 A) (𝒪 A) (closed-image U) holds
  closed-image-preserves-meets U V₁ V₂ =
   𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ (V₁ ∧[ 𝒪 A ] V₂))                        ＝⟨ Ⅰ    ⟩
   𝒻₊ (U ∨[ 𝒪 X ] (𝒻 ⋆∙ V₁ ∧[ 𝒪 X ] 𝒻 ⋆∙ V₂))                   ＝⟨ Ⅱ    ⟩
   𝒻₊ ((U ∨[ 𝒪 X ] 𝒻 ⋆∙ V₁) ∧[ 𝒪 X ] (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V₂))      ＝⟨ Ⅲ    ⟩
   𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V₁) ∧[ 𝒪 A ] 𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V₂)     ＝⟨ refl ⟩
   closed-image U V₁ ∧[ 𝒪 A ] closed-image U V₂                 ∎
    where
     Ⅰ = ap
          (λ - → 𝒻₊ (U ∨[ 𝒪 X ] -))
          (frame-homomorphisms-preserve-meets (𝒪 A) (𝒪 X) 𝒻 V₁ V₂)
     Ⅱ = ap 𝒻₊ (binary-distributivity-op (𝒪 X) U (𝒻 ⋆∙ V₁) (𝒻 ⋆∙ V₂))
     Ⅲ = f₊-preserves-binary-meetsₓ 𝒻 (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V₁) (U ∨[ 𝒪 X ] (𝒻 ⋆∙ V₂))

  closed-image-is-nucleus : (U : ⟨ 𝒪 X ⟩)
                          → is-nucleus (𝒪 A) (closed-image U) holds
  closed-image-is-nucleus U = closed-image-is-inflationary U
                            , closed-image-is-idempotent U
                            , closed-image-preserves-meets U

  closed-image-is-sc : (U : ⟨ 𝒪 X ⟩)
                     → is-scott-continuous (𝒪 A) (𝒪 A) (closed-image U) holds
  closed-image-is-sc U =
   ∘-of-scott-cont-is-scott-cont (𝒪 A) (𝒪 X) (𝒪 A) (𝒻₊ ∘ ‘ U ’ₓ .pr₁) (𝒻 ⋆∙_) † ‡
    where
     † : is-scott-continuous (𝒪 X) (𝒪 A) (𝒻₊ ∘ ‘ U ’ₓ .pr₁) holds
     † = ∘-of-scott-cont-is-scott-cont
          (𝒪 X)
          (𝒪 X)
          (𝒪 A)
          𝒻₊
          (‘ U ’ₓ .pr₁)
          (spectral-maps-are-perfect 𝒻 σ μ)
          (∨-is-scott-continuous (𝒪 X) U)
          where
           open PerfectMaps X A A-has-basis


     ‡ : is-scott-continuous (𝒪 A) (𝒪 X) (𝒻 ⋆∙_) holds
     ‡ = join-preserving-implies-scott-continuous
          (𝒪 A)
          (𝒪 X)
          (𝒻 ⋆∙_)
          (frame-homomorphisms-preserve-all-joins (𝒪 A) (𝒪 X) 𝒻)



  f⁻⁺-preserves-joins : is-join-preserving (𝒪 Patchₛ-A) (𝒪 X) f⁻⁺ holds
  f⁻⁺-preserves-joins = aft-forward 𝒻⁻⋆ₘ †
   where
    f⁻₊ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 Patchₛ-A ⟩
    f⁻₊ U = closed-image U ,  closed-image-is-nucleus U  , closed-image-is-sc U

    f⁻₊-is-monotone : is-monotonic (poset-of (𝒪 X)) (poset-of (𝒪 Patchₛ-A)) f⁻₊ holds
    f⁻₊-is-monotone (U , V) p n = pr₂ 𝒻₊ₘ _ (∨[ 𝒪 X ]-left-monotone p)

    f⁻₊ₘ : poset-of (𝒪 X) ─m→ poset-of (𝒪 Patchₛ-A)
    f⁻₊ₘ = f⁻₊ , f⁻₊-is-monotone

    open IgorsLemma  X A A-has-basis
    open PerfectMaps X A A-has-basis

    negation-lemma : {U V W : ⟨ 𝒪 X ⟩}
                   → is-clopen₀ (𝒪 X) V
                   → (U ≤[ poset-of (𝒪 X) ] (V ∨[ 𝒪 X ] W)) holds
                   → ((U ∧[ 𝒪 X ] (V ==> 𝟎[ 𝒪 X ]))
                       ≤[ poset-of (𝒪 X) ]
                      W) holds
    negation-lemma {U} {V} {W} (V′ , p , q) φ =
     U ∧[ 𝒪 X ] (V ==> 𝟎[ 𝒪 X ])               ＝⟨ Ⅰ ⟩ₚ
     U ∧[ 𝒪 X ] V′                             ≤⟨ Ⅱ  ⟩
     (V ∨[ 𝒪 X ] W) ∧[ 𝒪 X ] V′                ＝⟨ Ⅲ ⟩ₚ
     (V ∧[ 𝒪 X ] V′) ∨[ 𝒪 X ] (W ∧[ 𝒪 X ] V′)  ＝⟨ Ⅳ ⟩ₚ
     𝟎[ 𝒪 X ] ∨[ 𝒪 X ] (W ∧[ 𝒪 X ] V′)         ＝⟨ Ⅴ ⟩ₚ
     W ∧[ 𝒪 X ] V′                             ≤⟨  Ⅵ ⟩
     W                                         ■
      where
       open PosetReasoning (poset-of (𝒪 X))
       open LemmasAboutHeytingComplementation X X-has-basis

       Ⅰ = ap
            (λ - → U ∧[ 𝒪 X ] -)
            (complement-is-heyting-complement V V′ (p , q) ⁻¹)
       Ⅱ = ∧[ 𝒪 X ]-left-monotone φ
       Ⅲ = binary-distributivity-right (𝒪 X)
       Ⅳ = ap (λ - → - ∨[ 𝒪 X ] (W ∧[ 𝒪 X ] V′)) p
       Ⅴ = 𝟎-right-unit-of-∨ (𝒪 X) (W ∧[ 𝒪 X ] V′)
       Ⅵ = ∧[ 𝒪 X ]-lower₁ W V′

    negation-lemma′ : {U V W : ⟨ 𝒪 X ⟩}
                   → is-clopen₀ (𝒪 X) V
                    → ((U ∧[ 𝒪 X ] (V ==> 𝟎[ 𝒪 X ]))
                        ≤[ poset-of (𝒪 X) ]
                       W) holds
                    → (U ≤[ poset-of (𝒪 X) ] (V ∨[ 𝒪 X ] W)) holds
    negation-lemma′ {U} {V} {W} (V′ , p , q) φ =
     U                                                      ＝⟨ Ⅰ ⟩ₚ
     U ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                                    ＝⟨ Ⅱ ⟩ₚ
     U ∧[ 𝒪 X ] (V ∨[ 𝒪 X ] V′)                             ＝⟨ Ⅲ ⟩ₚ
     (U ∧[ 𝒪 X ] V) ∨[ 𝒪 X ] (U ∧[ 𝒪 X ] V′)                ＝⟨ Ⅳ ⟩ₚ
     (U ∧[ 𝒪 X ] V) ∨[ 𝒪 X ] (U ∧[ 𝒪 X ] (V ==> 𝟎[ 𝒪 X ]))  ≤⟨ Ⅴ  ⟩
     (U ∧[ 𝒪 X ] V) ∨[ 𝒪 X ] W                              ≤⟨ Ⅵ  ⟩
     V ∨[ 𝒪 X ] W                                           ■
      where
       open PosetReasoning (poset-of (𝒪 X))

       open LemmasAboutHeytingComplementation X X-has-basis

       Ⅰ =  𝟏-right-unit-of-∧ (𝒪 X) U ⁻¹
       Ⅱ = ap (λ - → U ∧[ 𝒪 X ] -) (q ⁻¹)
       Ⅲ = binary-distributivity (𝒪 X) U V V′
       Ⅳ = ap
            (λ - → (U ∧[ 𝒪 X ] V) ∨[ 𝒪 X ] (U ∧[ 𝒪 X ] -))
            (complement-is-heyting-complement V V′ (p , q))
       Ⅴ = ∨[ 𝒪 X ]-right-monotone φ
       Ⅵ = ∨[ 𝒪 X ]-left-monotone (∧[ 𝒪 X ]-lower₂ U V)

    f⁻₊-is-right-adjoint-of-f⁻⁺ : (𝒻⁻⋆ₘ ⊣ f⁻₊ₘ) holds
    f⁻₊-is-right-adjoint-of-f⁻⁺ 𝒿@(j , _) U = ϑ₁ , ϑ₂
     where

      ϑ₁ : (f⁻⁺ 𝒿 ≤[ poset-of (𝒪 X) ] U) holds
         → (𝒿 ≤[ poset-of (𝒪 Patchₛ-A) ] (f⁻₊ U)) holds
      ϑ₁ φ n =
       adjunction-inequality-forwardₓ
        𝒻
        (U ∨[ 𝒪 X ] 𝒻 ⋆∙ β n)
        (j (β n))
        ψ
         where
          open PosetReasoning (poset-of (𝒪 X))

          κ : is-clopen₀ (𝒪 X) (𝒻 ⋆∙ β n)
          κ = compacts-are-clopen-in-zero-dimensional-locales
               (𝒪 X)
               ∣ 𝕫ᴰ ∣
               (𝒻 ⋆∙ β n)
               (μ (β n) (pr₂ (βₖ n)))

          ϟ : ((𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] ((𝒻 ⋆∙ β n) ==> 𝟎[ 𝒪 X ]))
                    ≤[ poset-of (𝒪 X) ]
                   U) holds
          ϟ =
           𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] ((𝒻 ⋆∙ β n) ==> 𝟎[ 𝒪 X ]) ≤⟨ Ⅰ ⟩
           f⁻⁺₂ 𝒿                                          ＝⟨ Ⅱ   ⟩ₚ
           f⁻⁺  𝒿                                          ≤⟨ φ    ⟩
           U                                               ■
            where
             Ⅰ = ⋁[ 𝒪 X ]-upper
                  ⁅ 𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆
                  n
             Ⅱ = f⁻⁺₂-equiv-f⁻⁺₁ 𝒿 ⁻¹

          ※ : (𝒻 ⋆∙ j (β n) ≤[ poset-of (𝒪 X) ] (𝒻 ⋆∙ β n ∨[ 𝒪 X ] U)) holds
          ※ = negation-lemma′ κ ϟ

          ψ : (𝒻 ⋆∙ j (β n) ≤[ poset-of (𝒪 X) ] (U ∨[ 𝒪 X ] 𝒻 ⋆∙ β n)) holds
          ψ = 𝒻 ⋆∙ j (β n)          ≤⟨ ※ ⟩
              𝒻 ⋆∙ (β n) ∨[ 𝒪 X ] U ＝⟨ ∨[ 𝒪 X ]-is-commutative (𝒻 ⋆∙ β n) U ⟩ₚ
              U ∨[ 𝒪 X ] 𝒻 ⋆∙ (β n) ■

      S =
       ⁅ (𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)
        ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝕃 𝒿 m n holds ⁆

      ϑ₂ : (𝒿 ≤[ poset-of (𝒪 Patchₛ-A) ] (f⁻₊ U)) holds
         → (f⁻⁺ 𝒿 ≤[ poset-of (𝒪 X) ] U) holds
      ϑ₂ φ = ⋁[ 𝒪 X ]-least S (U , †)
       where
        open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

        † : (U is-an-upper-bound-of S) holds
        † (m , n , p) = goal
         where
          ψ : (U : ⟨ 𝒪 A ⟩)
            → (((‘ β m ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) .pr₁ U) ≤[ poset-of (𝒪 A)  ] j U) holds
          ψ = ≼ᵏ-implies-≼ (‘ β m ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) 𝒿 p

          κ : is-clopen₀ (𝒪 X) (𝒻 ⋆∙ β n)
          κ = compacts-are-clopen-in-zero-dimensional-locales
               (𝒪 X)
               ∣ 𝕫ᴰ ∣
               (𝒻 ⋆∙ β n)
               (μ (β n) (pr₂ (βₖ n)))

          ϡ : (T : ⟨ 𝒪 A ⟩)
            → (((𝒻 ⋆∙ (β m ∨[ 𝒪 A ] T)) ∧[ 𝒪 X ] 𝒻 ⋆∙ (β n ==>ₐ T))
                ≤[ poset-of (𝒪 X) ]
               (U ∨[ 𝒪 X ] (𝒻 ⋆∙ T))) holds
          ϡ T =
           let
            open PosetReasoning (poset-of (𝒪 X))
           in
            𝒻 ⋆∙ (β m ∨[ 𝒪 A ] T) ∧[ 𝒪 X ] 𝒻 ⋆∙ (β n ==>ₐ T)  ＝⟨ Ⅰ ⟩ₚ
            𝒻 ⋆∙ ((β m ∨[ 𝒪 A ] T) ∧[ 𝒪 A ] (β n ==>ₐ T))     ≤⟨ Ⅱ  ⟩
            U ∨[ 𝒪 X ] (𝒻 ⋆∙ T)                               ■
           where
            ♣ : (((β m ∨[ 𝒪 A ] T) ∧[ 𝒪 A ] (β n ==>ₐ T))
                  ≤[ poset-of (𝒪 A) ]
                 𝒻₊ (U ∨[ 𝒪 X ] (𝒻 ⋆∙ T))) holds
            ♣ = (β m ∨[ 𝒪 A ] T) ∧[ 𝒪 A ] (β n ==>ₐ T)    ≤⟨ Ⅰ ⟩
                j T                                       ≤⟨ Ⅱ ⟩
                𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ T)                    ■
             where
              open PosetReasoning (poset-of (𝒪 A))

              Ⅰ = ≼ᵏ-implies-≼ (‘ β m ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) 𝒿 p T
              Ⅱ = ≼ᵏ-implies-≼ 𝒿 (f⁻₊ U) φ T

            Ⅰ = frame-homomorphisms-preserve-meets
                 (𝒪 A)
                 (𝒪 X)
                 𝒻
                 (β m ∨[ 𝒪 A ] T)
                 (β n ==>ₐ T) ⁻¹
            Ⅱ = adjunction-inequality-backwardₓ
                 𝒻
                 (U ∨[ 𝒪 X ] 𝒻 ⋆∙ T)
                 ((β m ∨[ 𝒪 A ] T) ∧[ 𝒪 A ] (β n ==>ₐ T))
                 ♣

          ϟ : (𝒻 ⋆∙ β m ≤[ poset-of (𝒪 X) ] (U ∨[ 𝒪 X ] 𝒻 ⋆∙ β n)) holds
          ϟ = igors-lemma-⇐ 𝒻 (β m) (β n) U ϡ

          ϑ : (𝒻 ⋆∙ β m ≤[ poset-of (𝒪 X) ] (𝒻 ⋆∙ β n ∨[ 𝒪 X ] U)) holds
          ϑ = 𝒻 ⋆∙ β m               ≤⟨ ϟ ⟩
              U ∨[ 𝒪 X ] 𝒻 ⋆∙ β n    ＝⟨ ∨[ 𝒪 X ]-is-commutative U (𝒻 ⋆∙ β n) ⟩ₚ
              𝒻 ⋆∙ β n ∨[ 𝒪 X ] U    ■
               where
                open PosetReasoning (poset-of (𝒪 X))

          goal : (((𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ≤[ poset-of (𝒪 X) ] U) holds
          goal = negation-lemma κ ϑ

    † : has-right-adjoint 𝒻⁻⋆ₘ
    † = f⁻₊ₘ , f⁻₊-is-right-adjoint-of-f⁻⁺

  open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
   using () renaming (_is-lub-of_ to _is-lub-ofₓ_)

  𝒻⁻-γ : (S : Fam 𝓤 ⟨ 𝒪 Patchₛ-A ⟩)
       → ((f⁻⁺ (⋁[ 𝒪 Patchₛ-A ] S)) is-lub-ofₓ ⁅ f⁻⁺ 𝒿 ∣ 𝒿 ε S ⁆) holds
  𝒻⁻-γ S =
   transport
    (λ - → (- is-lub-ofₓ ⁅ f⁻⁺ 𝒿 ∣ 𝒿 ε S ⁆) holds)
    (f⁻⁺-preserves-joins S ⁻¹)
    (⋁[ 𝒪 X ]-upper ⁅ f⁻⁺ 𝒿 ∣ 𝒿 ε S ⁆ , ⋁[ 𝒪 X ]-least ⁅ f⁻⁺ 𝒿 ∣ 𝒿 ε S ⁆)

  main-lemma : (𝒻⁻₀ : X ─c→ Patchₛ-A)
             → (n : Bₐ)
             → is-complement-of (𝒪 X) (𝒻⁻₀ .pr₁ ¬‘ βₖ n ’) (𝒻⁻₀ .pr₁ ‘ β n ’)
  main-lemma 𝒻⁻₀ n =
   frame-homomorphisms-preserve-complements (𝒪 Patchₛ-A) (𝒪 X) 𝒻⁻₀ †
    where
     open PatchComplementation A σᴰ

     ‡ : is-boolean-complement-of (𝒪 Patchₛ-A) ¬‘ βₖ n ’ ‘ β n ’ holds
     ‡ = {!!}

     † : is-complement-of (𝒪 Patchₛ-A) ‘ β n ’ ¬‘ βₖ n ’
     † = complementation-is-symmetric (𝒪 Patchₛ-A) ¬‘ βₖ n ’ ‘ β n ’ ‡

{--

  𝒻⁻-makes-the-diagram-commute : (U : ⟨ 𝒪 A ⟩) → 𝒻 ⋆∙ U  ＝ f⁻⁺ ‘ U ’
  𝒻⁻-makes-the-diagram-commute U = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
   where
    𝟎-is-basic : ∃ t ꞉ Bₐ , 𝟎[ 𝒪 A ] ＝ β t
    𝟎-is-basic = compact-opens-are-basic-in-compact-frames
                  (𝒪 A)
                  (Bₐ , β)
                  β-is-directed-basis
                  (spectral-implies-compact (𝒪 A) ∣ σᴰ ∣)
                  𝟎[ 𝒪 A ]
                  (𝟎-is-compact (𝒪 A))
     where
      ※ : Σ t ꞉ Bₐ , is-top (𝒪 A) (β t) holds → ∃ (λ t → 𝟏[ 𝒪 A ] ＝ β t)
      ※ (t , p) = ∣ t , (𝟏-is-unique (𝒪 A) (β t) p ⁻¹) ∣

    ℒ : Fam 𝓤 Bₐ
    ℒ = covering-index-family (𝒪 A) (Bₐ , β) β-is-basis-for-A U

    ℒ-covers-U : U ＝ ⋁[ 𝒪 A ] ⁅ β l ∣ l ε ℒ ⁆
    ℒ-covers-U = covers (𝒪 A) (Bₐ , β) β-is-basis-for-A U

    Ⅲ : ((⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (β l) ∣ l ε ℒ ⁆) ≤[ poset-of (𝒪 X) ] f⁻⁺ ‘ U ’) holds
    Ⅲ = ⋁[ 𝒪 X ]-least ⁅ 𝒻 ⋆∙ (β l) ∣ l ε ℒ ⁆ (f⁻⁺ ‘ U ’ , ※)
     where
      open Joins (λ x y → x ≤[ poset-of (𝒪 A) ] y)
       using () renaming (_is-lub-of_ to _is-lub-ofₐ_;
                          _is-an-upper-bound-of_ to _is-an-upper-bound-ofₐ_)

      ※ : (l : index ℒ) → (𝒻 ⋆∙ (β (ℒ [ l ])) ≤[ poset-of (𝒪 X) ] f⁻⁺ ‘ U ’) holds
      ※ l = ∥∥-rec
             (holds-is-prop (𝒻 ⋆∙ (β (ℒ [ l ])) ≤[ poset-of (𝒪 X) ] f⁻⁺ ‘ U ’))
             ♣
             𝟎-is-basic
       where
        ♣ : Σ t ꞉ Bₐ , 𝟎[ 𝒪 A ] ＝ β t
          → (𝒻 ⋆∙ β (ℒ [ l ]) ≤[ poset-of (𝒪 X) ] f⁻⁺ ‘ U ’) holds
        ♣ (t , p) =
         let
          open PosetReasoning (poset-of (𝒪 X))
         in
          𝒻 ⋆∙ (β (ℒ [ l ]))                         ＝⟨ 𝟏 ⟩ₚ
          𝒻 ⋆∙ (β (ℒ [ l ])) ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]       ＝⟨ 𝟐 ⟩ₚ
          𝒻 ⋆∙ (β (ℒ [ l ])) ∧[ 𝒪 X ] ¬𝒻⋆ 𝟎[ 𝒪 A ]   ＝⟨ 𝟑 ⟩ₚ
          𝒻 ⋆∙ (β (ℒ [ l ])) ∧[ 𝒪 X ] ¬𝒻⋆ (β t)      ≤⟨ 𝟒  ⟩
          f⁻⁺ ‘ U ’                                  ■
           where
            ♠ = λ n →
             let
              open PosetReasoning (poset-of (𝒪 A))
              ※ = β (ℒ [ l ])                ≤⟨ ⋁[ 𝒪 A ]-upper ⁅ β l ∣ l ε ℒ ⁆ l ⟩
                  ⋁[ 𝒪 A ] ⁅ β l ∣ l ε ℒ ⁆   ＝⟨ ℒ-covers-U ⁻¹                   ⟩ₚ
                  U                          ≤⟨ ∨[ 𝒪 A ]-upper₁ U (β n)          ⟩
                  U ∨[ 𝒪 A ] β n             ■
              𝕒 = ap (λ - → (β (ℒ [ l ]) ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] (- ==>ₐ β n)) (p ⁻¹)
              𝕓 = ap
                   (λ - → (β (ℒ [ l ]) ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] -)
                   (only-𝟏-is-above-𝟏
                     (𝒪 A)
                     (𝟎[ 𝒪 A ] ==>ₐ β n)
                     (ex-falso-quodlibetₐ (β n)))
              𝕔 = 𝟏-right-unit-of-∧ (𝒪 A) (β (ℒ [ l ]) ∨[ 𝒪 A ] β n)
              𝕕 = ∨[ 𝒪 A ]-least ※ (∨[ 𝒪 A ]-upper₂ U (β n))
             in
              (β (ℒ [ l ]) ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] (β t ==>ₐ β n)      ＝⟨ 𝕒 ⟩ₚ
              (β (ℒ [ l ]) ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] (𝟎[ 𝒪 A ] ==>ₐ β n) ＝⟨ 𝕓 ⟩ₚ
              (β (ℒ [ l ]) ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] 𝟏[ 𝒪 A ]            ＝⟨ 𝕔 ⟩ₚ
              β (ℒ [ l ]) ∨[ 𝒪 A ] β n                                ≤⟨ 𝕕  ⟩
              U ∨[ 𝒪 A ] β n                                          ■

            𝟏 = 𝟏-right-unit-of-∧ (𝒪 X) (𝒻 ⋆∙ (β (ℒ [ l ]))) ⁻¹
            𝟐 = ap (λ - → 𝒻 ⋆∙ β (ℒ [ l ]) ∧[ 𝒪 X ] -)   (¬𝒻⋆𝟎-is-𝟏 ⁻¹)
            𝟑 = ap (λ - → 𝒻 ⋆∙ β (ℒ [ l ]) ∧[ 𝒪 X ] ¬𝒻⋆ -) p
            𝟒 = ⋁[ 𝒪 X ]-upper
                 ⁅ (𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝕃 ‘ U ’ m n holds ⁆
                 (ℒ [ l ] , t , ♠)

    † : (𝒻 ⋆∙ U ≤[ poset-of (𝒪 X) ] f⁻⁺ ‘ U ’) holds
    † =
     let
      open PosetReasoning (poset-of (𝒪 X))
     in
      𝒻 ⋆∙ U                            ＝⟨ Ⅰ ⟩ₚ
      𝒻 ⋆∙ (⋁[ 𝒪 A ] ⁅ β l ∣ l ε ℒ ⁆)   ＝⟨ Ⅱ ⟩ₚ
      ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (β l) ∣ l ε ℒ ⁆   ≤⟨  Ⅲ ⟩
      f⁻⁺ ‘ U ’                         ■
       where
        Ⅰ = ap (𝒻 ⋆∙_) ℒ-covers-U
        Ⅱ = frame-homomorphisms-preserve-all-joins (𝒪 A) (𝒪 X) 𝒻 ⁅ β l ∣ l ε ℒ ⁆

    ‡ : (f⁻⁺ ‘ U ’ ≤[ poset-of (𝒪 X) ] 𝒻 ⋆∙ U) holds
    ‡ = f⁻⁺  ‘ U ’  ＝⟨ f⁻⁺₂-equiv-f⁻⁺₁ ‘ U ’ ⟩ₚ
        f⁻⁺₂ ‘ U ’  ≤⟨ ※                      ⟩
        𝒻 ⋆∙ U      ■
     where
      open PosetReasoning (poset-of (𝒪 X))

      ϟ : (n : Bₐ)
        → ((𝒻 ⋆∙ (U ∨[ 𝒪 A ] β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ≤[ poset-of (𝒪 X) ] 𝒻 ⋆∙ U) holds
      ϟ n =
       𝒻 ⋆∙ (U ∨[ 𝒪 A ] β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)                             ＝⟨ 𝟏 ⟩ₚ
       (𝒻 ⋆∙ U ∨[ 𝒪 X ] 𝒻 ⋆∙ β n) ∧[ 𝒪 X ] ((𝒻 ⋆∙ (β n)) ==> 𝟎[ 𝒪 X ])      ＝⟨ 𝟐 ⟩ₚ
       (𝒻 ⋆∙ U ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ∨[ 𝒪 X ] (𝒻 ⋆∙ (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ≤⟨  𝟑 ⟩
       (𝒻 ⋆∙ U) ∨[ 𝒪 X ] (𝒻 ⋆∙ (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))                    ≤⟨ 𝟒  ⟩
       (𝒻 ⋆∙ U) ∨[ 𝒪 X ] 𝟎[ 𝒪 X ]                                           ＝⟨ 𝟓 ⟩ₚ
       𝒻 ⋆∙ U                                                               ■
        where
         𝟏 = ap
              (λ - → - ∧[ 𝒪 X ] ¬𝒻⋆ (β n))
              (frame-homomorphisms-preserve-binary-joins (𝒪 A) (𝒪 X) 𝒻 U (β n))
         𝟐 = binary-distributivity-right (𝒪 X)
         𝟑 = ∨[ 𝒪 X ]-left-monotone
              (∧[ 𝒪 X ]-lower₁
                (𝒻 ⋆∙ U)
                ((𝒻 ⋆∙ β n) ==> 𝟎[ 𝒪 X ]))
         𝟒 = ∨[ 𝒪 X ]-right-monotone (mp-left (𝒻 ⋆∙ β n) 𝟎[ 𝒪 X ])
         𝟓 =  𝟎-left-unit-of-∨ (𝒪 X) (𝒻 ⋆∙ U)

      ※ = ⋁[ 𝒪 X ]-least
           ⁅ 𝒻 ⋆∙ (U ∨[ 𝒪 A ] β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆
           (𝒻 ⋆∙ U , ϟ)

  𝒻⁻-is-unique : is-central
                  (Σ 𝒻⁻₀ ꞉ (X ─c→ Patch-A) ,
                   ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻₀ .pr₁ ‘ x ’))
                  ((f⁻⁺ , 𝒻⁻-α , 𝒻⁻-β , 𝒻⁻-γ) , 𝒻⁻-makes-the-diagram-commute)
  𝒻⁻-is-unique (𝒻⁻₀ , p) = to-subtype-＝ ※ (to-subtype-＝ γ (dfunext fe †))
   where
    f⁻₀ = pr₁ 𝒻⁻₀

    ※ : (𝒻⁻₀ : X ─c→ Patch-A)
      → is-prop ((U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U  ＝ 𝒻⁻₀ .pr₁ ‘ U ’)
    ※ 𝒻⁻₀ = Π-is-prop fe λ _ → carrier-of-[ poset-of (𝒪 X) ]-is-set

    γ : (ℊ⁻ : ⟨ 𝒪 Patch-A ⟩ → ⟨ 𝒪 X ⟩)
       → is-prop (is-a-frame-homomorphism (𝒪 Patch-A) (𝒪 X) ℊ⁻ holds)
    γ ℊ⁻ = holds-is-prop (is-a-frame-homomorphism (𝒪 Patch-A) (𝒪 X) ℊ⁻)

    open LemmasAboutHeytingComplementation X X-has-basis

    ψ : (n : Bₐ) → ¬𝒻⋆ (β n) ＝ f⁻₀ ¬‘ βₖ n ’
    ψ n = complements-are-unique (𝒪 X) (𝒻 ⋆∙ (β n)) (¬𝒻⋆ (β n)) (f⁻₀ ¬‘ βₖ n ’) ψ₁ ψ₂
     where
      ν : is-clopen (𝒪 X) (𝒻 ⋆∙ β n) holds
      ν = compacts-are-clopen-in-zero-dimensional-locales
           (𝒪 X)
           ∣ 𝕫ᴰ ∣
           (𝒻 ⋆∙ (β n))
           (μ (β n) (pr₂ (βₖ n)))

      C = pr₁ ν

      C-complements-𝒻⋆βn : is-complement-of (𝒪 X) C (𝒻 ⋆∙ (β n))
      C-complements-𝒻⋆βn = pr₂ ν

      ψ₁ : is-complement-of (𝒪 X) (¬𝒻⋆ (β n)) (𝒻 ⋆∙ β n)
      ψ₁ = transport
            (λ - → is-complement-of (𝒪 X) - (𝒻 ⋆∙ β n))
            (complement-is-heyting-complement (𝒻 ⋆∙ β n) C C-complements-𝒻⋆βn)
            C-complements-𝒻⋆βn

      ϟ : is-complement-of (𝒪 X) (f⁻₀ ¬‘ βₖ n ’) (𝒻⁻₀ .pr₁ ‘ β n ’)
      ϟ = {!frame-homomorphisms-preserve-complements (𝒪 Patchₛ-A) (𝒪 X) 𝒻⁻₀ ? !}

      ψ₂ : is-complement-of (𝒪 X) (f⁻₀ ¬‘ βₖ n ’) (𝒻 ⋆∙ β n)
      ψ₂ = transport
            (λ - → is-complement-of (𝒪 X) (f⁻₀ ¬‘ βₖ n ’) -)
            (p (β n) ⁻¹)
            ϟ

    † : (𝒿 : ⟨ 𝒪 Patchₛ-A ⟩) → f⁻⁺ 𝒿 ＝ 𝒻⁻₀ .pr₁ 𝒿
    † 𝒿 = {!!}

  proof-of-ump : ∃! 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U  ＝ 𝒻⁻ .pr₁ ‘ U ’)
  proof-of-ump =
   ((f⁻⁺ , 𝒻⁻-α , 𝒻⁻-β , 𝒻⁻-γ) , 𝒻⁻-makes-the-diagram-commute) , 𝒻⁻-is-unique

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
   γ σᴰ 𝕫ᴰ = UniversalPropertyOfPatch.proof-of-ump X σᴰ 𝕫ᴰ (pr₁ 𝕤) 𝒻 μ

--}

\end{code}

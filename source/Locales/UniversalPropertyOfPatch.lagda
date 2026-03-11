Ayberk Tosun.

Originally started 7th of December 2022.
Rewritten from scratch on 26th of April 2023.
Completed on the 2nd of June 2023.

\begin{code}[hide]

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.List hiding ([_])
open import MLTT.Spartan hiding (𝟚)
open import Slice.Family
open import UF.Base
open import UF.Embeddings
open import UF.Equiv renaming (_■ to _𝔔𝔈𝔇)
open import UF.FunExt
open import UF.PropTrunc
open import UF.PropTrunc
open import UF.Retracts
open import UF.EquivalenceExamples
open import UF.Size

module Locales.UniversalPropertyOfPatch
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt)
       where

open import Locales.AdjointFunctorTheoremForFrames pt fe
open import Locales.Clopen                     pt fe sr
open import Locales.Compactness.Definition                pt fe
open import Locales.Complements                pt fe
open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame                      pt fe
open import Locales.PosetalAdjunction           pt fe
open import Locales.HeytingComplementation     pt fe sr
open import Locales.HeytingImplication         pt fe
open import Locales.Sublocale.Nucleus           pt fe
open import Locales.PatchLocale                pt fe sr
open import Locales.PatchProperties            pt fe sr
open import Locales.PerfectMaps                pt fe
open import Locales.ScottContinuity            pt fe sr
open import Locales.SmallBasis                 pt fe sr
open import Locales.Spectrality.Properties     pt fe
open import Locales.Spectrality.SpectralLocale pt fe
open import Locales.Spectrality.SpectralMap    pt fe
open import Locales.Stone                      pt fe sr
open import Locales.StoneImpliesSpectral       pt fe sr
open import Locales.ZeroDimensionality         pt fe sr
open import UF.ImageAndSurjection
open import UF.Logic
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open ContinuousMaps
open FrameHomomorphismProperties
open FrameHomomorphisms hiding (fun; fun-syntax)
open PropositionalTruncation pt
open AllCombinators pt fe

\end{code}

\begin{code}

open Locale

\end{code}

\section{Proof of the Universal Property}

In this module, we prove the following universal property:

    given any continuous `f : X → A` from a Stone locale `X` into
    a spectral locale `A`, there exists a unique map `f⁻` satisfying
    `f⁺(U) = f⁻⁺(‘ U ’)` for any open `U : 𝒪(A)`.

This proof is given at the very end of the module and is called `ump-of-patch`.
In the following submodule `UniversalProperty` we assume the structures involved
in spectrality and zero-dimensionality and use this to prove the universal
property for the small version of Patch (which we often denote `Patchₛ`).

\begin{code}

module UniversalProperty (A : Locale (𝓤 ⁺) 𝓤 𝓤)
                         (X  : Locale (𝓤 ⁺) 𝓤 𝓤)
                         (σᴰ : spectralᴰ A)
                         (𝕫ᴰ : zero-dimensionalᴰ (𝒪 X))
                         (𝕜  : is-compact X holds)
                         (𝒻 : X ─c→ A)
                         (μ : is-spectral-map A X 𝒻 holds) where

\end{code}

As prevoiusly mentioned, we assume

  * `A` and `X`: large and locally small locales,
  * `σᴰ`: the spectrality data of `A`,
  * `𝕫ᴰ`: the zero-dimensioality structure of `X`
  * `𝕜`: compactness of `X`
  * `𝒻`: an arbitrary spectral continuous map from `X` into a `A` (which amounts
    to a spectral frame homomorphisms from frame `𝒪(A)` into frame `𝒪(X)`.
  * `μ`: proof that `𝒻` is a spectral map.

\begin{code}

 σ : is-spectral A holds
 σ = spectralᴰ-gives-spectrality A σᴰ

 sk : 𝒦 A is 𝓤 small
 sk = spectralᴰ-implies-small-𝒦 A σᴰ

 open PatchConstruction A σ  using (nucleus-of; _≼_; _$_; perfect-nuclei-eq;
                                    idₙ; 𝔡𝔦𝔯)
 open ClosedNucleus     A σ
 open OpenNucleus       A σᴰ sk

 open SmallPatchConstruction A σᴰ
  using (𝟎-is-id; ≼-implies-≼ᵏ; ≼ᵏ-implies-≼; _≼ᵏ_)
  renaming (SmallPatch to Patchₛ-A)
 open ContinuousMapNotation X A hiding (_⋆)

\end{code}

\begin{code}

 X-has-basis : has-basis (𝒪 X) holds
 X-has-basis = ∣ zero-dimensionalᴰ-implies-has-basis (𝒪 X) 𝕫ᴰ ∣

\end{code}

We denote by `Bₐ` the index set of the basis of `A` and by `β` the enumeration
function of the basis.

\begin{code}

 Bₐ : 𝓤 ̇
 Bₐ = pr₁ (pr₁ σᴰ)

 βₐ : Bₐ → ⟨ 𝒪 A ⟩
 βₐ = pr₂ (pr₁ σᴰ)

\end{code}

Similarly by `Bₓ`, we denote the index set of the basis of `X` and by `βₓ`
the enumeration function.

\begin{code}

 Bₓ : 𝓤 ̇
 Bₓ = pr₁ (pr₁ 𝕫ᴰ)

 βₓ : Bₓ → ⟨ 𝒪 X ⟩
 βₓ = pr₂ (pr₁ 𝕫ᴰ)

\end{code}

\begin{code}

 β-is-directed-basis : is-directed-basis (𝒪 A) (Bₐ , βₐ)
 β-is-directed-basis = basisₛ-is-basis A σᴰ , basisₛ-covers-are-directed A σᴰ

 A-directed-basisᴰ : directed-basisᴰ (𝒪 A)
 A-directed-basisᴰ = basisₛ A σᴰ , †
  where
   † : directed-basis-forᴰ (𝒪 A) (Bₐ , βₐ)
   † U = pr₁ Σ-assoc (basisₛ-is-basis A σᴰ U , basisₛ-covers-are-directed A σᴰ U)

 β-is-basis-for-A : is-basis-for (𝒪 A) (Bₐ , βₐ)
 β-is-basis-for-A = pr₁ β-is-directed-basis


 A-has-basis : has-basis (𝒪 A) holds
 A-has-basis = ∣ (Bₐ , βₐ) , β-is-basis-for-A ∣

 infixl 4 _∧ₓ_

 _∧ₓ_ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 U ∧ₓ V = U ∧[ 𝒪 X ] V

 infix 5 _≤ₓ_

 _≤ₓ_ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → Ω 𝓤
 _≤ₓ_ = λ U V → U ≤[ poset-of (𝒪 X) ] V

\end{code}

\begin{code}

 open HeytingImplicationConstruction X X-has-basis
 open HeytingImplicationConstruction A A-has-basis
  using ()
  renaming (_==>_ to _==>ₐ_; H₈ to H₈ₐ;
            heyting-implication-identity to heyting-implication-identityₐ;
            heyting-implication₁ to heyting-implication₁ₐ;
            ==>-right-monotone to ==>ₐ-right-monotone;
            ex-falso-quodlibet to ex-falso-quodlibetₐ)

\end{code}

It is often convenient to have a version of `βₐ` that also gives the proof
of compactness of the basic open it returns.

\begin{code}

 κₐ : (i : Bₐ) → is-compact-open A (βₐ i) holds
 κₐ = basisₛ-consists-of-compact-opens A σᴰ

 βₖ : Bₐ → 𝒦 A
 βₖ i = βₐ i , κₐ i

\end{code}

The following is shorthand notation for the negation of `𝒻 ⋆∙ U` which we know
to be the complement of `𝒻 ⋆∙ U`.

\begin{code}

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

\end{code}

The following is a ternary relation expressing, for a basic open
`‘β(m)’ ∧ ¬‘β(n)’` to be below some perfect nucleus.

TODO: improve the naming.

\begin{code}

 𝔏 : ⟨ 𝒪 Patchₛ-A ⟩ → Bₐ → Bₐ → Ω 𝓤
 𝔏 𝒿 m n = (‘ βₐ m ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) ≼ᵏ 𝒿

 below : ⟨ 𝒪 Patchₛ-A ⟩ → 𝓤 ̇
 below 𝒿 = Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝔏 𝒿 m n holds

\end{code}

This is the unique function that we define that makes our diagram commute.

\begin{code}

 f⁻⁺ : ⟨ 𝒪 Patchₛ-A ⟩ → ⟨ 𝒪 X ⟩
 f⁻⁺ 𝒿 = ⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ βₐ m) ∧ₓ ¬𝒻⋆ (βₐ n) ∣ (m , n , p) ∶ below 𝒿 ⁆

\end{code}

There is an equivalent way to define `f⁻⁺`, given in `f⁻⁺₂` below. The
equivalence of the two is quite important and is used in the proofs below.

\begin{code}

 f⁻⁺₂ : ⟨ 𝒪 Patchₛ-A ⟩ → ⟨ 𝒪 X ⟩
 f⁻⁺₂ 𝒿@(j , _) = ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ j (βₐ n) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ n ∶ Bₐ ⁆

 f⁻⁺₂-equiv-f⁻⁺₁ : (𝒿 : ⟨ 𝒪 Patchₛ-A ⟩) → f⁻⁺ 𝒿 ＝ f⁻⁺₂ 𝒿
 f⁻⁺₂-equiv-f⁻⁺₁ 𝒿@(j , _) = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
  where
   S : Fam 𝓤 ⟨ 𝒪 X ⟩
   S = ⁅ (𝒻 ⋆∙ βₐ m) ∧ₓ ¬𝒻⋆ (βₐ n) ∣ (m , n , p) ∶ below 𝒿 ⁆

   T : Fam 𝓤 ⟨ 𝒪 X ⟩
   T = ⁅ 𝒻 ⋆∙ j (βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n) ∣ n ∶ Bₐ ⁆

   †₀ : cofinal-in (𝒪 X) S T holds
   †₀ (m , n , p) = ∣ n , ※ ∣
    where
     open PosetReasoning (poset-of (𝒪 A))

     Ⅰ = ∨[ 𝒪 A ]-upper₁ (βₐ m) (βₐ n)
     Ⅱ = 𝟏-right-unit-of-∧ (𝒪 A) (βₐ m ∨[ 𝒪 A ] βₐ n) ⁻¹
     Ⅲ = ap
          (λ - → (βₐ m ∨[ 𝒪 A ] βₐ n) ∧[ 𝒪 A ] -)
          (heyting-implication-identityₐ (βₐ n) ⁻¹)

     q : (βₐ m ≤[ poset-of (𝒪 A) ] j (βₐ n)) holds
     q = βₐ m                                                ≤⟨ Ⅰ     ⟩
         βₐ m ∨[ 𝒪 A ] βₐ n                                   ＝⟨ Ⅱ    ⟩ₚ
         (βₐ m ∨[ 𝒪 A ] βₐ n) ∧[ 𝒪 A ] 𝟏[ 𝒪 A ]               ＝⟨ Ⅲ    ⟩ₚ
         (βₐ m ∨[ 𝒪 A ] βₐ n) ∧[ 𝒪 A ] (βₐ n ==>ₐ βₐ n)         ＝⟨ refl ⟩ₚ
         (βₐ m ∨[ 𝒪 A ] βₐ n) ∧[ 𝒪 A ] (¬‘ βₖ n ’ .pr₁ (βₐ n)) ＝⟨ refl ⟩ₚ
         (‘ βₐ m ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) .pr₁ (βₐ n)     ≤⟨ p n   ⟩
         j (βₐ n)                                            ■

     ※ : ((𝒻 ⋆∙ βₐ m ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n))
           ≤[ poset-of (𝒪 X) ]
          (𝒻 ⋆∙ j (βₐ n) ∧[ 𝒪 X ] (¬𝒻⋆ (βₐ n)))) holds
     ※ = ∧[ 𝒪 X ]-left-monotone
          (frame-morphisms-are-monotonic
            (𝒪 A)
            (𝒪 X)
            (𝒻 ⋆∙_)
            (𝒻 .pr₂)
            (βₐ m , j (βₐ n)) q)


   † : ((⋁[ 𝒪 X ] S) ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] T)) holds
   † = cofinal-implies-join-covered (𝒪 X) S T †₀

   ‡ : ((⋁[ 𝒪 X ] T) ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] S)) holds
   ‡ = ⋁[ 𝒪 X ]-least T ((⋁[ 𝒪 X ] S) , ‡₁)
    where
     open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)

     ‡₁ : ((⋁[ 𝒪 X ] S) is-an-upper-bound-of T) holds
     ‡₁ n =
      let
       open PosetReasoning (poset-of (𝒪 X))
      in
       𝒻 ⋆∙ j (βₐ n) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)                       ＝⟨ Ⅰ  ⟩ₚ
       𝒻 ⋆∙ (⋁[ 𝒪 A ] ⁅ βₐ i ∣ i ε 𝒥 ⁆) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)    ＝⟨ Ⅱ  ⟩ₚ
       (⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (βₐ i) ∣ i ε 𝒥 ⁆) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)  ＝⟨ Ⅲ  ⟩ₚ
       ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (βₐ i) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ i ε 𝒥 ⁆    ≤⟨ Ⅳ   ⟩
       ⋁[ 𝒪 X ] S                                            ■
      where
       𝒥 : Fam 𝓤 Bₐ
       𝒥 = cover-indexₛ A σᴰ (j (βₐ n))

       ♠ : ((⋁[ 𝒪 X ] S)
             is-an-upper-bound-of
            ⁅ 𝒻 ⋆∙ (βₐ i) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ i ε 𝒥 ⁆) holds
       ♠ i = ⋁[ 𝒪 X ]-upper S (𝒥 [ i ] , n , ♢)
        where
         open PosetReasoning (poset-of (𝒪 A))
         open NucleusHeytingImplicationLaw A A-has-basis (nucleus-of 𝒿)

         ♢ : 𝔏 𝒿 (𝒥 [ i ]) n holds
         ♢ m =
          (‘ βₐ (𝒥 [ i ]) ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) .pr₁ (βₐ m)      ＝⟨ refl ⟩ₚ
          ((βₐ (𝒥 [ i ]) ∨[ 𝒪 A ] βₐ m) ∧[ 𝒪 A ] (βₐ n ==>ₐ βₐ m))        ≤⟨ Ⅰ     ⟩
          (j (βₐ n) ∨[ 𝒪 A ] βₐ m) ∧[ 𝒪 A ] (βₐ n ==>ₐ βₐ m)              ≤⟨ Ⅱ     ⟩
          (j (βₐ n) ∨[ 𝒪 A ] βₐ m) ∧[ 𝒪 A ] (βₐ n ==>ₐ j (βₐ m))          ＝⟨ Ⅲ    ⟩ₚ
          (j (βₐ n) ∨[ 𝒪 A ] βₐ m) ∧[ 𝒪 A ] (j (βₐ n) ==>ₐ j (βₐ m))      ≤⟨ Ⅳ     ⟩
          (j (βₐ n) ∨[ 𝒪 A ] j (βₐ m)) ∧[ 𝒪 A ] (j (βₐ n) ==>ₐ j (βₐ m))  ＝⟨ Ⅴ    ⟩ₚ
          (j (βₐ m) ∨[ 𝒪 A ] j (βₐ n)) ∧[ 𝒪 A ] (j (βₐ n) ==>ₐ j (βₐ m))  ＝⟨ Ⅵ    ⟩ₚ
          j (βₐ m)                                                     ■
           where
            ♣ = βₐ (𝒥 [ i ]) ≤⟨ 𝕒 ⟩ ⋁[ 𝒪 A ] ⁅ βₐ i ∣ i ε 𝒥 ⁆  ＝⟨ 𝕓 ⟩ₚ j (βₐ n) ■
                 where
                  𝕒 = ⋁[ 𝒪 A ]-upper ⁅ βₐ i ∣ i ε 𝒥 ⁆ i
                  𝕓 = covers (𝒪 A) (Bₐ , βₐ) β-is-basis-for-A (j (βₐ n)) ⁻¹

            Ⅰ = ∧[ 𝒪 A ]-left-monotone (∨[ 𝒪 A ]-left-monotone ♣)
            Ⅱ = ∧[ 𝒪 A ]-right-monotone
                 (==>ₐ-right-monotone (𝓃₁ (𝒪 A) (nucleus-of 𝒿) (βₐ m)))
            Ⅲ = ap
                 (λ - → (j (βₐ n) ∨[ 𝒪 A ] βₐ m) ∧[ 𝒪 A ] -)
                 (nucleus-heyting-implication-law (βₐ n) (βₐ m))
            Ⅳ = ∧[ 𝒪 A ]-left-monotone
                 (∨[ 𝒪 A ]-right-monotone (𝓃₁ (𝒪 A) (nucleus-of 𝒿) (βₐ m)))
            Ⅴ = ap
                 (λ - → - ∧[ 𝒪 A ] (j (βₐ n) ==>ₐ j (βₐ m)))
                 (∨[ 𝒪 A ]-is-commutative (j (βₐ n)) (j (βₐ m)))
            Ⅵ = H₈ₐ (j (βₐ m)) (j (βₐ n)) ⁻¹

       Ⅰ = ap
            (λ - → 𝒻 ⋆∙ - ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n))
            (covers (𝒪 A) (Bₐ , βₐ) β-is-basis-for-A (j (βₐ n)))
       Ⅱ = ap
            (λ - → - ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n))
            (frame-homomorphisms-preserve-all-joins′ (𝒪 A) (𝒪 X) 𝒻 ⁅ βₐ i ∣ i ε 𝒥 ⁆)
       Ⅲ = distributivity′-right (𝒪 X) (¬𝒻⋆ (βₐ n)) ⁅ 𝒻 ⋆∙ (βₐ i) ∣ i ε 𝒥 ⁆
       Ⅳ = ⋁[ 𝒪 X ]-least ⁅ 𝒻 ⋆∙ (βₐ i) ∧ₓ ¬𝒻⋆ (βₐ n) ∣ i ε 𝒥 ⁆ ((⋁[ 𝒪 X ] S) , ♠)

\end{code}

The function `f⁻⁺` is monotone. This of course follows from both meet and join
preservation but I have proved it separately for reasons that I don't remember.

TODO: investigate if there was a good reason why this had to be done in a
separate proof

\begin{code}

 f⁻⁺-is-monotone : is-monotonic (poset-of (𝒪 Patchₛ-A)) (poset-of (𝒪 X)) f⁻⁺
                    holds
 f⁻⁺-is-monotone (𝒿 , 𝓀) p = cofinal-implies-join-covered (𝒪 X) 𝒮 𝒯 †
  where
   𝒮 : Fam 𝓤 ⟨ 𝒪 X ⟩
   𝒮 = ⁅ (𝒻 ⋆∙ βₐ m) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)
         ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝔏 𝒿 m n holds ⁆

   𝒯 : Fam 𝓤 ⟨ 𝒪 X ⟩
   𝒯 = ⁅ (𝒻 ⋆∙ βₐ m) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)
         ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝔏 𝓀 m n holds ⁆

   † : cofinal-in (𝒪 X) 𝒮 𝒯 holds
   † (m , n , q) = ∣ (m , n , ‡) , ♣ ∣
    where
     open PosetReasoning (poset-of (𝒪 A))

     ‡ : 𝔏 𝓀 m n holds
     ‡ l = (‘ βₐ m ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) .pr₁ (βₐ l)   ≤⟨ q l ⟩
           𝒿 $ (βₐ l)                                        ≤⟨ p l ⟩
           𝓀 $ (βₐ l)                                        ■

     ♣ : (_ ≤[ poset-of (𝒪 X) ] _) holds
     ♣ = ≤-is-reflexive (poset-of (𝒪 X)) ((𝒻 ⋆∙ βₐ m) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n))

 f⁻⁺ₘ : poset-of (𝒪 Patchₛ-A) ─m→ poset-of (𝒪 X)
 f⁻⁺ₘ = f⁻⁺ , f⁻⁺-is-monotone

\end{code}

\begin{code}

 open PatchStoneᴰ A σᴰ

 Patchₛ-A-basisᴰ : basisᴰ (𝒪 Patchₛ-A)
 Patchₛ-A-basisᴰ =
  spectralᴰ-implies-basisᴰ Patchₛ-A patchₛ-spectralᴰ

 -- Patchₛ-A-has-basis : has-basis (𝒪 Patchₛ-A) holds
 -- Patchₛ-A-has-basis = ?

\end{code}

Some horrible import bureaucracy below 😬

\begin{code}

 open AdjointFunctorTheorem X Patchₛ-A ∣ Patchₛ-A-basisᴰ ∣
  hiding (f₊-is-right-adjoint-of-f⁺)
 open AdjointFunctorTheorem Patchₛ-A X X-has-basis
  using ()
  renaming (adjunction-inequality-forward to adjunction-inequality-forward₀)
 open AdjointFunctorTheorem X A A-has-basis
  using    (f₊-is-right-adjoint-of-f⁺)
  renaming (right-adjoint-of to right-adjoint-ofₓ;
            f₊-preserves-binary-meets to f₊-preserves-binary-meetsₓ;
            adjunction-inequality-forward to adjunction-inequality-forwardₓ;
            adjunction-inequality-backward to adjunction-inequality-backwardₓ)
 open PosetalAdjunctionBetween (poset-of (𝒪 Patchₛ-A)) (poset-of (𝒪 X))
 open PosetalAdjunctionBetween (poset-of (𝒪 X)) (poset-of (𝒪 A))
  using () renaming (counit to counitₓ)
 open PosetalAdjunctionBetween (poset-of (𝒪 A)) (poset-of (𝒪 X))
  using () renaming (counit to counitₐ)

\end{code}

We now define some notation that will keep coming up.

We denote by `𝒻₊` the right adjoint of `𝒻⁺`, which is monotonic map denote by
`𝒻₊ₘ`.

\begin{code}

 𝒻₊ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 A ⟩
 𝒻₊ = pr₁ (right-adjoint-ofₓ 𝒻)

 𝒻₊ₘ : poset-of (𝒪 X) ─m→ poset-of (𝒪 A)
 𝒻₊ₘ = right-adjoint-ofₓ 𝒻

\end{code}

\begin{code}

 𝒻⁺ₘ : poset-of (𝒪 A) ─m→ poset-of (𝒪 X)
 𝒻⁺ₘ = pr₁ 𝒻 , frame-morphisms-are-monotonic (𝒪 A) (𝒪 X) (𝒻 ⋆∙_) (pr₂ 𝒻)

\end{code}

We prove that `f⁻⁺` preserves the top element of `𝒪(Patchₛ-A)`.

\begin{code}

 𝒻⁻-α : f⁻⁺ 𝟏[ 𝒪 Patchₛ-A ] ＝ 𝟏[ 𝒪 X ]
 𝒻⁻-α = only-𝟏-is-above-𝟏 (𝒪 X) (f⁻⁺ 𝟏[ 𝒪 Patchₛ-A ]) †
  where
   open PosetReasoning (poset-of (𝒪 X))

   † : (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] f⁻⁺ 𝟏[ 𝒪 Patchₛ-A ]) holds
   † =
    ∥∥-rec
     (holds-is-prop (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] f⁻⁺ 𝟏[ 𝒪 Patchₛ-A ]))
     ‡
     (compact-opens-are-basic A A-directed-basisᴰ 𝟎[ 𝒪 A ] (𝟎-is-compact A))
      where
       ‡ : Σ i ꞉ Bₐ , βₐ i ＝ 𝟎[ 𝒪 A ]
         → (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] f⁻⁺ 𝟏[ 𝒪 Patchₛ-A ]) holds
       ‡ (i , p′) =
        𝟏[ 𝒪 X ]                                                ＝⟨ Ⅰ    ⟩ₚ
        𝟏[ 𝒪 X ] ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                              ＝⟨ Ⅱ    ⟩ₚ
        𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                         ＝⟨ Ⅲ    ⟩ₚ
        𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ i)                        ≤⟨  Ⅳ    ⟩
        ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ n ∶ Bₐ ⁆  ＝⟨ refl ⟩ₚ
        f⁻⁺₂ 𝟏[ 𝒪 Patchₛ-A ]                                    ＝⟨ Ⅴ    ⟩ₚ
        f⁻⁺  𝟏[ 𝒪 Patchₛ-A ]                                    ■
         where
          p   = p′ ⁻¹
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
                 (𝒻 ⋆∙ βₐ i) ==> 𝟎[ 𝒪 X ]    ＝⟨refl⟩
                 ¬𝒻⋆ (βₐ i)                    ∎)
          Ⅳ   = ⋁[ 𝒪 X ]-upper ⁅ 𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ n ∶ Bₐ ⁆ i
          Ⅱ   = ap
                 (λ - → - ∧[ 𝒪 X ] 𝟏[ 𝒪 X ])
                 (frame-homomorphisms-preserve-top (𝒪 A) (𝒪 X) 𝒻 ⁻¹)
          Ⅴ   = f⁻⁺₂-equiv-f⁻⁺₁ 𝟏[ 𝒪 Patchₛ-A ] ⁻¹

\end{code}

The function `f⁻⁺` preserves binary meets.


\begin{code}

 𝒻⁻-β : preserves-binary-meets (𝒪 Patchₛ-A) (𝒪 X) f⁻⁺ holds
 𝒻⁻-β 𝒿@(j , _) 𝓀@(k , _) =

  f⁻⁺ (𝒿 ∧[ 𝒪 Patchₛ-A ] 𝓀)

   ＝⟨ Ⅰ ⟩

  f⁻⁺₂ (𝒿 ∧[ 𝒪 Patchₛ-A ] 𝓀)

   ＝⟨refl⟩

  ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (j (βₐ n) ∧[ 𝒪 A ] k (βₐ n)) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ n ∶ Bₐ ⁆

   ＝⟨ Ⅱ    ⟩

  ⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ j (βₐ n) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (βₐ n)) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ n ∶ Bₐ ⁆

   ＝⟨ Ⅲ ⟩

  ⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ j (βₐ n)  ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n))
             ∧[ 𝒪 X ]
             (𝒻 ⋆∙ k (βₐ n) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)) ∣ n ∶ Bₐ ⁆
   ＝⟨ Ⅳ ⟩

  ⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ j (βₐ m)  ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ m))
             ∧[ 𝒪 X ]
             (𝒻 ⋆∙ k (βₐ n) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)) ∣ (m , n) ∶ Bₐ × Bₐ ⁆

   ＝⟨ Ⅴ ⟩

  (⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ j (βₐ n)) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ n ∶ Bₐ ⁆)
   ∧[ 𝒪 X ]
  (⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ k (βₐ n)) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ n ∶ Bₐ ⁆)

   ＝⟨refl⟩

  f⁻⁺₂ 𝒿 ∧[ 𝒪 X ] f⁻⁺₂ 𝓀

   ＝⟨ Ⅵ ⟩

  f⁻⁺ 𝒿 ∧[ 𝒪 X ] f⁻⁺ 𝓀

   ∎
   where
    Ⅰ = f⁻⁺₂-equiv-f⁻⁺₁ (𝒿 ∧[ 𝒪 Patchₛ-A ] 𝓀)
    Ⅱ = ap
         (λ - → ⋁[ 𝒪 X ] (Bₐ , -))
         (dfunext fe λ n →
           ap
            (λ - → - ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n))
            (frame-homomorphisms-preserve-meets (𝒪 A) (𝒪 X) 𝒻 (j (βₐ n)) (k (βₐ n))))
    Ⅲ = ap
         (λ - → ⋁[ 𝒪 X ] (Bₐ , -))
         (dfunext fe λ n →
           let
            𝕒 = ap
                 (λ - → (𝒻 ⋆∙ j (βₐ n) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (βₐ n)) ∧[ 𝒪 X ] -)
                 (∧[ 𝒪 X ]-is-idempotent (¬𝒻⋆ (βₐ n)))
            𝕓 = ∧[ 𝒪 X ]-is-associative
                 (𝒻 ⋆∙ j (βₐ n))
                 (𝒻 ⋆∙ k (βₐ n))
                 (¬𝒻⋆ (βₐ n) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)) ⁻¹
            𝕔 = ap
                 (λ - → 𝒻 ⋆∙ j (βₐ n) ∧[ 𝒪 X ] -)
                 (∧[ 𝒪 X ]-is-associative (𝒻 ⋆∙ k (βₐ n)) (¬𝒻⋆ (βₐ n)) (¬𝒻⋆ (βₐ n)))
            𝕕 = ap
                 (λ - → 𝒻 ⋆∙ j (βₐ n) ∧[ 𝒪 X ] (- ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)))
                 (∧[ 𝒪 X ]-is-commutative (𝒻 ⋆∙ k (βₐ n)) (¬𝒻⋆ (βₐ n)))
            𝕖 = ap
                 (λ - → 𝒻 ⋆∙ j (βₐ n) ∧[ 𝒪 X ] -)
                 (∧[ 𝒪 X ]-is-associative (¬𝒻⋆ (βₐ n)) (𝒻 ⋆∙ k (βₐ n)) (¬𝒻⋆ (βₐ n)) ⁻¹)
            𝕗 = ∧[ 𝒪 X ]-is-associative
                 (𝒻 ⋆∙ j (βₐ n))
                 (¬𝒻⋆ (βₐ n))
                 (𝒻 ⋆∙ k (βₐ n) ∧[ 𝒪 X ] (¬𝒻⋆ (βₐ n)))
           in
            𝒻 ⋆∙ j (βₐ n) ∧ₓ 𝒻 ⋆∙ k (βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n)
             ＝⟨ 𝕒 ⟩
            𝒻 ⋆∙ j (βₐ n) ∧ₓ 𝒻 ⋆∙ k (βₐ n) ∧ₓ (¬𝒻⋆ (βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n))
             ＝⟨ 𝕓 ⟩
            𝒻 ⋆∙ j (βₐ n) ∧ₓ (𝒻 ⋆∙ k (βₐ n) ∧ₓ (¬𝒻⋆ (βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n)))
             ＝⟨ 𝕔 ⟩
            𝒻 ⋆∙ j (βₐ n) ∧ₓ (((𝒻 ⋆∙ k (βₐ n)) ∧ₓ ¬𝒻⋆ (βₐ n)) ∧ₓ ¬𝒻⋆ (βₐ n))
             ＝⟨ 𝕕 ⟩
            𝒻 ⋆∙ j (βₐ n) ∧ₓ ((¬𝒻⋆ (βₐ n) ∧ₓ 𝒻 ⋆∙ (k (βₐ n))) ∧ₓ ¬𝒻⋆ (βₐ n))
             ＝⟨ 𝕖 ⟩
            𝒻 ⋆∙ j (βₐ n) ∧ₓ (¬𝒻⋆ (βₐ n) ∧ₓ ((𝒻 ⋆∙ k (βₐ n)) ∧ₓ ¬𝒻⋆ (βₐ n)))
             ＝⟨ 𝕗 ⟩
            (𝒻 ⋆∙ j (βₐ n)  ∧ₓ ¬𝒻⋆ (βₐ n)) ∧ₓ (𝒻 ⋆∙ k (βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n))
             ∎)

    lhs₁ = ⁅ (𝒻 ⋆∙ j (βₐ n)  ∧ₓ ¬𝒻⋆ (βₐ n)) ∧ₓ (𝒻 ⋆∙ k (βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n)) ∣ n ∶ Bₐ ⁆
    rhs₁ = ⁅ (𝒻 ⋆∙ j (βₐ m)  ∧ₓ ¬𝒻⋆ (βₐ m)) ∧ₓ (𝒻 ⋆∙ k (βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n))
            ∣ (m , n) ∶ Bₐ × Bₐ ⁆

    † : cofinal-in (𝒪 X) lhs₁ rhs₁ holds
    † n = ∣ (n , n) , ≤-is-reflexive (poset-of (𝒪 X)) (lhs₁ [ n ]) ∣

    ‡ : cofinal-in (𝒪 X) rhs₁ lhs₁ holds
    ‡ (m , n) = ∥∥-rec ∃-is-prop ϡ ※
     where
      ϡ : (Σ o ꞉ Bₐ , βₐ o ＝ βₐ m ∨[ 𝒪 A ] βₐ n)
        → ∃ o ꞉ Bₐ , (rhs₁ [ (m , n) ] ≤[ poset-of (𝒪 X) ] lhs₁ [ o ]) holds
      ϡ (o , p) = ∣ o , ϟ ∣
       where
        𝕒₁ = ∧[ 𝒪 X ]-is-associative
              (𝒻 ⋆∙ j (βₐ m))
              (¬𝒻⋆ (βₐ m))
              (𝒻 ⋆∙ k (βₐ n) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)) ⁻¹
        𝕒₂ = ap
              (λ - → 𝒻 ⋆∙ j (βₐ m) ∧[ 𝒪 X ] -)
              (∧[ 𝒪 X ]-is-associative (¬𝒻⋆ (βₐ m)) (𝒻 ⋆∙ k (βₐ n)) (¬𝒻⋆ (βₐ n)))
        𝕒₃ = ap
              (λ - → 𝒻 ⋆∙ j (βₐ m) ∧[ 𝒪 X ] (- ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)))
              (∧[ 𝒪 X ]-is-commutative (¬𝒻⋆ (βₐ m)) (𝒻 ⋆∙ k (βₐ n)))
        𝕒₄ = ap
              (λ - → 𝒻 ⋆∙ j (βₐ m) ∧[ 𝒪 X ] -)
              (∧[ 𝒪 X ]-is-associative (𝒻 ⋆∙ k (βₐ n)) (¬𝒻⋆ (βₐ m)) (¬𝒻⋆ (βₐ n)) ⁻¹)
        𝕒₅ = ∧[ 𝒪 X ]-is-associative
              (𝒻 ⋆∙ j (βₐ m))
              (𝒻 ⋆∙ k (βₐ n))
              (¬𝒻⋆ (βₐ m) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n))
        𝕒₆ = ap
              (λ - → - ∧[ 𝒪 X ] (¬𝒻⋆ (βₐ m) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)))
              (frame-homomorphisms-preserve-meets (𝒪 A) (𝒪 X) 𝒻 (j (βₐ m)) (k (βₐ n)) ⁻¹)

        𝕒  = (𝒻 ⋆∙ j (βₐ m) ∧ₓ ¬𝒻⋆ (βₐ m)) ∧ₓ (𝒻 ⋆∙ k (βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n))    ＝⟨ 𝕒₁ ⟩
             𝒻 ⋆∙ j (βₐ m) ∧ₓ (¬𝒻⋆ (βₐ m) ∧ₓ (𝒻 ⋆∙ k (βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n)))    ＝⟨ 𝕒₂ ⟩
             𝒻 ⋆∙ j (βₐ m) ∧ₓ ((¬𝒻⋆ (βₐ m) ∧ₓ 𝒻 ⋆∙ k (βₐ n)) ∧ₓ ¬𝒻⋆ (βₐ n))    ＝⟨ 𝕒₃ ⟩
             𝒻 ⋆∙ j (βₐ m) ∧ₓ (𝒻 ⋆∙ (k (βₐ n)) ∧ₓ ¬𝒻⋆ (βₐ m) ∧ₓ ¬𝒻⋆ (βₐ n))    ＝⟨ 𝕒₄ ⟩
             𝒻 ⋆∙ j (βₐ m) ∧ₓ (𝒻 ⋆∙ (k (βₐ n)) ∧ₓ (¬𝒻⋆ (βₐ m) ∧ₓ ¬𝒻⋆ (βₐ n)))  ＝⟨ 𝕒₅ ⟩
             (𝒻 ⋆∙ j (βₐ m) ∧ₓ 𝒻 ⋆∙ (k (βₐ n))) ∧ₓ (¬𝒻⋆ (βₐ m) ∧ₓ ¬𝒻⋆ (βₐ n))  ＝⟨ 𝕒₆ ⟩
             (𝒻 ⋆∙ (j (βₐ m) ∧[ 𝒪 A ] k (βₐ n))) ∧ₓ (¬𝒻⋆ (βₐ m) ∧ₓ ¬𝒻⋆ (βₐ n)) ∎
        𝕓₁ = j (βₐ m) ∧[ 𝒪 A ] k (βₐ n)   ≤⟨ ∧[ 𝒪 A ]-lower₁ (j (βₐ m)) (k (βₐ n)) ⟩
             j (βₐ m)                    ≤⟨ ♠                                   ⟩
             j (βₐ m ∨[ 𝒪 A ] βₐ n)       ＝⟨ ap j p ⁻¹                          ⟩ₚ
             j (βₐ o)                    ■
              where
               open PosetReasoning (poset-of (𝒪 A))
               ♠ = nuclei-are-monotone
                    (𝒪 A)
                    (nucleus-of 𝒿)
                    (_ , _)
                    (∨[ 𝒪 A ]-upper₁ (βₐ m) (βₐ n))
        𝕓₂ = j (βₐ m) ∧[ 𝒪 A ] k (βₐ n) ≤⟨ ∧[ 𝒪 A ]-lower₂ (j (βₐ m)) (k (βₐ n)) ⟩
             k (βₐ n)                  ≤⟨ ♠                                   ⟩
             k (βₐ m ∨[ 𝒪 A ] βₐ n)     ＝⟨ ap k p ⁻¹ ⟩ₚ
             k (βₐ o)                  ■
              where
               open PosetReasoning (poset-of (𝒪 A))

               ♠ = nuclei-are-monotone
                    (𝒪 A)
                    (nucleus-of 𝓀)
                    (_ , _)
                    (∨[ 𝒪 A ]-upper₂ (βₐ m) (βₐ n))
        𝕓  = ∧[ 𝒪 X ]-left-monotone
              (frame-morphisms-are-monotonic
                (𝒪 A)
                (𝒪 X)
                (pr₁ 𝒻)
                (pr₂ 𝒻)
                ((j (βₐ m) ∧[ 𝒪 A ] k (βₐ n)) , (j (βₐ o) ∧[ 𝒪 A ] k (βₐ o)))
                (∧[ 𝒪 A ]-greatest
                  (j (βₐ o))
                  (k (βₐ o))
                  (j (βₐ m) ∧[ 𝒪 A ] k (βₐ n))
                  𝕓₁
                  𝕓₂))

        ♣ : ((¬𝒻⋆ (βₐ m) ∧ₓ ¬𝒻⋆ (βₐ n)) ≤[ poset-of (𝒪 X) ] ¬𝒻⋆ (βₐ o)) holds
        ♣ = ¬𝒻⋆ (βₐ m) ∧ₓ ¬𝒻⋆ (βₐ n)                                  ＝⟨ refl ⟩ₚ
            ((𝒻 ⋆∙ βₐ m) ==> 𝟎[ 𝒪 X ]) ∧ₓ ((𝒻 ⋆∙ βₐ n) ==> 𝟎[ 𝒪 X ])  ＝⟨ 𝟏    ⟩ₚ
            ((𝒻 ⋆∙ (βₐ m) ∨[ 𝒪 X ] (𝒻 ⋆∙ (βₐ n))) ==> 𝟎[ 𝒪 X ])       ＝⟨ 𝟐    ⟩ₚ
            ((𝒻 ⋆∙ (βₐ m ∨[ 𝒪 A ] βₐ n)) ==> 𝟎[ 𝒪 X ])                ＝⟨ 𝟑    ⟩ₚ
            ¬𝒻⋆ (βₐ o)                                               ■
         where
          open PosetReasoning (poset-of (𝒪 X))

          𝟏 = ==>-left-reverses-joins (𝒻 ⋆∙ (βₐ m)) (𝒻 ⋆∙ (βₐ n)) 𝟎[ 𝒪 X ]
          𝟐 = ap
               (λ - → - ==> 𝟎[ 𝒪 X ])
               (frame-homomorphisms-preserve-binary-joins (𝒪 A) (𝒪 X) 𝒻 (βₐ m) (βₐ n) ⁻¹)
          𝟑 = ap (λ - → (𝒻 ⋆∙ -) ==> 𝟎[ 𝒪 X ]) (p ⁻¹)

        𝕔 = ∧[ 𝒪 X ]-right-monotone ♣
        𝕕 = ap
             (λ - → - ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ o))
             (frame-homomorphisms-preserve-meets
               (𝒪 A)
               (𝒪 X)
               𝒻
               (j (βₐ o))
               (k (βₐ o)))
        𝕖 =
         (𝒻 ⋆∙ j (βₐ o) ∧ₓ 𝒻 ⋆∙ k (βₐ o)) ∧ₓ ¬𝒻⋆ (βₐ o)                ＝⟨ 𝟏 ⟩
         (𝒻 ⋆∙ j (βₐ o) ∧ₓ 𝒻 ⋆∙ k (βₐ o)) ∧ₓ (¬𝒻⋆ (βₐ o) ∧ₓ ¬𝒻⋆ (βₐ o)) ＝⟨ 𝟐 ⟩
         𝒻 ⋆∙ j (βₐ o) ∧ₓ (𝒻 ⋆∙ k (βₐ o) ∧ₓ (¬𝒻⋆ (βₐ o) ∧ₓ ¬𝒻⋆ (βₐ o))) ＝⟨ 𝟑 ⟩
         𝒻 ⋆∙ j (βₐ o) ∧ₓ ((𝒻 ⋆∙ k (βₐ o) ∧ₓ ¬𝒻⋆ (βₐ o)) ∧ₓ ¬𝒻⋆ (βₐ o)) ＝⟨ 𝟒 ⟩
         𝒻 ⋆∙ j (βₐ o) ∧ₓ ((¬𝒻⋆ (βₐ o) ∧ₓ 𝒻 ⋆∙ k (βₐ o)) ∧ₓ ¬𝒻⋆ (βₐ o)) ＝⟨ 𝟓 ⟩
         𝒻 ⋆∙ j (βₐ o) ∧ₓ (¬𝒻⋆ (βₐ o) ∧ₓ (𝒻 ⋆∙ k (βₐ o) ∧ₓ ¬𝒻⋆ (βₐ o))) ＝⟨ 𝟔 ⟩
         (𝒻 ⋆∙ j (βₐ o) ∧ₓ ¬𝒻⋆ (βₐ o)) ∧ₓ (𝒻 ⋆∙ k (βₐ o) ∧ₓ ¬𝒻⋆ (βₐ o)) ∎
          where
           𝟏 = ap
                (λ - → (𝒻 ⋆∙ j (βₐ o) ∧ₓ 𝒻 ⋆∙ k (βₐ o)) ∧ₓ -)
                (∧[ 𝒪 X ]-is-idempotent (¬𝒻⋆ (βₐ o)))
           𝟐 = ∧[ 𝒪 X ]-is-associative
                (𝒻 ⋆∙ j (βₐ o))
                (𝒻 ⋆∙ k (βₐ o))
                (¬𝒻⋆ (βₐ o) ∧ₓ ¬𝒻⋆ (βₐ o)) ⁻¹
           𝟑 = ap
                (λ - → 𝒻 ⋆∙ (j (βₐ o)) ∧ₓ -)
                (∧[ 𝒪 X ]-is-associative (𝒻 ⋆∙ k (βₐ o)) (¬𝒻⋆ (βₐ  o)) (¬𝒻⋆ (βₐ o)))
           𝟒 = ap
                (λ - → 𝒻 ⋆∙ j (βₐ o) ∧ₓ (- ∧ₓ ¬𝒻⋆ (βₐ o)))
                (∧[ 𝒪 X ]-is-commutative (𝒻 ⋆∙ k (βₐ o)) (¬𝒻⋆ (βₐ o)))
           𝟓 = ap
                (λ - → 𝒻 ⋆∙ j (βₐ o) ∧ₓ -)
                (∧[ 𝒪 X ]-is-associative (¬𝒻⋆ (βₐ o)) (𝒻 ⋆∙ k (βₐ o)) (¬𝒻⋆ (βₐ o)) ⁻¹)
           𝟔 = ∧[ 𝒪 X ]-is-associative
                (𝒻 ⋆∙ j (βₐ o))
                (¬𝒻⋆ (βₐ o))
                (𝒻 ⋆∙ k (βₐ o) ∧ₓ ¬𝒻⋆ (βₐ o))

        open PosetReasoning (poset-of (𝒪 X))

        ϟ = (𝒻 ⋆∙ j (βₐ m) ∧ₓ ¬𝒻⋆ (βₐ m)) ∧ₓ (𝒻 ⋆∙ k (βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n))    ＝⟨ 𝕒 ⟩ₚ
            (𝒻 ⋆∙ (j (βₐ m) ∧[ 𝒪 A ] k (βₐ n))) ∧ₓ (¬𝒻⋆ (βₐ m) ∧ₓ ¬𝒻⋆ (βₐ n)) ≤⟨ 𝕓  ⟩
            𝒻 ⋆∙ (j (βₐ o) ∧[ 𝒪 A ] k (βₐ o)) ∧ₓ (¬𝒻⋆ (βₐ m) ∧ₓ ¬𝒻⋆ (βₐ n))   ≤⟨ 𝕔  ⟩
            𝒻 ⋆∙ (j (βₐ o) ∧[ 𝒪 A ] k (βₐ o)) ∧ₓ ¬𝒻⋆ (βₐ o)                  ＝⟨ 𝕕 ⟩ₚ
            (𝒻 ⋆∙ j (βₐ o) ∧ₓ 𝒻 ⋆∙ k (βₐ o)) ∧ₓ ¬𝒻⋆ (βₐ o)                   ＝⟨ 𝕖 ⟩ₚ
            (𝒻 ⋆∙ j (βₐ o) ∧ₓ ¬𝒻⋆ (βₐ o)) ∧ₓ (𝒻 ⋆∙ k (βₐ o) ∧ₓ ¬𝒻⋆ (βₐ o))    ■

      ξ : is-compact-open A (βₐ m ∨[ 𝒪 A ] βₐ n) holds
      ξ = compact-opens-are-closed-under-∨ A (βₐ m) (βₐ n) (κₐ m) (κₐ n)

      ※ : ∃ o ꞉ Bₐ , βₐ o ＝ βₐ m ∨[ 𝒪 A ] βₐ n
      ※ = ∥∥-rec
           ∃-is-prop
           (λ { (o , p′) → ∣ o , p′ ∣})
           (compact-opens-are-basic A A-directed-basisᴰ (βₐ m ∨[ 𝒪 A ] βₐ n) ξ)

    Ⅳ = bicofinal-implies-same-join (𝒪 X) lhs₁ rhs₁ † ‡

    Ⅴ = distributivity+
         (𝒪 X)
         ⁅ (𝒻 ⋆∙ j (βₐ n)) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ n ∶ Bₐ ⁆
         ⁅ (𝒻 ⋆∙ k (βₐ n)) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ n ∶ Bₐ ⁆ ⁻¹
    Ⅵ = ap₂
         (λ x y → x ∧[ 𝒪 X ] y)
         (f⁻⁺₂-equiv-f⁻⁺₁ 𝒿 ⁻¹)
         (f⁻⁺₂-equiv-f⁻⁺₁ 𝓀 ⁻¹)

\end{code}

We now proceed to the join preservation proof which requires quite a few
auxiliary definitions and lemmas.

\begin{code}

 X-is-spectral : is-spectral X holds
 X-is-spectral = stone-locales-are-spectral X (𝕜 , 𝕫ᴰ)

 open ClosedNucleus X X-is-spectral
  using    ()
  renaming (‘_’ to ‘_’ₓ)

\end{code}

The following function `closed-image` takes an open `X` and gives a perfect
nucleus on `A`. It is the right adjoint to the function `f⁻⁺` that we have
defined. We define this function and prove the adjunction to show that `f⁻⁺`
preserves joins using the Adjoint Functor Theorem.
\begin{code}

 closed-image : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 A ⟩ → ⟨ 𝒪 A ⟩
 closed-image U = (𝒻₊ ∘ ‘ U ’ₓ .pr₁) ∘ 𝒻 ⋆∙_

\end{code}

The definition of this function was suggested by Igor Arrieta who also gave a
summary of the proof. Even though our proof here differs from his, the idea is
due to him.

\begin{code}

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

\end{code}

\begin{code}

 closed-image-preserves-meets : (U : ⟨ 𝒪 X ⟩)
                              → preserves-binary-meets
                                 (𝒪 A)
                                 (𝒪 A)
                                 (closed-image U)
                                holds
 closed-image-preserves-meets U V₁ V₂ =
  𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ (V₁ ∧[ 𝒪 A ] V₂))                        ＝⟨ Ⅰ    ⟩
  𝒻₊ (U ∨[ 𝒪 X ] (𝒻 ⋆∙ V₁ ∧[ 𝒪 X ] 𝒻 ⋆∙ V₂))                   ＝⟨ Ⅱ    ⟩
  𝒻₊ ((U ∨[ 𝒪 X ] 𝒻 ⋆∙ V₁) ∧[ 𝒪 X ] (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V₂))      ＝⟨ Ⅲ    ⟩
  𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V₁) ∧[ 𝒪 A ] 𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V₂)     ＝⟨refl⟩
  closed-image U V₁ ∧[ 𝒪 A ] closed-image U V₂                 ∎
   where
    Ⅰ = ap
         (λ - → 𝒻₊ (U ∨[ 𝒪 X ] -))
         (frame-homomorphisms-preserve-meets (𝒪 A) (𝒪 X) 𝒻 V₁ V₂)
    Ⅱ = ap 𝒻₊ (binary-distributivity-op (𝒪 X) U (𝒻 ⋆∙ V₁) (𝒻 ⋆∙ V₂))
    Ⅲ = f₊-preserves-binary-meetsₓ 𝒻 (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V₁) (U ∨[ 𝒪 X ] (𝒻 ⋆∙ V₂))

\end{code}

As mentioned previously, `closed-image U` is a perfect nucleus for any `U :
𝒪(X)`. We now prove this fact.

\begin{code}

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
         (spectral-maps-are-perfect σ 𝒻 μ)
         (∨-is-scott-continuous (𝒪 X) U)
         where
          open PerfectMaps X A A-has-basis


    ‡ : is-scott-continuous (𝒪 A) (𝒪 X) (𝒻 ⋆∙_) holds
    ‡ = join-preserving-implies-scott-continuous
         (𝒪 A)
         (𝒪 X)
         (𝒻 ⋆∙_)
         (frame-homomorphisms-preserve-all-joins′ (𝒪 A) (𝒪 X) 𝒻)

\end{code}

\begin{code}

 f⁻₊ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 Patchₛ-A ⟩
 f⁻₊ U = closed-image U ,  closed-image-is-nucleus U  , closed-image-is-sc U

\end{code}

\begin{code}

 f⁻₊-is-monotone : is-monotonic (poset-of (𝒪 X)) (poset-of (𝒪 Patchₛ-A)) f⁻₊
                    holds
 f⁻₊-is-monotone (U , V) p n = pr₂ 𝒻₊ₘ _ (∨[ 𝒪 X ]-left-monotone p)

 f⁻₊ₘ : poset-of (𝒪 X) ─m→ poset-of (𝒪 Patchₛ-A)
 f⁻₊ₘ = f⁻₊ , f⁻₊-is-monotone

\end{code}

\begin{code}

 f⁻₊-is-right-adjoint-of-f⁻⁺ : (f⁻⁺ₘ ⊣ f⁻₊ₘ) holds
 f⁻₊-is-right-adjoint-of-f⁻⁺ 𝒿@(j , _) U = ϑ₁ , ϑ₂
  where
   open IgorsLemma  X A A-has-basis
   open PerfectMaps X A A-has-basis
   open HeytingComplementationLemmas X X-has-basis

   ϑ₁ : (f⁻⁺ 𝒿 ≤ₓ U ⇒ 𝒿 ≤[ poset-of (𝒪 Patchₛ-A) ] (f⁻₊ U)) holds
   ϑ₁ φ n =
    adjunction-inequality-forwardₓ
     𝒻
     (U ∨[ 𝒪 X ] 𝒻 ⋆∙ (βₐ n))
     (j (βₐ n))
     ψ
      where
       open PosetReasoning (poset-of (𝒪 X))

       κ′ : is-clopen₀ (𝒪 X) (𝒻 ⋆∙ (βₐ n))
       κ′ = compacts-are-clopen-in-zd-locales
             X
             ∣ 𝕫ᴰ ∣
             (𝒻 ⋆∙ βₐ n)
             (μ (βₐ n) (κ n))

       ϟ : ((𝒻 ⋆∙ j (βₐ n) ∧[ 𝒪 X ] ((𝒻 ⋆∙ βₐ n) ==> 𝟎[ 𝒪 X ]))
                 ≤[ poset-of (𝒪 X) ]
                U) holds
       ϟ =
        𝒻 ⋆∙ j (βₐ n) ∧[ 𝒪 X ] ((𝒻 ⋆∙ βₐ n) ==> 𝟎[ 𝒪 X ]) ≤⟨ Ⅰ ⟩
        f⁻⁺₂ 𝒿                                          ＝⟨ Ⅱ   ⟩ₚ
        f⁻⁺  𝒿                                          ≤⟨ φ    ⟩
        U                                               ■
         where
          Ⅰ = ⋁[ 𝒪 X ]-upper
               ⁅ 𝒻 ⋆∙ j (βₐ n) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ n ∶ Bₐ ⁆
               n
          Ⅱ = f⁻⁺₂-equiv-f⁻⁺₁ 𝒿 ⁻¹

       ※ : (𝒻 ⋆∙ j (βₐ n) ≤[ poset-of (𝒪 X) ] (𝒻 ⋆∙ βₐ n ∨[ 𝒪 X ] U)) holds
       ※ = negation-∨-lemma₂ κ′ ϟ

       ψ : (𝒻 ⋆∙ j (βₐ n) ≤[ poset-of (𝒪 X) ] (U ∨[ 𝒪 X ] 𝒻 ⋆∙ βₐ n)) holds
       ψ = 𝒻 ⋆∙ j (βₐ n)          ≤⟨ ※ ⟩
           𝒻 ⋆∙ (βₐ n) ∨[ 𝒪 X ] U ＝⟨ ∨[ 𝒪 X ]-is-commutative (𝒻 ⋆∙ βₐ n) U ⟩ₚ
           U ∨[ 𝒪 X ] 𝒻 ⋆∙ (βₐ n) ■

   S =
    ⁅ (𝒻 ⋆∙ βₐ m) ∧ₓ ¬𝒻⋆ (βₐ n)
     ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝔏 𝒿 m n holds ⁆

   ϑ₂ : (𝒿 ≤[ poset-of (𝒪 Patchₛ-A) ] (f⁻₊ U)) holds
      → (f⁻⁺ 𝒿 ≤[ poset-of (𝒪 X) ] U) holds
   ϑ₂ φ = ⋁[ 𝒪 X ]-least S (U , †)
    where
     open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
     open PatchConstruction A σ using (⋁ₙ; _⋏_)

     † : (U is-an-upper-bound-of S) holds
     † (m , n , p) = goal
      where
       ψ : (U : ⟨ 𝒪 A ⟩)
         → (((‘ βₐ m ’ ⋏ ¬‘ βₖ n ’) .pr₁ U) ≤[ poset-of (𝒪 A)  ] j U) holds
       ψ = ≼ᵏ-implies-≼ (‘ βₐ m ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) 𝒿 p

       κ′ : is-clopen₀ (𝒪 X) (𝒻 ⋆∙ βₐ n)
       κ′ =
        compacts-are-clopen-in-zd-locales X ∣ 𝕫ᴰ ∣ (𝒻 ⋆∙ βₐ n) (μ (βₐ n) (κ n))

       ϡ : (T : ⟨ 𝒪 A ⟩)
         → (((𝒻 ⋆∙ (βₐ m ∨[ 𝒪 A ] T)) ∧[ 𝒪 X ] 𝒻 ⋆∙ (βₐ n ==>ₐ T))
             ≤[ poset-of (𝒪 X) ]
            (U ∨[ 𝒪 X ] 𝒻 ⋆∙ T)) holds
       ϡ T =
        let
         open PosetReasoning (poset-of (𝒪 X))
        in
         𝒻 ⋆∙ (βₐ m ∨[ 𝒪 A ] T) ∧[ 𝒪 X ] 𝒻 ⋆∙ (βₐ n ==>ₐ T)  ＝⟨ Ⅰ ⟩ₚ
         𝒻 ⋆∙ ((βₐ m ∨[ 𝒪 A ] T) ∧[ 𝒪 A ] (βₐ n ==>ₐ T))     ≤⟨ Ⅱ  ⟩
         U ∨[ 𝒪 X ] (𝒻 ⋆∙ T)                               ■
        where
         ♣ : (((βₐ m ∨[ 𝒪 A ] T) ∧[ 𝒪 A ] (βₐ n ==>ₐ T))
               ≤[ poset-of (𝒪 A) ]
              𝒻₊ (U ∨[ 𝒪 X ] (𝒻 ⋆∙ T))) holds
         ♣ = (βₐ m ∨[ 𝒪 A ] T) ∧[ 𝒪 A ] (βₐ n ==>ₐ T)    ≤⟨ Ⅰ ⟩
             j T                                       ≤⟨ Ⅱ ⟩
             𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ T)                    ■
          where
           open PosetReasoning (poset-of (𝒪 A))

           Ⅰ = ≼ᵏ-implies-≼ (‘ βₐ m ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) 𝒿 p T
           Ⅱ = ≼ᵏ-implies-≼ 𝒿 (f⁻₊ U) φ T

         Ⅰ = frame-homomorphisms-preserve-meets
              (𝒪 A)
              (𝒪 X)
              𝒻
              (βₐ m ∨[ 𝒪 A ] T)
              (βₐ n ==>ₐ T) ⁻¹
         Ⅱ = adjunction-inequality-backwardₓ
              𝒻
              (U ∨[ 𝒪 X ] 𝒻 ⋆∙ T)
              ((βₐ m ∨[ 𝒪 A ] T) ∧[ 𝒪 A ] (βₐ n ==>ₐ T))
              ♣

       ϟ : (𝒻 ⋆∙ βₐ m ≤[ poset-of (𝒪 X) ] (U ∨[ 𝒪 X ] 𝒻 ⋆∙ βₐ n)) holds
       ϟ = igors-lemma-⇐ 𝒻 (βₐ m) (βₐ n) U ϡ

       ϑ : (𝒻 ⋆∙ βₐ m ≤[ poset-of (𝒪 X) ] (𝒻 ⋆∙ βₐ n ∨[ 𝒪 X ] U)) holds
       ϑ = 𝒻 ⋆∙ βₐ m               ≤⟨ ϟ ⟩
           U ∨[ 𝒪 X ] 𝒻 ⋆∙ βₐ n    ＝⟨ ∨[ 𝒪 X ]-is-commutative U (𝒻 ⋆∙ βₐ n) ⟩ₚ
           𝒻 ⋆∙ βₐ n ∨[ 𝒪 X ] U    ■
            where
             open PosetReasoning (poset-of (𝒪 X))

       goal : (((𝒻 ⋆∙ βₐ m) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n)) ≤[ poset-of (𝒪 X) ] U) holds
       goal = negation-∨-lemma₁ κ′ ϑ

\end{code}

Proof that `f⁻⁺` preserves joins.

\begin{code}

 f⁻⁺-preserves-joins : is-join-preserving (𝒪 Patchₛ-A) (𝒪 X) f⁻⁺ holds
 f⁻⁺-preserves-joins = aft-forward f⁻⁺ₘ (f⁻₊ₘ , f⁻₊-is-right-adjoint-of-f⁻⁺)

 open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
  using () renaming (_is-lub-of_ to _is-lub-ofₓ_)

 𝒻⁻-γ : (S : Fam 𝓤 ⟨ 𝒪 Patchₛ-A ⟩)
      → (f⁻⁺ (⋁[ 𝒪 Patchₛ-A ] S) is-lub-ofₓ ⁅ f⁻⁺ 𝒿 ∣ 𝒿 ε S ⁆) holds
 𝒻⁻-γ S =
  transport
   (λ - → (- is-lub-ofₓ ⁅ f⁻⁺ 𝒿 ∣ 𝒿 ε S ⁆) holds)
   (f⁻⁺-preserves-joins S ⁻¹)
   (⋁[ 𝒪 X ]-upper ⁅ f⁻⁺ 𝒿 ∣ 𝒿 ε S ⁆ , ⋁[ 𝒪 X ]-least ⁅ f⁻⁺ 𝒿 ∣ 𝒿 ε S ⁆)

\end{code}

Now, we start working towards proving that `f⁻⁺` makes the aforementioned
diagram commute.

\begin{code}

 easy-lemma : (𝒻⁻₀@(f⁻₀ , _) : X ─c→ Patchₛ-A)
            → (n : Bₐ)
            → is-boolean-complement-of (𝒪 X) (f⁻₀ ¬‘ βₖ n ’) (f⁻₀ ‘ βₐ n ’) holds
 easy-lemma 𝒻⁻₀ n =
  frame-homomorphisms-preserve-complements (𝒪 Patchₛ-A) (𝒪 X) 𝒻⁻₀ †
   where
    open PatchComplementation A σᴰ

    ‡ : is-boolean-complement-of (𝒪 Patchₛ-A) ¬‘ βₖ n ’ ‘ βₐ n ’ holds
    ‡ = open-complements-closed (βₐ n) (pr₂ (βₖ n))

    † : is-boolean-complement-of (𝒪 Patchₛ-A) ‘ βₐ n ’ ¬‘ βₖ n ’ holds
    † = complementation-is-symmetric (𝒪 Patchₛ-A) ¬‘ βₖ n ’ ‘ βₐ n ’ ‡


\end{code}

A corollary of the "easy lemma" is that any continuous map `𝒻⁻₀` from `X` into
`Patch-A` that makes the diagram commute also satisfies

```
    𝒻⁻₀⁺ ¬‘ C ’ = ¬𝒻⁺ C ≡ 𝒻⁺ C ==> 𝟎
```

We call this lemma `commutes-with-open-nucleus`.

\begin{code}

 commutes-with-open-nucleus : (𝒻⁻₀@(f⁻₀ , _) : X ─c→ Patchₛ-A)
                            → ((n : Bₐ) → 𝒻 ⋆∙ (βₐ n) ＝ f⁻₀ ‘ βₐ n ’)
                            → (n : Bₐ) →  ¬𝒻⋆ (βₐ n) ＝ f⁻₀ ¬‘ βₖ n ’
 commutes-with-open-nucleus 𝒻⁻₀@(f⁻₀ , _) ϑ n =
  complements-are-unique (𝒪 X) (𝒻 ⋆∙ (βₐ n)) (¬𝒻⋆ (βₐ n)) (f⁻₀ ¬‘ βₖ n ’) φ ψ
   where
    open HeytingComplementationLemmas X X-has-basis

    ν : is-clopen (𝒪 X) (𝒻 ⋆∙ (βₐ n)) holds
    ν = compacts-are-clopen-in-zd-locales
         X
         ∣ 𝕫ᴰ ∣
         (𝒻 ⋆∙ βₐ n)
         (μ (βₐ n) (κ n))

    C = pr₁ ν

    C-complements-𝒻⋆βn : is-boolean-complement-of (𝒪 X) C (𝒻 ⋆∙ (βₐ n)) holds
    C-complements-𝒻⋆βn = pr₂ ν

    φ : is-boolean-complement-of (𝒪 X) (¬𝒻⋆ (βₐ n)) (𝒻 ⋆∙ (βₐ n)) holds
    φ = transport
         (λ - → is-boolean-complement-of (𝒪 X) - (𝒻 ⋆∙ (βₐ n)) holds)
         (complement-is-heyting-complement (𝒻 ⋆∙ (βₐ n)) C C-complements-𝒻⋆βn)
         C-complements-𝒻⋆βn

    ψ : is-boolean-complement-of (𝒪 X) (f⁻₀ ¬‘ βₖ n ’) (𝒻 ⋆∙ (βₐ n)) holds
    ψ = transport
         (λ - → is-boolean-complement-of (𝒪 X) (f⁻₀ ¬‘ βₖ n ’) - holds)
         (ϑ n ⁻¹)
         (easy-lemma 𝒻⁻₀ n)

\end{code}

Using `commutes-with-open-nucleus` and the `easy-lemma`, it is not hard to
prove that `𝒻⁻` makes the diagram commute.

\begin{code}

 𝒻⁻-makes-the-diagram-commute : (U : ⟨ 𝒪 A ⟩) → 𝒻 ⋆∙ U  ＝ f⁻⁺ ‘ U ’
 𝒻⁻-makes-the-diagram-commute U = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
  where
   𝟎-is-basic : is-basic A 𝟎[ 𝒪 A ] A-directed-basisᴰ holds
   𝟎-is-basic = compact-opens-are-basic A A-directed-basisᴰ 𝟎[ 𝒪 A ] (𝟎-is-compact A)

   ℒ : Fam 𝓤 Bₐ
   ℒ = covering-index-family (𝒪 A) (Bₐ , βₐ) β-is-basis-for-A U

   ℒ-covers-U : U ＝ ⋁[ 𝒪 A ] ⁅ βₐ l ∣ l ε ℒ ⁆
   ℒ-covers-U = covers (𝒪 A) (Bₐ , βₐ) β-is-basis-for-A U

   Ⅲ : ((⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (βₐ l) ∣ l ε ℒ ⁆) ≤[ poset-of (𝒪 X) ] f⁻⁺ ‘ U ’) holds
   Ⅲ = ⋁[ 𝒪 X ]-least ⁅ 𝒻 ⋆∙ (βₐ l) ∣ l ε ℒ ⁆ (f⁻⁺ ‘ U ’ , ※)
    where
     open Joins (λ x y → x ≤[ poset-of (𝒪 A) ] y)
      using () renaming (_is-lub-of_ to _is-lub-ofₐ_;
                         _is-an-upper-bound-of_ to _is-an-upper-bound-ofₐ_)

     ※ : (l : index ℒ) → (𝒻 ⋆∙ (βₐ (ℒ [ l ])) ≤[ poset-of (𝒪 X) ] f⁻⁺ ‘ U ’) holds
     ※ l = ∥∥-rec
            (holds-is-prop (𝒻 ⋆∙ (βₐ (ℒ [ l ])) ≤[ poset-of (𝒪 X) ] f⁻⁺ ‘ U ’))
            ♣
            𝟎-is-basic
      where
       ♣ : Σ t ꞉ Bₐ , βₐ t ＝ 𝟎[ 𝒪 A ]
         → (𝒻 ⋆∙ βₐ (ℒ [ l ]) ≤[ poset-of (𝒪 X) ] f⁻⁺ ‘ U ’) holds
       ♣ (t , q) =
        let
         open PosetReasoning (poset-of (𝒪 X))
        in
         𝒻 ⋆∙ (βₐ (ℒ [ l ]))                         ＝⟨ 𝟏 ⟩ₚ
         𝒻 ⋆∙ (βₐ (ℒ [ l ])) ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]       ＝⟨ 𝟐 ⟩ₚ
         𝒻 ⋆∙ (βₐ (ℒ [ l ])) ∧[ 𝒪 X ] ¬𝒻⋆ 𝟎[ 𝒪 A ]   ＝⟨ 𝟑 ⟩ₚ
         𝒻 ⋆∙ (βₐ (ℒ [ l ])) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ t)      ≤⟨ 𝟒  ⟩
         f⁻⁺ ‘ U ’                                  ■
          where
           ♠ = λ n →
            let
             open PosetReasoning (poset-of (𝒪 A))
             ※ = βₐ (ℒ [ l ])                ≤⟨ ⋁[ 𝒪 A ]-upper ⁅ βₐ l ∣ l ε ℒ ⁆ l ⟩
                 ⋁[ 𝒪 A ] ⁅ βₐ l ∣ l ε ℒ ⁆   ＝⟨ ℒ-covers-U ⁻¹                   ⟩ₚ
                 U                          ≤⟨ ∨[ 𝒪 A ]-upper₁ U (βₐ n)          ⟩
                 U ∨[ 𝒪 A ] βₐ n             ■
             𝕒 = ap (λ - → (βₐ (ℒ [ l ]) ∨[ 𝒪 A ] βₐ n) ∧[ 𝒪 A ] (- ==>ₐ βₐ n)) q
             𝕓 = ap
                  (λ - → (βₐ (ℒ [ l ]) ∨[ 𝒪 A ] βₐ n) ∧[ 𝒪 A ] -)
                  (only-𝟏-is-above-𝟏
                    (𝒪 A)
                    (𝟎[ 𝒪 A ] ==>ₐ βₐ n)
                    (ex-falso-quodlibetₐ (βₐ n)))
             𝕔 = 𝟏-right-unit-of-∧ (𝒪 A) (βₐ (ℒ [ l ]) ∨[ 𝒪 A ] βₐ n)
             𝕕 = ∨[ 𝒪 A ]-least ※ (∨[ 𝒪 A ]-upper₂ U (βₐ n))
            in
             (βₐ (ℒ [ l ]) ∨[ 𝒪 A ] βₐ n) ∧[ 𝒪 A ] (βₐ t ==>ₐ βₐ n)      ＝⟨ 𝕒 ⟩ₚ
             (βₐ (ℒ [ l ]) ∨[ 𝒪 A ] βₐ n) ∧[ 𝒪 A ] (𝟎[ 𝒪 A ] ==>ₐ βₐ n) ＝⟨ 𝕓 ⟩ₚ
             (βₐ (ℒ [ l ]) ∨[ 𝒪 A ] βₐ n) ∧[ 𝒪 A ] 𝟏[ 𝒪 A ]            ＝⟨ 𝕔 ⟩ₚ
             βₐ (ℒ [ l ]) ∨[ 𝒪 A ] βₐ n                                ≤⟨ 𝕕  ⟩
             U ∨[ 𝒪 A ] βₐ n                                          ■

           𝟏 = 𝟏-right-unit-of-∧ (𝒪 X) (𝒻 ⋆∙ (βₐ (ℒ [ l ]))) ⁻¹
           𝟐 = ap (λ - → 𝒻 ⋆∙ βₐ (ℒ [ l ]) ∧[ 𝒪 X ] -)   (¬𝒻⋆𝟎-is-𝟏 ⁻¹)
           𝟑 = ap (λ - → 𝒻 ⋆∙ βₐ (ℒ [ l ]) ∧[ 𝒪 X ] ¬𝒻⋆ -) (q ⁻¹)
           𝟒 = ⋁[ 𝒪 X ]-upper
                ⁅ 𝒻 ⋆∙ βₐ m ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ (m , n , p) ∶ below ‘ U ’ ⁆
                (ℒ [ l ] , t , ♠)

   † : (𝒻 ⋆∙ U ≤[ poset-of (𝒪 X) ] f⁻⁺ ‘ U ’) holds
   † =
    let
     open PosetReasoning (poset-of (𝒪 X))
    in
     𝒻 ⋆∙ U                            ＝⟨ Ⅰ ⟩ₚ
     𝒻 ⋆∙ (⋁[ 𝒪 A ] ⁅ βₐ l ∣ l ε ℒ ⁆)   ＝⟨ Ⅱ ⟩ₚ
     ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (βₐ l) ∣ l ε ℒ ⁆   ≤⟨  Ⅲ ⟩
     f⁻⁺ ‘ U ’                         ■
      where
       Ⅰ = ap (𝒻 ⋆∙_) ℒ-covers-U
       Ⅱ = frame-homomorphisms-preserve-all-joins′ (𝒪 A) (𝒪 X) 𝒻 ⁅ βₐ l ∣ l ε ℒ ⁆

   ‡ : (f⁻⁺ ‘ U ’ ≤[ poset-of (𝒪 X) ] 𝒻 ⋆∙ U) holds
   ‡ = f⁻⁺  ‘ U ’  ＝⟨ f⁻⁺₂-equiv-f⁻⁺₁ ‘ U ’ ⟩ₚ
       f⁻⁺₂ ‘ U ’  ≤⟨ ※                      ⟩
       𝒻 ⋆∙ U      ■
    where
     open PosetReasoning (poset-of (𝒪 X))

     ϟ : (n : Bₐ)
       → ((𝒻 ⋆∙ (U ∨[ 𝒪 A ] βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n)) ≤ₓ 𝒻 ⋆∙ U) holds
     ϟ n =
      𝒻 ⋆∙ (U ∨[ 𝒪 A ] βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n)                         ＝⟨ 𝟏 ⟩ₚ
      (𝒻 ⋆∙ U ∨[ 𝒪 X ] 𝒻 ⋆∙ βₐ n) ∧ₓ ((𝒻 ⋆∙ (βₐ n)) ==> 𝟎[ 𝒪 X ])  ＝⟨ 𝟐 ⟩ₚ
      (𝒻 ⋆∙ U ∧ₓ ¬𝒻⋆ (βₐ n)) ∨[ 𝒪 X ] (𝒻 ⋆∙ (βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n))   ≤⟨  𝟑 ⟩
      𝒻 ⋆∙ U ∨[ 𝒪 X ] (𝒻 ⋆∙ (βₐ n) ∧ₓ ¬𝒻⋆ (βₐ n))                  ≤⟨  𝟒 ⟩
      (𝒻 ⋆∙ U) ∨[ 𝒪 X ] 𝟎[ 𝒪 X ]                                 ＝⟨ 𝟓 ⟩ₚ
      𝒻 ⋆∙ U                                                     ■
       where
        𝟏 = ap
             (λ - → - ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n))
             (frame-homomorphisms-preserve-binary-joins (𝒪 A) (𝒪 X) 𝒻 U (βₐ n))
        𝟐 = binary-distributivity-right (𝒪 X)
        𝟑 = ∨[ 𝒪 X ]-left-monotone
             (∧[ 𝒪 X ]-lower₁
               (𝒻 ⋆∙ U)
               ((𝒻 ⋆∙ βₐ n) ==> 𝟎[ 𝒪 X ]))
        𝟒 = ∨[ 𝒪 X ]-right-monotone (mp-left (𝒻 ⋆∙ βₐ n) 𝟎[ 𝒪 X ])
        𝟓 =  𝟎-left-unit-of-∨ (𝒪 X) (𝒻 ⋆∙ U)

     ※ = ⋁[ 𝒪 X ]-least
          ⁅ 𝒻 ⋆∙ (U ∨[ 𝒪 A ] βₐ n) ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ n) ∣ n ∶ Bₐ ⁆
          (𝒻 ⋆∙ U , ϟ)

\end{code}

We now package up the function `f⁻` with the proof that it's a continuous map.

\begin{code}

 𝒻⁻⁺ : X ─c→ Patchₛ-A
 𝒻⁻⁺ = f⁻⁺ , 𝒻⁻-α , 𝒻⁻-β , 𝒻⁻-γ

\end{code}

\section{Uniqueness}

First, the extensional equality which is the main content of the uniqueness
proof.

\begin{code}

 𝒻⁻-is-unique-ext : (𝒻⁻₀@(f⁻₀ , _) : X ─c→ Patchₛ-A)
                  → (((U : ⟨ 𝒪 A ⟩) → 𝒻 ⋆∙ U  ＝ f⁻₀ ‘ U ’) )
                  → (𝒿 : ⟨ 𝒪 Patchₛ-A ⟩) → f⁻⁺ 𝒿 ＝ f⁻₀ 𝒿
 𝒻⁻-is-unique-ext 𝒻⁻₀@(f⁻₀ , _) ϑ 𝒿 =
  f⁻⁺ 𝒿                                                                 ＝⟨ Ⅰ ⟩
  f⁻⁺ (⋁ₙ ⁅ (𝔠 k) ⋏ (𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆)            ＝⟨ Ⅱ ⟩
  ⋁[ 𝒪 X ] ⁅ f⁻⁺ (𝔠 k ⋏ 𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆          ＝⟨ Ⅲ ⟩
  ⋁[ 𝒪 X ] ⁅ f⁻⁺ (𝔠 k) ∧ₓ f⁻⁺ (𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆   ＝⟨ Ⅳ ⟩
  ⋁[ 𝒪 X ] ⁅ f⁻⁺ (𝔠 k) ∧ₓ ¬𝒻⋆ (βₐ l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆   ＝⟨ Ⅴ ⟩
  ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (βₐ k) ∧ₓ ¬𝒻⋆ (βₐ l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆  ＝⟨ Ⅵ ⟩
  ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (βₐ k) ∧ₓ f⁻₀ (𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆  ＝⟨ Ⅶ ⟩
  ⋁[ 𝒪 X ] ⁅ f⁻₀ (𝔠 k) ∧ₓ f⁻₀ (𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆   ＝⟨ Ⅷ ⟩
  ⋁[ 𝒪 X ] ⁅ f⁻₀ (𝔠 k ⋏ 𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆          ＝⟨ Ⅸ ⟩
  f⁻₀ (⋁ₙ ⁅ 𝔠 k ⋏ 𝔬 l ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆)                ＝⟨ Ⅹ ⟩
  f⁻₀ 𝒿                                                                 ∎
   where
    open BasisOfPatch A σᴰ hiding (σ)
    open PatchConstruction A σ using (⋁ₙ; _⋏_)

    ν : 𝒿 ＝ ⋁[ 𝒪 Patchₛ-A ] ⁅ 𝔠 k ⋏ 𝔬 l ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆
    ν = main-covering-lemma 𝒿

    Ⅰ = ap f⁻⁺ ν
    Ⅱ = ⋁[ 𝒪 X ]-unique
         ⁅ f⁻⁺ (𝔠 k ∧[ 𝒪 Patchₛ-A ] 𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆
         (f⁻⁺ (⋁[ 𝒪 Patchₛ-A ] ⁅ 𝔠 k ⋏ 𝔬 l ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆))
         (𝒻⁻-γ ⁅ 𝔠 k ∧[ 𝒪 Patchₛ-A ] 𝔬 l ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆)
    Ⅲ = ap
         (λ - → ⋁[ 𝒪 X ] (basic-below 𝒿 , -))
         (dfunext fe (λ { ((k , l) , p) → 𝒻⁻-β (𝔠 k) (𝔬 l)}))

    ctx = λ - → ⋁[ 𝒪 X ] (basic-below 𝒿 , -)

    Ⅳ = ap
         ctx
         (dfunext fe (λ { ((k , l) , p) →
           ap
            (λ - → (f⁻⁺ (𝔠 k)) ∧[ 𝒪 X ] -)
            (commutes-with-open-nucleus 𝒻⁻⁺ ※ l ⁻¹)}))
             where
              ※ = 𝒻⁻-makes-the-diagram-commute ∘ βₐ
    Ⅴ = ap
         ctx
         ((dfunext fe (λ { ((k , l) , p) →
            ap
             (λ - → - ∧[ 𝒪 X ] ¬𝒻⋆ (βₐ l))
             (𝒻⁻-makes-the-diagram-commute (βₐ k) ⁻¹)})))
    Ⅵ = ap
         ctx
         (dfunext fe λ { ((k , l) , p) →
           ap
            (λ - → 𝒻 ⋆∙ (βₐ k) ∧[ 𝒪 X ] -)
            (commutes-with-open-nucleus 𝒻⁻₀ (ϑ ∘ βₐ) l)})
    Ⅶ = ap
         ctx
         (dfunext fe λ { ((k , l) , p) →
           ap
            (λ - → - ∧[ 𝒪 X ] f⁻₀ (𝔬 l))
            (ϑ (βₐ k))})
    Ⅷ = ap
         ctx
         (dfunext fe λ { ((k , l) , p) →
          frame-homomorphisms-preserve-meets
           (𝒪 Patchₛ-A)
           (𝒪 X)
           𝒻⁻₀
           (𝔠 k)
           (𝔬 l) ⁻¹} )
    Ⅸ = frame-homomorphisms-preserve-all-joins′
         (𝒪 Patchₛ-A)
         (𝒪 X)
         𝒻⁻₀
         ⁅ 𝔠 k ∧[ 𝒪 Patchₛ-A ] 𝔬 l ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆ ⁻¹
    Ⅹ = ap f⁻₀ ν ⁻¹

 𝒻⁻-is-unique : is-central
                 (Σ 𝒻⁻₀ ꞉ (X ─c→ Patchₛ-A) ,
                  ((U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U  ＝ 𝒻⁻₀ .pr₁ ‘ U ’))
                 ((f⁻⁺ , 𝒻⁻-α , 𝒻⁻-β , 𝒻⁻-γ) , 𝒻⁻-makes-the-diagram-commute)
 𝒻⁻-is-unique (𝒻⁻₀@(f⁻₀ , _ , _ , 𝒻⁻₀-γ) , ϑ) =
  to-subtype-＝ ※ (to-subtype-＝ γ (dfunext fe †))
   where
    ※ : (𝒻⁻₀ : X ─c→ Patchₛ-A)
      → is-prop ((U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U  ＝ 𝒻⁻₀ .pr₁ ‘ U ’)
    ※ 𝒻⁻₀ = Π-is-prop fe λ _ → carrier-of-[ poset-of (𝒪 X) ]-is-set

    γ : (ℊ⁻ : ⟨ 𝒪 Patchₛ-A ⟩ → ⟨ 𝒪 X ⟩)
       → is-prop (is-a-frame-homomorphism (𝒪 Patchₛ-A) (𝒪 X) ℊ⁻ holds)
    γ ℊ⁻ = holds-is-prop (is-a-frame-homomorphism (𝒪 Patchₛ-A) (𝒪 X) ℊ⁻)

    open HeytingComplementationLemmas X X-has-basis
    open BasisOfPatch A σᴰ

    † : (𝒿 : ⟨ 𝒪 Patchₛ-A ⟩) → f⁻⁺ 𝒿 ＝ f⁻₀ 𝒿
    † = 𝒻⁻-is-unique-ext 𝒻⁻₀ ϑ

 proof-of-ump : ∃! 𝒻⁻ ꞉ (X ─c→ Patchₛ-A) , ((U : ⟨ 𝒪 A ⟩) → 𝒻 ⋆∙ U  ＝ 𝒻⁻ .pr₁ ‘ U ’)
 proof-of-ump =
  ((f⁻⁺ , 𝒻⁻-α , 𝒻⁻-β , 𝒻⁻-γ) , 𝒻⁻-makes-the-diagram-commute) , 𝒻⁻-is-unique

ump-of-patch : {𝓤  : Universe}
             → (A  : Locale (𝓤 ⁺) 𝓤 𝓤)
             → (σ  : is-spectral A holds)
             → (sk : has-small-𝒦 A)
             → (X : Locale (𝓤 ⁺) 𝓤 𝓤)
             → is-stone X holds
             → (𝒻@(f , _) : X ─c→ A)
             → is-spectral-map A X 𝒻 holds
             → let
                σ′ : spectralᴰ A
                σ′ = spectral-and-small-𝒦-implies-spectralᴰ A σ sk

                open PatchConstruction A σ renaming (Patch to Patch-A)
                open ClosedNucleus A σ
                open OpenNucleus A σ′
               in
                ∃! 𝒻⁻ ꞉ X ─c→ Patch-A , ((U : ⟨ 𝒪 A ⟩) → f U  ＝ 𝒻⁻ .pr₁ ‘ U ’)
ump-of-patch {𝓤} A σ sk X 𝕤 𝒻 μ = ∥∥-rec₂ (being-singleton-is-prop fe) γ ∣ σ′ ∣ (pr₂ 𝕤)
 where
  σ′ : spectralᴰ A
  σ′ = spectral-and-small-𝒦-implies-spectralᴰ A σ sk

  open PatchConstruction A σ renaming (Patch to Patch-A)
  open ClosedNucleus A σ
  open OpenNucleus A σ′

  γ : spectralᴰ A
    → zero-dimensionalᴰ (𝒪 X)
    → ∃! 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U  ＝ 𝒻⁻ .pr₁ ‘ U ’)
  γ σᴰ 𝕫ᴰ = (𝒻⁻₀ , 𝒻⁻-makes-the-diagram-commute) , 𝔠
   where
    open UniversalProperty A X σᴰ 𝕫ᴰ (pr₁ 𝕤) 𝒻 μ
    open SmallPatchConstruction A σᴰ renaming (SmallPatch to Patchₛ-A)

    𝒻⁻₀ : X ─c→ Patch-A
    𝒻⁻₀ = f⁻⁺ , 𝒻⁻-α , 𝒻⁻-β , 𝒻⁻-γ

    𝔠 : is-central
         ((Σ 𝒻⁻₀ ꞉ (X ─c→ Patch-A) , ((U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U  ＝ 𝒻⁻₀ .pr₁ ‘ U ’)))
         (𝒻⁻₀ , 𝒻⁻-makes-the-diagram-commute)
    𝔠 (𝒻⁻₁@(f⁻₁ , α₁ , β₁ , γ₁) , p) =
     to-subtype-＝ ♣ (to-subtype-＝ ♠ (dfunext fe (𝒻⁻-is-unique-ext 𝒻⁻₁′ p)))
      where
       open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
       open PosetReasoning (poset-of (𝒪 X))

       𝒻⁻₁′ : X ─c→ Patchₛ-A
       𝒻⁻₁′ = f⁻₁ , α₁ , β₁ , γ₁′
        where
         γ₁′ : (S : Fam 𝓤 ⟨ 𝒪 Patchₛ-A ⟩)
             → (f⁻₁ (⋁[ 𝒪 Patchₛ-A ] S) is-lub-of ⁅ f⁻₁ U ∣ U ε S ⁆) holds
         γ₁′ S = † , ‡
          where
           † = λ i →
                meet-preserving-implies-monotone
                 (𝒪 Patchₛ-A)
                 (𝒪 X)
                 f⁻₁
                 β₁
                 (_ , _)
                 (⋁[ 𝒪 Patchₛ-A ]-upper S i)

           open Joins _≼ᵏ_
            using ()
            renaming (_is-an-upper-bound-of_ to _is-an-upper-bound-ofₙ_)
           open Joins _≼_
            using ()
            renaming (_is-an-upper-bound-of_ to _is-an-upper-bound-ofₖ_)

           -- TODO: the following two things are definitionally equal and
           -- I don't understand why Agda cannot realise this.
           φ : ⋁[ 𝒪 Patchₛ-A ] S ＝ ⋁[ 𝒪 Patch-A ] S
           φ = ≤-is-antisymmetric (poset-of (𝒪 Patchₛ-A)) φ₁ φ₂
            where
             ψ₁ : ((⋁[ 𝒪 Patchₛ-A ] S) is-an-upper-bound-ofₙ S) holds
             ψ₁ i = ≼-implies-≼ᵏ
                     (S [ i ])
                     (⋁[ 𝒪 Patch-A ] S)
                     (⋁[ 𝒪 Patch-A ]-upper S i)

             φ₁ : ((⋁[ 𝒪 Patchₛ-A ] S) ≼ᵏ (⋁[ 𝒪 Patch-A ] S)) holds
             φ₁ = ⋁[ 𝒪 Patchₛ-A ]-least S ((⋁[ 𝒪 Patch-A ] S) , ψ₁)

             ψ₂ : ((⋁[ 𝒪 Patch-A ] S) is-an-upper-bound-ofₖ S) holds
             ψ₂ i = ≼ᵏ-implies-≼
                     (S [ i ])
                     (⋁[ 𝒪 Patchₛ-A ] S)
                     (⋁[ 𝒪 Patchₛ-A ]-upper S i)

             φ₂ : ((⋁[ 𝒪 Patch-A ] S) ≼ᵏ (⋁[ 𝒪 Patchₛ-A ] S)) holds
             φ₂ = ⋁[ 𝒪 Patch-A ]-least S ((⋁[ 𝒪 Patchₛ-A ] S) , ψ₂) ∘ βₐ

           ‡ : ((U , _) : upper-bound ⁅ f⁻₁ U ∣ U ε S ⁆)
             → (f⁻₁ (⋁[ 𝒪 Patchₛ-A ] S) ≤ₓ U) holds
           ‡ (U , p) = f⁻₁ (⋁[ 𝒪 Patchₛ-A ] S)   ＝⟨ ap (𝒻⁻₁ .pr₁) φ   ⟩ₚ
                       f⁻₁ (⋁[ 𝒪 Patch-A ] S)    ≤⟨ pr₂ (γ₁ S) (U , p) ⟩
                       U                         ■

       ♣ : (𝒻⁻₂ : X ─c→ Patch-A)
         → is-prop ((U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U ＝ 𝒻⁻₂ .pr₁ ‘ U ’)
       ♣ 𝒻⁻₂ = Π-is-prop fe (λ _ → carrier-of-[ poset-of (𝒪 X) ]-is-set)

       ♠ : (𝒻⁻₂ : ⟨ 𝒪 Patch-A ⟩ → ⟨ 𝒪 X ⟩)
         → is-prop (is-a-frame-homomorphism (𝒪 Patch-A) (𝒪 X) 𝒻⁻₂ holds)
       ♠ = holds-is-prop ∘ is-a-frame-homomorphism (𝒪 Patch-A) (𝒪 X)

       ϟ : (𝒿 : ⟨ 𝒪 Patch-A ⟩) → f⁻⁺ 𝒿 ＝ f⁻₁ 𝒿
       ϟ = 𝒻⁻-is-unique-ext 𝒻⁻₁′ p

{--

-- --}
-- --}
-- --}

\end{code}

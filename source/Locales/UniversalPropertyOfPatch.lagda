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
                         (σᴰ : spectralᴰ (𝒪 A))
                         (𝕫ᴰ : zero-dimensionalᴰ (𝒪 X))
                         (𝕜  : is-compact (𝒪 X) holds)
                         (𝒻 : X ─c→ A)
                         (μ : is-spectral-map (𝒪 A) (𝒪 X) 𝒻 holds) where

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

 open PatchConstruction A ∣ σᴰ ∣  using (nucleus-of; _≼_; _$_; perfect-nuclei-eq; idₙ; 𝔡𝔦𝔯)
 open ClosedNucleus     A ∣ σᴰ ∣
 open OpenNucleus       A ∣ σᴰ ∣

 open SmallPatchConstruction A σᴰ
  using (𝟎-is-id; ≼-implies-≼ᵏ; ≼ᵏ-implies-≼; _≼ᵏ_)
  renaming (SmallPatch to Patchₛ-A)
 open ContinuousMapNotation X A hiding (_⋆)

\end{code}

\begin{code}

 X-has-basis : has-basis (𝒪 X) holds
 X-has-basis = ∣ pr₁ 𝕫ᴰ , pr₁ (pr₁ (pr₂ 𝕫ᴰ)) ∣

\end{code}

We denote by `Bₐ` the index set of the basis of `A` and by `β` the enumeration
function of the basis.

\begin{code}

 Bₐ : 𝓤  ̇
 Bₐ = pr₁ (pr₁ σᴰ)

 β : Bₐ → ⟨ 𝒪 A ⟩
 β = pr₂ (pr₁ σᴰ)

\end{code}

Similarly by `Bₓ`, we denote the index set of the basis of `X` and by `βₓ`
the enumeration function.

\begin{code}

 Bₓ : 𝓤  ̇
 Bₓ = pr₁ (pr₁ 𝕫ᴰ)

 βₓ : Bₓ → ⟨ 𝒪 X ⟩
 βₓ = pr₂ (pr₁ 𝕫ᴰ)

\end{code}

\begin{code}

 β-is-directed-basis : is-directed-basis (𝒪 A) (Bₐ , β)
 β-is-directed-basis = pr₁ (pr₂ σᴰ)

 β-is-basis-for-A : is-basis-for (𝒪 A) (Bₐ , β)
 β-is-basis-for-A = pr₁ β-is-directed-basis

 A-has-basis : has-basis (𝒪 A) holds
 A-has-basis = spectral-frames-have-bases (𝒪 A) ∣ σᴰ ∣

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

It is often convenient to have a version of `β` that also gives the proof
of compactness of the basic open it returns.

\begin{code}

 βₖ : Bₐ → 𝒦
 βₖ m = β m , pr₁ (pr₂ (pr₂ σᴰ)) m

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
 𝔏 𝒿 m n = (‘ β m ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) ≼ᵏ 𝒿

 below : ⟨ 𝒪 Patchₛ-A ⟩ → 𝓤  ̇
 below 𝒿 = Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝔏 𝒿 m n holds

\end{code}

This is the unique function that we define that makes our diagram commute.

\begin{code}

 f⁻⁺ : ⟨ 𝒪 Patchₛ-A ⟩ → ⟨ 𝒪 X ⟩
 f⁻⁺ 𝒿 = ⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ β m) ∧ₓ ¬𝒻⋆ (β n) ∣ (m , n , p) ∶ below 𝒿 ⁆

\end{code}

There is an equivalent way to define `f⁻⁺`, given in `f⁻⁺₂` below. The
equivalence of the two is quite important and is used in the proofs below.

\begin{code}

 f⁻⁺₂ : ⟨ 𝒪 Patchₛ-A ⟩ → ⟨ 𝒪 X ⟩
 f⁻⁺₂ 𝒿@(j , _) = ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆

 f⁻⁺₂-equiv-f⁻⁺₁ : (𝒿 : ⟨ 𝒪 Patchₛ-A ⟩) → f⁻⁺ 𝒿 ＝ f⁻⁺₂ 𝒿
 f⁻⁺₂-equiv-f⁻⁺₁ 𝒿@(j , _) = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
  where
   S : Fam 𝓤 ⟨ 𝒪 X ⟩
   S = ⁅ (𝒻 ⋆∙ β m) ∧ₓ ¬𝒻⋆ (β n) ∣ (m , n , p) ∶ below 𝒿 ⁆

   T : Fam 𝓤 ⟨ 𝒪 X ⟩
   T = ⁅ 𝒻 ⋆∙ j (β n) ∧ₓ ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆

   †₀ : cofinal-in (𝒪 X) S T holds
   †₀ (m , n , p) = ∣ n , ※ ∣
    where
     open PosetReasoning (poset-of (𝒪 A))

     Ⅰ = ∨[ 𝒪 A ]-upper₁ (β m) (β n)
     Ⅱ = 𝟏-right-unit-of-∧ (𝒪 A) (β m ∨[ 𝒪 A ] β n) ⁻¹
     Ⅲ = ap
          (λ - → (β m ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] -)
          (heyting-implication-identityₐ (β n) ⁻¹)

     q : (β m ≤[ poset-of (𝒪 A) ] j (β n)) holds
     q = β m                                                ≤⟨ Ⅰ     ⟩
         β m ∨[ 𝒪 A ] β n                                   ＝⟨ Ⅱ    ⟩ₚ
         (β m ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] 𝟏[ 𝒪 A ]               ＝⟨ Ⅲ    ⟩ₚ
         (β m ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] (β n ==>ₐ β n)         ＝⟨ refl ⟩ₚ
         (β m ∨[ 𝒪 A ] β n) ∧[ 𝒪 A ] (¬‘ βₖ n ’ .pr₁ (β n)) ＝⟨ refl ⟩ₚ
         (‘ β m ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) .pr₁ (β n)     ≤⟨ p n   ⟩
         j (β n)                                            ■

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
       𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)                       ＝⟨ Ⅰ  ⟩ₚ
       𝒻 ⋆∙ (⋁[ 𝒪 A ] ⁅ β i ∣ i ε 𝒥 ⁆) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)    ＝⟨ Ⅱ  ⟩ₚ
       (⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (β i) ∣ i ε 𝒥 ⁆) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)  ＝⟨ Ⅲ  ⟩ₚ
       ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (β i) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ i ε 𝒥 ⁆    ≤⟨ Ⅳ   ⟩
       ⋁[ 𝒪 X ] S                                            ■
      where
       𝒥 : Fam 𝓤 Bₐ
       𝒥 = pr₁ (pr₁ (pr₁ (pr₂ σᴰ)) (j (β n)))

       ♠ : ((⋁[ 𝒪 X ] S)
             is-an-upper-bound-of
            ⁅ 𝒻 ⋆∙ (β i) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ i ε 𝒥 ⁆) holds
       ♠ i = ⋁[ 𝒪 X ]-upper S (𝒥 [ i ] , n , ♢)
        where
         open PosetReasoning (poset-of (𝒪 A))
         open NucleusHeytingImplicationLaw A A-has-basis (nucleus-of 𝒿)

         ♢ : 𝔏 𝒿 (𝒥 [ i ]) n holds
         ♢ m =
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
            Ⅳ = ∧[ 𝒪 A ]-left-monotone
                 (∨[ 𝒪 A ]-right-monotone (𝓃₁ (𝒪 A) (nucleus-of 𝒿) (β m)))
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
       Ⅳ = ⋁[ 𝒪 X ]-least ⁅ 𝒻 ⋆∙ (β i) ∧ₓ ¬𝒻⋆ (β n) ∣ i ε 𝒥 ⁆ ((⋁[ 𝒪 X ] S) , ♠)

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
   𝒮 = ⁅ (𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)
         ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝔏 𝒿 m n holds ⁆

   𝒯 : Fam 𝓤 ⟨ 𝒪 X ⟩
   𝒯 = ⁅ (𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)
         ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝔏 𝓀 m n holds ⁆

   † : cofinal-in (𝒪 X) 𝒮 𝒯 holds
   † (m , n , q) = ∣ (m , n , ‡) , ♣ ∣
    where
     open PosetReasoning (poset-of (𝒪 A))

     ‡ : 𝔏 𝓀 m n holds
     ‡ l = (‘ β m ’ ∧[ 𝒪 Patchₛ-A ] ¬‘ βₖ n ’) .pr₁ (β l)   ≤⟨ q l ⟩
           𝒿 $ (β l)                                        ≤⟨ p l ⟩
           𝓀 $ (β l)                                        ■

     ♣ : (_ ≤[ poset-of (𝒪 X) ] _) holds
     ♣ = ≤-is-reflexive (poset-of (𝒪 X)) ((𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))

 f⁻⁺ₘ : poset-of (𝒪 Patchₛ-A) ─m→ poset-of (𝒪 X)
 f⁻⁺ₘ = f⁻⁺ , f⁻⁺-is-monotone

\end{code}

\begin{code}

 open PatchStoneᴰ A σᴰ

 Patchₛ-A-has-basis : has-basis (𝒪 Patchₛ-A) holds
 Patchₛ-A-has-basis = spectral-frames-have-bases
                       (𝒪 Patchₛ-A)
                       patchₛ-is-spectral

\end{code}

Some horrible import bureaucracy below 😬

\begin{code}

 open AdjointFunctorTheorem X Patchₛ-A Patchₛ-A-has-basis
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
 open GaloisConnectionBetween (poset-of (𝒪 Patchₛ-A)) (poset-of (𝒪 X))
 open GaloisConnectionBetween (poset-of (𝒪 X)) (poset-of (𝒪 A))
  using () renaming (counit to counitₓ)
 open GaloisConnectionBetween (poset-of (𝒪 A)) (poset-of (𝒪 X))
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
   † = ∥∥-rec
        (holds-is-prop (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] f⁻⁺ 𝟏[ 𝒪 Patchₛ-A ]))
        ‡
        (compact-opens-are-basic-in-compact-frames
          (𝒪 A)
          (Bₐ , β)
          (pr₁ (pr₂ σᴰ))
          (spectral-implies-compact (𝒪 A) ∣ σᴰ ∣)
          𝟎[ 𝒪 A ]
          (𝟎-is-compact (𝒪 A)))
        where
         ‡ : Σ i ꞉ Bₐ , 𝟎[ 𝒪 A ] ＝ β i
           → (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] f⁻⁺ 𝟏[ 𝒪 Patchₛ-A ]) holds
         ‡ (i , p) =
          𝟏[ 𝒪 X ]                                                ＝⟨ Ⅰ    ⟩ₚ
          𝟏[ 𝒪 X ] ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                              ＝⟨ Ⅱ    ⟩ₚ
          𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                         ＝⟨ Ⅲ    ⟩ₚ
          𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] ¬𝒻⋆ (β i)                        ≤⟨  Ⅳ    ⟩
          ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ 𝟏[ 𝒪 A ] ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆  ＝⟨ refl ⟩ₚ
          f⁻⁺₂ 𝟏[ 𝒪 Patchₛ-A ]                                    ＝⟨ Ⅴ    ⟩ₚ
          f⁻⁺  𝟏[ 𝒪 Patchₛ-A ]                                    ■
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

\end{code}

The function `f⁻⁺` preserves binary meets.

\begin{code}

 𝒻⁻-β : preserves-binary-meets (𝒪 Patchₛ-A) (𝒪 X) f⁻⁺ holds
 𝒻⁻-β 𝒿@(j , _) 𝓀@(k , _) =

  f⁻⁺ (𝒿 ∧[ 𝒪 Patchₛ-A ] 𝓀)

   ＝⟨ Ⅰ ⟩

  f⁻⁺₂ (𝒿 ∧[ 𝒪 Patchₛ-A ] 𝓀)

   ＝⟨ refl ⟩

  ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (j (β n) ∧[ 𝒪 A ] k (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆

   ＝⟨ Ⅱ    ⟩

  ⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] 𝒻 ⋆∙ k (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆

   ＝⟨ Ⅲ ⟩

  ⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ j (β n)  ∧[ 𝒪 X ] ¬𝒻⋆ (β n))
             ∧[ 𝒪 X ]
             (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ∣ n ∶ Bₐ ⁆
   ＝⟨ Ⅳ ⟩

  ⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ j (β m)  ∧[ 𝒪 X ] ¬𝒻⋆ (β m))
             ∧[ 𝒪 X ]
             (𝒻 ⋆∙ k (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ∣ (m , n) ∶ Bₐ × Bₐ ⁆

   ＝⟨ Ⅴ ⟩

  (⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ j (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆)
   ∧[ 𝒪 X ]
  (⋁[ 𝒪 X ] ⁅ (𝒻 ⋆∙ k (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆)

   ＝⟨ refl ⟩

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
            𝒻 ⋆∙ j (β n) ∧ₓ 𝒻 ⋆∙ k (β n) ∧ₓ ¬𝒻⋆ (β n)
             ＝⟨ 𝕒 ⟩
            𝒻 ⋆∙ j (β n) ∧ₓ 𝒻 ⋆∙ k (β n) ∧ₓ (¬𝒻⋆ (β n) ∧ₓ ¬𝒻⋆ (β n))
             ＝⟨ 𝕓 ⟩
            𝒻 ⋆∙ j (β n) ∧ₓ (𝒻 ⋆∙ k (β n) ∧ₓ (¬𝒻⋆ (β n) ∧ₓ ¬𝒻⋆ (β n)))
             ＝⟨ 𝕔 ⟩
            𝒻 ⋆∙ j (β n) ∧ₓ (((𝒻 ⋆∙ k (β n)) ∧ₓ ¬𝒻⋆ (β n)) ∧ₓ ¬𝒻⋆ (β n))
             ＝⟨ 𝕕 ⟩
            𝒻 ⋆∙ j (β n) ∧ₓ ((¬𝒻⋆ (β n) ∧ₓ 𝒻 ⋆∙ (k (β n))) ∧ₓ ¬𝒻⋆ (β n))
             ＝⟨ 𝕖 ⟩
            𝒻 ⋆∙ j (β n) ∧ₓ (¬𝒻⋆ (β n) ∧ₓ ((𝒻 ⋆∙ k (β n)) ∧ₓ ¬𝒻⋆ (β n)))
             ＝⟨ 𝕗 ⟩
            (𝒻 ⋆∙ j (β n)  ∧ₓ ¬𝒻⋆ (β n)) ∧ₓ (𝒻 ⋆∙ k (β n) ∧ₓ ¬𝒻⋆ (β n))
             ∎)

    lhs₁ = ⁅ (𝒻 ⋆∙ j (β n)  ∧ₓ ¬𝒻⋆ (β n)) ∧ₓ (𝒻 ⋆∙ k (β n) ∧ₓ ¬𝒻⋆ (β n)) ∣ n ∶ Bₐ ⁆
    rhs₁ = ⁅ (𝒻 ⋆∙ j (β m)  ∧ₓ ¬𝒻⋆ (β m)) ∧ₓ (𝒻 ⋆∙ k (β n) ∧ₓ ¬𝒻⋆ (β n))
            ∣ (m , n) ∶ Bₐ × Bₐ ⁆

    † : cofinal-in (𝒪 X) lhs₁ rhs₁ holds
    † n = ∣ (n , n) , ≤-is-reflexive (poset-of (𝒪 X)) (lhs₁ [ n ]) ∣

    ‡ : cofinal-in (𝒪 X) rhs₁ lhs₁ holds
    ‡ (m , n) = ∥∥-rec ∃-is-prop ϡ ※
     where
      ϡ : (Σ o ꞉ Bₐ , β o ＝ β m ∨[ 𝒪 A ] β n)
        → ∃ o ꞉ Bₐ , (rhs₁ [ (m , n) ] ≤[ poset-of (𝒪 X) ] lhs₁ [ o ]) holds
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

        𝕒  = (𝒻 ⋆∙ j (β m) ∧ₓ ¬𝒻⋆ (β m)) ∧ₓ (𝒻 ⋆∙ k (β n) ∧ₓ ¬𝒻⋆ (β n))    ＝⟨ 𝕒₁ ⟩
             𝒻 ⋆∙ j (β m) ∧ₓ (¬𝒻⋆ (β m) ∧ₓ (𝒻 ⋆∙ k (β n) ∧ₓ ¬𝒻⋆ (β n)))    ＝⟨ 𝕒₂ ⟩
             𝒻 ⋆∙ j (β m) ∧ₓ ((¬𝒻⋆ (β m) ∧ₓ 𝒻 ⋆∙ k (β n)) ∧ₓ ¬𝒻⋆ (β n))    ＝⟨ 𝕒₃ ⟩
             𝒻 ⋆∙ j (β m) ∧ₓ (𝒻 ⋆∙ (k (β n)) ∧ₓ ¬𝒻⋆ (β m) ∧ₓ ¬𝒻⋆ (β n))    ＝⟨ 𝕒₄ ⟩
             𝒻 ⋆∙ j (β m) ∧ₓ (𝒻 ⋆∙ (k (β n)) ∧ₓ (¬𝒻⋆ (β m) ∧ₓ ¬𝒻⋆ (β n)))  ＝⟨ 𝕒₅ ⟩
             (𝒻 ⋆∙ j (β m) ∧ₓ 𝒻 ⋆∙ (k (β n))) ∧ₓ (¬𝒻⋆ (β m) ∧ₓ ¬𝒻⋆ (β n))  ＝⟨ 𝕒₆ ⟩
             (𝒻 ⋆∙ (j (β m) ∧[ 𝒪 A ] k (β n))) ∧ₓ (¬𝒻⋆ (β m) ∧ₓ ¬𝒻⋆ (β n)) ∎
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

        ♣ : ((¬𝒻⋆ (β m) ∧ₓ ¬𝒻⋆ (β n)) ≤[ poset-of (𝒪 X) ] ¬𝒻⋆ (β o)) holds
        ♣ = ¬𝒻⋆ (β m) ∧ₓ ¬𝒻⋆ (β n)                                  ＝⟨ refl ⟩ₚ
            ((𝒻 ⋆∙ β m) ==> 𝟎[ 𝒪 X ]) ∧ₓ ((𝒻 ⋆∙ β n) ==> 𝟎[ 𝒪 X ])  ＝⟨ 𝟏    ⟩ₚ
            ((𝒻 ⋆∙ (β m) ∨[ 𝒪 X ] (𝒻 ⋆∙ (β n))) ==> 𝟎[ 𝒪 X ])       ＝⟨ 𝟐    ⟩ₚ
            ((𝒻 ⋆∙ (β m ∨[ 𝒪 A ] β n)) ==> 𝟎[ 𝒪 X ])                ＝⟨ 𝟑    ⟩ₚ
            ¬𝒻⋆ (β o)                                               ■
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
         (𝒻 ⋆∙ j (β o) ∧ₓ 𝒻 ⋆∙ k (β o)) ∧ₓ ¬𝒻⋆ (β o)                ＝⟨ 𝟏 ⟩
         (𝒻 ⋆∙ j (β o) ∧ₓ 𝒻 ⋆∙ k (β o)) ∧ₓ (¬𝒻⋆ (β o) ∧ₓ ¬𝒻⋆ (β o)) ＝⟨ 𝟐 ⟩
         𝒻 ⋆∙ j (β o) ∧ₓ (𝒻 ⋆∙ k (β o) ∧ₓ (¬𝒻⋆ (β o) ∧ₓ ¬𝒻⋆ (β o))) ＝⟨ 𝟑 ⟩
         𝒻 ⋆∙ j (β o) ∧ₓ ((𝒻 ⋆∙ k (β o) ∧ₓ ¬𝒻⋆ (β o)) ∧ₓ ¬𝒻⋆ (β o)) ＝⟨ 𝟒 ⟩
         𝒻 ⋆∙ j (β o) ∧ₓ ((¬𝒻⋆ (β o) ∧ₓ 𝒻 ⋆∙ k (β o)) ∧ₓ ¬𝒻⋆ (β o)) ＝⟨ 𝟓 ⟩
         𝒻 ⋆∙ j (β o) ∧ₓ (¬𝒻⋆ (β o) ∧ₓ (𝒻 ⋆∙ k (β o) ∧ₓ ¬𝒻⋆ (β o))) ＝⟨ 𝟔 ⟩
         (𝒻 ⋆∙ j (β o) ∧ₓ ¬𝒻⋆ (β o)) ∧ₓ (𝒻 ⋆∙ k (β o) ∧ₓ ¬𝒻⋆ (β o)) ∎
          where
           𝟏 = ap
                (λ - → (𝒻 ⋆∙ j (β o) ∧ₓ 𝒻 ⋆∙ k (β o)) ∧ₓ -)
                (∧[ 𝒪 X ]-is-idempotent (¬𝒻⋆ (β o)))
           𝟐 = ∧[ 𝒪 X ]-is-associative
                (𝒻 ⋆∙ j (β o))
                (𝒻 ⋆∙ k (β o))
                (¬𝒻⋆ (β o) ∧ₓ ¬𝒻⋆ (β o)) ⁻¹
           𝟑 = ap
                (λ - → 𝒻 ⋆∙ (j (β o)) ∧ₓ -)
                (∧[ 𝒪 X ]-is-associative (𝒻 ⋆∙ k (β o)) (¬𝒻⋆ (β  o)) (¬𝒻⋆ (β o)))
           𝟒 = ap
                (λ - → 𝒻 ⋆∙ j (β o) ∧ₓ (- ∧ₓ ¬𝒻⋆ (β o)))
                (∧[ 𝒪 X ]-is-commutative (𝒻 ⋆∙ k (β o)) (¬𝒻⋆ (β o)))
           𝟓 = ap
                (λ - → 𝒻 ⋆∙ j (β o) ∧ₓ -)
                (∧[ 𝒪 X ]-is-associative (¬𝒻⋆ (β o)) (𝒻 ⋆∙ k (β o)) (¬𝒻⋆ (β o)) ⁻¹)
           𝟔 = ∧[ 𝒪 X ]-is-associative
                (𝒻 ⋆∙ j (β o))
                (¬𝒻⋆ (β o))
                (𝒻 ⋆∙ k (β o) ∧ₓ ¬𝒻⋆ (β o))

        open PosetReasoning (poset-of (𝒪 X))

        ϟ = (𝒻 ⋆∙ j (β m) ∧ₓ ¬𝒻⋆ (β m)) ∧ₓ (𝒻 ⋆∙ k (β n) ∧ₓ ¬𝒻⋆ (β n))    ＝⟨ 𝕒 ⟩ₚ
            (𝒻 ⋆∙ (j (β m) ∧[ 𝒪 A ] k (β n))) ∧ₓ (¬𝒻⋆ (β m) ∧ₓ ¬𝒻⋆ (β n)) ≤⟨ 𝕓  ⟩
            𝒻 ⋆∙ (j (β o) ∧[ 𝒪 A ] k (β o)) ∧ₓ (¬𝒻⋆ (β m) ∧ₓ ¬𝒻⋆ (β n))   ≤⟨ 𝕔  ⟩
            𝒻 ⋆∙ (j (β o) ∧[ 𝒪 A ] k (β o)) ∧ₓ ¬𝒻⋆ (β o)                  ＝⟨ 𝕕 ⟩ₚ
            (𝒻 ⋆∙ j (β o) ∧ₓ 𝒻 ⋆∙ k (β o)) ∧ₓ ¬𝒻⋆ (β o)                   ＝⟨ 𝕖 ⟩ₚ
            (𝒻 ⋆∙ j (β o) ∧ₓ ¬𝒻⋆ (β o)) ∧ₓ (𝒻 ⋆∙ k (β o) ∧ₓ ¬𝒻⋆ (β o))    ■

      ※ : ∃ o ꞉ Bₐ , β o ＝ β m ∨[ 𝒪 A ] β n
      ※ = ∥∥-rec
           ∃-is-prop
           (λ { (o , p) → ∣ o , (p ⁻¹) ∣ })
           (compact-opens-are-basic-in-compact-frames
             (𝒪 A)
             (Bₐ , β)
             (pr₁ (pr₂ σᴰ))
             (spectral-implies-compact (𝒪 A) ∣ σᴰ ∣)
             (β m ∨[ 𝒪 A ] β n)
             (compacts-are-closed-under-joins
               (𝒪 A)
               (β m)
               (β n)
               (pr₂ (βₖ m))
               (pr₂ (βₖ n))))

    Ⅳ = bicofinal-implies-same-join (𝒪 X) lhs₁ rhs₁ † ‡

    Ⅴ = distributivity+
         (𝒪 X)
         ⁅ (𝒻 ⋆∙ j (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆
         ⁅ (𝒻 ⋆∙ k (β n)) ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ n ∶ Bₐ ⁆ ⁻¹
    Ⅵ = ap₂
         (λ x y → x ∧[ 𝒪 X ] y)
         (f⁻⁺₂-equiv-f⁻⁺₁ 𝒿 ⁻¹)
         (f⁻⁺₂-equiv-f⁻⁺₁ 𝓀 ⁻¹)

\end{code}

We now proceed to the join preservation proof which requires quite a few
auxiliary definitions and lemmas.

\begin{code}

 open ClosedNucleus X (stone-locales-are-spectral (𝒪 X) (𝕜 , ∣ 𝕫ᴰ ∣))
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
  𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V₁) ∧[ 𝒪 A ] 𝒻₊ (U ∨[ 𝒪 X ] 𝒻 ⋆∙ V₂)     ＝⟨ refl ⟩
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
         (spectral-maps-are-perfect 𝒻 ∣ σᴰ ∣ μ)
         (∨-is-scott-continuous (𝒪 X) U)
         where
          open PerfectMaps X A A-has-basis


    ‡ : is-scott-continuous (𝒪 A) (𝒪 X) (𝒻 ⋆∙_) holds
    ‡ = join-preserving-implies-scott-continuous
         (𝒪 A)
         (𝒪 X)
         (𝒻 ⋆∙_)
         (frame-homomorphisms-preserve-all-joins (𝒪 A) (𝒪 X) 𝒻)

\end{code}

\begin{code}

 f⁻₊ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 Patchₛ-A ⟩
 f⁻₊ U = closed-image U ,  closed-image-is-nucleus U  , closed-image-is-sc U

\end{code}

\begin{code}

 f⁻₊-is-monotone : is-monotonic (poset-of (𝒪 X)) (poset-of (𝒪 Patchₛ-A)) f⁻₊ holds
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
   open LemmasAboutHeytingComplementation X X-has-basis

   ϑ₁ : (f⁻⁺ 𝒿 ≤ₓ U ⇒ 𝒿 ≤[ poset-of (𝒪 Patchₛ-A) ] (f⁻₊ U)) holds
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
       ※ = negation-∨-lemma₂ κ ϟ

       ψ : (𝒻 ⋆∙ j (β n) ≤[ poset-of (𝒪 X) ] (U ∨[ 𝒪 X ] 𝒻 ⋆∙ β n)) holds
       ψ = 𝒻 ⋆∙ j (β n)          ≤⟨ ※ ⟩
           𝒻 ⋆∙ (β n) ∨[ 𝒪 X ] U ＝⟨ ∨[ 𝒪 X ]-is-commutative (𝒻 ⋆∙ β n) U ⟩ₚ
           U ∨[ 𝒪 X ] 𝒻 ⋆∙ (β n) ■

   S =
    ⁅ (𝒻 ⋆∙ β m) ∧ₓ ¬𝒻⋆ (β n)
     ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝔏 𝒿 m n holds ⁆

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
            (U ∨[ 𝒪 X ] 𝒻 ⋆∙ T)) holds
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
       goal = negation-∨-lemma₁ κ ϑ

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
            → is-complement-of (𝒪 X) (f⁻₀ ¬‘ βₖ n ’) (f⁻₀ ‘ β n ’)
 easy-lemma 𝒻⁻₀ n =
  frame-homomorphisms-preserve-complements (𝒪 Patchₛ-A) (𝒪 X) 𝒻⁻₀ †
   where
    open PatchComplementation A σᴰ

    ‡ : is-boolean-complement-of (𝒪 Patchₛ-A) ¬‘ βₖ n ’ ‘ β n ’ holds
    ‡ = open-complements-closed (β n) (pr₂ (βₖ n))

    † : is-complement-of (𝒪 Patchₛ-A) ‘ β n ’ ¬‘ βₖ n ’
    † = complementation-is-symmetric (𝒪 Patchₛ-A) ¬‘ βₖ n ’ ‘ β n ’ ‡

\end{code}

A corollary of the "easy lemma" is that any continuous map `𝒻⁻₀` from `X` into
`Patch-A` that makes the diagram commute also satisfies

```
    𝒻⁻₀⁺ ¬‘ C ’ = ¬𝒻⁺ C ≡ 𝒻⁺ C ==> 𝟎
```

We call this lemma `commutes-with-open-nucleus`.

\begin{code}

 commutes-with-open-nucleus : (𝒻⁻₀@(f⁻₀ , _) : X ─c→ Patchₛ-A)
                            → ((n : Bₐ) → 𝒻 ⋆∙ (β n) ＝ f⁻₀ ‘ β n ’)
                            → (n : Bₐ) →  ¬𝒻⋆ (β n) ＝ f⁻₀ ¬‘ βₖ n ’
 commutes-with-open-nucleus 𝒻⁻₀@(f⁻₀ , _) ϑ n =
  complements-are-unique (𝒪 X) (𝒻 ⋆∙ (β n)) (¬𝒻⋆ (β n)) (f⁻₀ ¬‘ βₖ n ’) φ ψ
   where
    open LemmasAboutHeytingComplementation X X-has-basis

    ν : is-clopen (𝒪 X) (𝒻 ⋆∙ β n) holds
    ν = compacts-are-clopen-in-zero-dimensional-locales
         (𝒪 X)
         ∣ 𝕫ᴰ ∣
         (𝒻 ⋆∙ (β n))
         (μ (β n) (pr₂ (βₖ n)))

    C = pr₁ ν

    C-complements-𝒻⋆βn : is-complement-of (𝒪 X) C (𝒻 ⋆∙ (β n))
    C-complements-𝒻⋆βn = pr₂ ν

    φ : is-complement-of (𝒪 X) (¬𝒻⋆ (β n)) (𝒻 ⋆∙ β n)
    φ = transport
         (λ - → is-complement-of (𝒪 X) - (𝒻 ⋆∙ β n))
         (complement-is-heyting-complement (𝒻 ⋆∙ β n) C C-complements-𝒻⋆βn)
         C-complements-𝒻⋆βn

    ψ : is-complement-of (𝒪 X) (f⁻₀ ¬‘ βₖ n ’) (𝒻 ⋆∙ β n)
    ψ = transport
         (λ - → is-complement-of (𝒪 X) (f⁻₀ ¬‘ βₖ n ’) -)
         (ϑ n ⁻¹)
         (easy-lemma 𝒻⁻₀ n)

\end{code}

Using `commutes-with-open-nucleus` and the `easy-lemma`, it is not hard to
prove that `𝒻⁻` makes the diagram commute.

\begin{code}

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
                ⁅ 𝒻 ⋆∙ β m ∧[ 𝒪 X ] ¬𝒻⋆ (β n) ∣ (m , n , p) ∶ below ‘ U ’ ⁆
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
       → ((𝒻 ⋆∙ (U ∨[ 𝒪 A ] β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ≤ₓ 𝒻 ⋆∙ U) holds
     ϟ n =
      𝒻 ⋆∙ (U ∨[ 𝒪 A ] β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)                             ＝⟨ 𝟏 ⟩ₚ
      (𝒻 ⋆∙ U ∨[ 𝒪 X ] 𝒻 ⋆∙ β n) ∧[ 𝒪 X ] ((𝒻 ⋆∙ (β n)) ==> 𝟎[ 𝒪 X ])      ＝⟨ 𝟐 ⟩ₚ
      (𝒻 ⋆∙ U ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ∨[ 𝒪 X ] (𝒻 ⋆∙ (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n)) ≤⟨  𝟑 ⟩
      (𝒻 ⋆∙ U) ∨[ 𝒪 X ] (𝒻 ⋆∙ (β n) ∧[ 𝒪 X ] ¬𝒻⋆ (β n))                    ≤⟨  𝟒 ⟩
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

\end{code}

We now package up the function `f⁻` with the proof that it's a continuous map.

\begin{code}

 𝒻⁻⁺ : X ─c→ Patchₛ-A
 𝒻⁻⁺ = f⁻⁺ , 𝒻⁻-α , 𝒻⁻-β , 𝒻⁻-γ

\end{code}

\section{Uniqueness}

\begin{code}

 𝒻⁻-is-unique-ext : (𝒻⁻′ : X ─c→ Patchₛ-A)
                  → (((U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U  ＝ 𝒻⁻′ .pr₁ ‘ U ’) )
                  → (𝒿 : ⟨ 𝒪 Patchₛ-A ⟩) → f⁻⁺ 𝒿 ＝ 𝒻⁻′ .pr₁ 𝒿
 𝒻⁻-is-unique-ext 𝒻⁻₀@(f⁻₀ , _) ϑ 𝒿 =
  f⁻⁺ 𝒿                                                                      ＝⟨ Ⅰ ⟩
  f⁻⁺ (⋁ₙ ⁅ (𝔠 k) ⋏ (𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆)                 ＝⟨ Ⅱ ⟩
  ⋁[ 𝒪 X ] ⁅ f⁻⁺ (𝔠 k ⋏ 𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆               ＝⟨ Ⅲ ⟩
  ⋁[ 𝒪 X ] ⁅ f⁻⁺ (𝔠 k) ∧ₓ f⁻⁺ (𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆        ＝⟨ Ⅳ ⟩
  ⋁[ 𝒪 X ] ⁅ f⁻⁺ (𝔠 k) ∧ₓ ¬𝒻⋆ (β l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆        ＝⟨ Ⅴ ⟩
  ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (β k) ∧ₓ ¬𝒻⋆ (β l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆       ＝⟨ Ⅵ ⟩
  ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (β k) ∧ₓ f⁻₀ (𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆       ＝⟨ Ⅶ ⟩
  ⋁[ 𝒪 X ] ⁅ f⁻₀ (𝔠 k) ∧ₓ f⁻₀ (𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆        ＝⟨ Ⅷ ⟩
  ⋁[ 𝒪 X ] ⁅ f⁻₀ (𝔠 k ∧[ 𝒪 Patchₛ-A ] 𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆ ＝⟨ Ⅸ ⟩
  f⁻₀ (⋁ₙ ⁅ 𝔠 k ∧[ 𝒪 Patchₛ-A ] 𝔬 l ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆)       ＝⟨ Ⅹ ⟩
  f⁻₀ 𝒿                                                                      ∎
   where
    open BasisOfPatch A σᴰ
    open PatchConstruction A ∣ σᴰ ∣ using (⋁ₙ; _⋏_)

    ν : 𝒿 ＝ ⋁[ 𝒪 Patchₛ-A ] ⁅ 𝔠 k ∧[ 𝒪 Patchₛ-A ] 𝔬 l ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆
    ν = main-covering-lemma 𝒿

    Ⅰ = ap f⁻⁺ ν
    Ⅱ = ⋁[ 𝒪 X ]-unique
         ⁅ f⁻⁺ (𝔠 k ∧[ 𝒪 Patchₛ-A ] 𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆
         (f⁻⁺ (⋁[ 𝒪 Patchₛ-A ] ⁅ 𝔠 k ∧[ 𝒪 Patchₛ-A ] 𝔬 l ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆))
         (𝒻⁻-γ ⁅ 𝔠 k ∧[ 𝒪 Patchₛ-A ] 𝔬 l ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆)
    Ⅲ = ap
         (λ - → ⋁[ 𝒪 X ] (basic-below 𝒿 , -))
         (dfunext fe (λ { ((k , l) , p) → 𝒻⁻-β (𝔠 k) (𝔬 l) }))

    Ⅳ : ⋁[ 𝒪 X ] ⁅ f⁻⁺ (𝔠 k) ∧[ 𝒪 X ] f⁻⁺ (𝔬 l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆ ＝ ⋁[ 𝒪 X ] ⁅ f⁻⁺ (𝔠 k) ∧[ 𝒪 X ] ¬𝒻⋆ (β l) ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆
    Ⅳ = ap
         (λ - → ⋁[ 𝒪 X ] (basic-below 𝒿 , -))
         (dfunext fe (λ { ((k , l) , p) → ap (λ - → (f⁻⁺ (𝔠 k)) ∧[ 𝒪 X ] -) (commutes-with-open-nucleus 𝒻⁻⁺ (λ n → 𝒻⁻-makes-the-diagram-commute (β n)) l ⁻¹) }))
    Ⅴ = ap (λ - → ⋁[ 𝒪 X ] (basic-below 𝒿 , -)) ((dfunext fe (λ { ((k , l) , p) → ap (λ - → - ∧[ 𝒪 X ] ¬𝒻⋆ (β l)) (𝒻⁻-makes-the-diagram-commute (β k) ⁻¹) })))
    Ⅵ = ap (λ - → ⋁[ 𝒪 X ] (basic-below 𝒿 , -)) (dfunext fe λ { ((k , l) , p) → ap (λ - → 𝒻 ⋆∙ (β k) ∧[ 𝒪 X ] -) (commutes-with-open-nucleus 𝒻⁻₀ (ϑ ∘ β) l) })
    Ⅶ = ap (λ - → ⋁[ 𝒪 X ] (basic-below 𝒿 , -)) (dfunext fe λ { ((k , l) , p) → ap (λ - → - ∧[ 𝒪 X ] f⁻₀ (𝔬 l)) (ϑ (β k)) })
    Ⅷ = ap (λ - → ⋁[ 𝒪 X ] (basic-below 𝒿 , -)) (dfunext fe λ { ((k , l) , p) → frame-homomorphisms-preserve-meets (𝒪 Patchₛ-A) (𝒪 X) 𝒻⁻₀ (𝔠 k) (𝔬 l) ⁻¹ } )
    Ⅸ = frame-homomorphisms-preserve-all-joins (𝒪 Patchₛ-A) (𝒪 X) 𝒻⁻₀ ⁅ 𝔠 k ∧[ 𝒪 Patchₛ-A ] 𝔬 l ∣ ((k , l) , _) ∶ basic-below 𝒿 ⁆ ⁻¹
    Ⅹ = ap f⁻₀ ν ⁻¹

 𝒻⁻-is-unique : is-central
                 (Σ 𝒻⁻₀ ꞉ (X ─c→ Patchₛ-A) ,
                  ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻₀ .pr₁ ‘ x ’))
                 ((f⁻⁺ , 𝒻⁻-α , 𝒻⁻-β , 𝒻⁻-γ) , 𝒻⁻-makes-the-diagram-commute)
 𝒻⁻-is-unique (𝒻⁻₀@(_ , _ , _ , 𝒻⁻₀-γ) , ϑ) = to-subtype-＝ ※ (to-subtype-＝ γ (dfunext fe †))
  where
   f⁻₀ = pr₁ 𝒻⁻₀

   ※ : (𝒻⁻₀ : X ─c→ Patchₛ-A)
     → is-prop ((U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U  ＝ 𝒻⁻₀ .pr₁ ‘ U ’)
   ※ 𝒻⁻₀ = Π-is-prop fe λ _ → carrier-of-[ poset-of (𝒪 X) ]-is-set

   γ : (ℊ⁻ : ⟨ 𝒪 Patchₛ-A ⟩ → ⟨ 𝒪 X ⟩)
      → is-prop (is-a-frame-homomorphism (𝒪 Patchₛ-A) (𝒪 X) ℊ⁻ holds)
   γ ℊ⁻ = holds-is-prop (is-a-frame-homomorphism (𝒪 Patchₛ-A) (𝒪 X) ℊ⁻)

   open LemmasAboutHeytingComplementation X X-has-basis

   ψ₂ : (n : Bₐ) → is-complement-of (𝒪 X) (f⁻₀ ¬‘ βₖ n ’) (𝒻 ⋆∙ (β n))
   ψ₂ n = transport
           (λ - → is-complement-of (𝒪 X) (f⁻₀ ¬‘ βₖ n ’) -)
           (ϑ (β n) ⁻¹)
           (easy-lemma 𝒻⁻₀ n)

   ψ : (n : Bₐ) → ¬𝒻⋆ (β n) ＝ f⁻₀ ¬‘ βₖ n ’
   ψ n =
    complements-are-unique (𝒪 X) (𝒻 ⋆∙ (β n)) (¬𝒻⋆ (β n)) (f⁻₀ ¬‘ βₖ n ’) ψ₁ (ψ₂ n)
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

   open BasisOfPatch A σᴰ

   † : (𝒿 : ⟨ 𝒪 Patchₛ-A ⟩) → f⁻⁺ 𝒿 ＝ f⁻₀ 𝒿
   † = 𝒻⁻-is-unique-ext 𝒻⁻₀ ϑ

 proof-of-ump : ∃! 𝒻⁻ ꞉ (X ─c→ Patchₛ-A) , ((U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U  ＝ 𝒻⁻ .pr₁ ‘ U ’)
 proof-of-ump =
  ((f⁻⁺ , 𝒻⁻-α , 𝒻⁻-β , 𝒻⁻-γ) , 𝒻⁻-makes-the-diagram-commute) , 𝒻⁻-is-unique

ump-of-patch : {𝓤 : Universe}
             → (A : Locale (𝓤 ⁺) 𝓤 𝓤)
             → (σ : is-spectral (𝒪 A) holds)
             → (X : Locale (𝓤 ⁺) 𝓤 𝓤)
             → is-stone (𝒪 X) holds
             → (𝒻 : X ─c→ A)
             → is-spectral-map (𝒪 A) (𝒪 X) 𝒻 holds
             → let
                open PatchConstruction A σ renaming (Patch to Patch-A)
                open ClosedNucleus A σ
                open OpenNucleus A σ
               in
                ∃! 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻ .pr₁ ‘ x ’)
ump-of-patch {𝓤} A σ X 𝕤 𝒻 μ = ∥∥-rec₂ (being-singleton-is-prop fe) γ σ (pr₂ 𝕤)
 where
  open PatchConstruction A σ renaming (Patch to Patch-A)
  open ClosedNucleus A σ
  open OpenNucleus A σ

  γ : spectralᴰ (𝒪 A)
    → zero-dimensionalᴰ (𝒪 X)
    → ∃! 𝒻⁻ ꞉ (X ─c→ Patch-A) , ((x : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ x  ＝ 𝒻⁻ .pr₁ ‘ x ’)
  γ σᴰ 𝕫ᴰ = (𝒻⁻₀ , †) , ‡
   where
    open UniversalProperty A X σᴰ 𝕫ᴰ (pr₁ 𝕤) 𝒻 μ
    open SmallPatchConstruction A σᴰ renaming (SmallPatch to Patchₛ-A)

    f⁻₀ : ⟨ 𝒪 Patch-A ⟩ → ⟨ 𝒪 X ⟩
    f⁻₀ 𝒿 = f⁻⁺ 𝒿

    𝒻⁻₀ : X ─c→ Patch-A
    𝒻⁻₀ = f⁻₀ , 𝒻⁻-α , 𝒻⁻-β , 𝒻⁻-γ

    † : (U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U ＝ 𝒻⁻₀ .pr₁ ‘ U ’
    † = 𝒻⁻-makes-the-diagram-commute

    ‡ : is-central
         ((Σ 𝒻⁻₀ ꞉ (X ─c→ Patch-A) , ((U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U  ＝ 𝒻⁻₀ .pr₁ ‘ U ’)))
         (𝒻⁻₀ , 𝒻⁻-makes-the-diagram-commute)
    ‡ (𝒻⁻₁@(_ , α₁ , β₁ , γ₁) , p) = to-subtype-＝ ♣ (to-subtype-＝ ♠ (dfunext fe ϟ))
     where
      open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
      open PosetReasoning (poset-of (𝒪 X))

      𝒻⁻₁′ : X ─c→ Patchₛ-A
      𝒻⁻₁′ = (𝒻⁻₁ .pr₁) , α₁ , β₁ , γ₁′
       where
        γ₁′ : (S : Fam 𝓤 ⟨ 𝒪 Patchₛ-A ⟩)
            → (𝒻⁻₁ .pr₁ (join-of (𝒪 Patchₛ-A) S) is-lub-of ⁅ 𝒻⁻₁ .pr₁ x ∣ x ε S ⁆) holds
        γ₁′ S = foo , bar
         where
          foo : ((𝒻⁻₁ .pr₁ (join-of (𝒪 Patchₛ-A) S)) is-an-upper-bound-of ⁅ 𝒻⁻₁ .pr₁ x ∣ x ε S ⁆) holds
          foo i = 𝒻⁻₁ .pr₁ (S [ i ]) ≤⟨ meet-preserving-implies-monotone (𝒪 Patchₛ-A) (𝒪 X) (𝒻⁻₁ .pr₁) β₁ (_ , _) (⋁[ 𝒪 Patchₛ-A ]-upper S i)  ⟩ 𝒻⁻₁ .pr₁ (join-of (𝒪 Patchₛ-A) S) ■

          eq : ⋁[ 𝒪 Patchₛ-A ] S ＝ ⋁[ 𝒪 Patch-A ] S
          eq = ≤-is-antisymmetric (poset-of (𝒪 Patchₛ-A)) eq₁ eq₂
           where
            eq₁ : rel-syntax (poset-of (𝒪 Patchₛ-A)) (join-of (𝒪 Patchₛ-A) S) (join-of (𝒪 Patch-A) S) holds
            eq₁ i = ⋁[ 𝒪 Patchₛ-A ]-least S (((join-of (𝒪 Patch-A) S)) , ♢) i
             where
              ♢ : (rel-syntax (poset-of (𝒪 Patchₛ-A)) Joins.is-an-upper-bound-of
                     join-of (𝒪 Patch-A) S)
                    S
                    holds
              ♢ i = ≼-implies-≼ᵏ (S [ i ]) (join-of (𝒪 Patch-A) S) (⋁[ 𝒪 Patch-A ]-upper S i)

            eq₂ : rel-syntax (poset-of (𝒪 Patchₛ-A)) (join-of (𝒪 Patch-A) S) (join-of (𝒪 Patchₛ-A) S) holds
            eq₂ i = ⋁[ 𝒪 Patch-A ]-least S ((join-of (𝒪 Patchₛ-A) S) , ♢) (β i)
             where
              ♢ : (rel-syntax (poset-of (𝒪 Patch-A)) Joins.is-an-upper-bound-of
                     join-of (𝒪 Patchₛ-A) S)
                    S
                    holds
              ♢ i = ≼ᵏ-implies-≼ (S [ i ]) (join-of (𝒪 Patchₛ-A) S) (⋁[ 𝒪 Patchₛ-A ]-upper S i)

          bar : ((U , _) : upper-bound ⁅ 𝒻⁻₁ .pr₁ x ∣ x ε S ⁆) → (𝒻⁻₁ .pr₁ (⋁[ 𝒪 Patchₛ-A ] S) ≤[ poset-of (𝒪 X) ] U) holds
          bar (U , p) = 𝒻⁻₁ .pr₁ (⋁[ 𝒪 Patchₛ-A ] S) ＝⟨ ap (𝒻⁻₁ .pr₁) eq ⟩ₚ 𝒻⁻₁ .pr₁ (⋁[ 𝒪 Patch-A ] S) ≤⟨ pr₂ (γ₁ S) (U , p) ⟩ U ■

      ♣ : (𝒻⁻₂ : X ─c→ Patch-A)
        → is-prop ((U : ⟨ 𝒪 A ⟩) → 𝒻 .pr₁ U ＝ 𝒻⁻₂ .pr₁ ‘ U ’)
      ♣ 𝒻⁻₂ = Π-is-prop fe (λ _ → carrier-of-[ poset-of (𝒪 X) ]-is-set)

      ♠ : (𝒻⁻₂ : ⟨ 𝒪 Patch-A ⟩ → ⟨ 𝒪 X ⟩)
        → is-prop (is-a-frame-homomorphism (𝒪 Patch-A) (𝒪 X) 𝒻⁻₂ holds)
      ♠ = holds-is-prop ∘ is-a-frame-homomorphism (𝒪 Patch-A) (𝒪 X)

      ϟ : (𝒿 : ⟨ 𝒪 Patch-A ⟩) → f⁻₀ 𝒿 ＝ 𝒻⁻₁ .pr₁ 𝒿
      ϟ 𝒿 = f⁻₀ 𝒿 ＝⟨ refl ⟩ f⁻⁺ 𝒿 ＝⟨ 𝒻⁻-is-unique-ext 𝒻⁻₁′ p 𝒿 ⟩ 𝒻⁻₁ .pr₁ 𝒿 ∎

\end{code}

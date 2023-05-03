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
     open SmallPatchConstruction A σᴰ using (𝟎-is-id; ≼-implies-≼ᵏ; ≼ᵏ-implies-≼; _≼ᵏ_) renaming (SmallPatch to Patchₛ-A)
     open ContinuousMapNotation X A

     X-has-basis : has-basis (𝒪 X) holds
     X-has-basis = ∣ pr₁ 𝕫ᴰ , pr₁ (pr₁ (pr₂ 𝕫ᴰ)) ∣

     A-has-basis : has-basis (𝒪 A) holds
     A-has-basis = spectral-frames-have-bases (𝒪 A) σ

     open HeytingImplicationConstruction X X-has-basis
     open HeytingImplicationConstruction A A-has-basis
      using ()
      renaming (_==>_ to _==>ₐ_; H₈ to H₈ₐ;
                heyting-implication-identity to heyting-implication-identityₐ;
                ==>-right-monotone to ==>ₐ-right-monotone)

     Bₐ : 𝓤  ̇
     Bₐ = pr₁ (pr₁ σᴰ)

     β : Bₐ → ⟨ 𝒪 A ⟩
     β = pr₂ (pr₁ σᴰ)

     β-is-basis-for-A : is-basis-for (𝒪 A) (Bₐ , β)
     β-is-basis-for-A U = {!pr₁ (pr₁ (pr₂ σᴰ)) U!} , {!!}

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

     f⁻⋆₂ : ⟨ 𝒪 Patchₛ-A ⟩ → ⟨ 𝒪 X ⟩
     f⁻⋆₂ 𝒿@(j , _) =
      ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] ¬𝒻⋆ n ∣ n ∶ Bₐ ⁆

     f⁻⋆₂-equiv-f⁻⋆₁ : (𝒿 : ⟨ 𝒪 Patchₛ-A ⟩) → f⁻⋆ 𝒿 ＝ f⁻⋆₂ 𝒿
     f⁻⋆₂-equiv-f⁻⋆₁ 𝒿@(j , _) = ≤-is-antisymmetric (poset-of (𝒪 X)) †′ ‡
      where
       S : Fam 𝓤 ⟨ 𝒪 X ⟩
       S = ⁅ (𝒻 ⋆∙ β m) ∧[ 𝒪 X ] ¬𝒻⋆ n ∣ (m , n , p) ∶ Σ m ꞉ Bₐ , Σ n ꞉ Bₐ , 𝕃 𝒿 m n holds ⁆

       T : Fam 𝓤 ⟨ 𝒪 X ⟩
       T = ⁅ 𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] ¬𝒻⋆ n ∣ n ∶ Bₐ ⁆

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

         ※ : ((𝒻 ⋆∙ β m ∧[ 𝒪 X ] ¬𝒻⋆ n)
               ≤[ poset-of (𝒪 X) ]
              (𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] (¬𝒻⋆ n))) holds
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
           𝒻 ⋆∙ j (β n) ∧[ 𝒪 X ] ¬𝒻⋆ n                          ＝⟨ Ⅰ  ⟩ₚ
           𝒻 ⋆∙ (⋁[ 𝒪 A ] ⁅ β i ∣ i ε 𝒥 ⁆) ∧[ 𝒪 X ] ¬𝒻⋆ n       ＝⟨ Ⅱ  ⟩ₚ
           (⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (β i) ∣ i ε 𝒥 ⁆) ∧[ 𝒪 X ] ¬𝒻⋆ n     ＝⟨ Ⅲ  ⟩ₚ
           ⋁[ 𝒪 X ] ⁅ 𝒻 ⋆∙ (β i) ∧[ 𝒪 X ] ¬𝒻⋆ n ∣ i ε 𝒥 ⁆       ≤⟨ Ⅳ   ⟩
           ⋁[ 𝒪 X ] S                                           ■
          where
           𝒥 = covering-index-family (𝒪 A) (Bₐ , β) β-is-basis-for-A (j (β n))

           ※ : ((⋁[ 𝒪 X ] S)
                 is-an-upper-bound-of
                ⁅ 𝒻 ⋆∙ (β i) ∧[ 𝒪 X ] ¬𝒻⋆ n ∣ i ε 𝒥 ⁆) holds
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
                            𝕒 = ⋁[ 𝒪 A ]-upper (⁅ β i ∣ i ε 𝒥 ⁆) (𝒥 [ i ])
                            𝕓 = covers (𝒪 A) ⁅ β i ∣ i ε 𝒥 ⁆ β-is-basis-for-A (j (β n)) ⁻¹

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
                (λ - → 𝒻 ⋆∙ - ∧[ 𝒪 X ] ¬𝒻⋆ n)
                (covers (𝒪 A) (Bₐ , β) β-is-basis-for-A (j (β n)))
           Ⅱ = ap
                (λ - → - ∧[ 𝒪 X ] ¬𝒻⋆ n)
                (frame-homomorphisms-preserve-all-joins
                  (𝒪 A)
                  (𝒪 X)
                  𝒻
                  ⁅ β i ∣ i ε 𝒥 ⁆)
           Ⅲ = distributivity′-right (𝒪 X) (¬𝒻⋆ n) ⁅ 𝒻 ⋆∙ (β i) ∣ i ε 𝒥 ⁆
           Ⅳ = ⋁[ 𝒪 X ]-least
                ⁅ 𝒻 ⋆∙ (β i) ∧[ 𝒪 X ] ¬𝒻⋆ n ∣ i ε 𝒥 ⁆
                ((⋁[ 𝒪 X ] S) , ※)

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

     open AdjointFunctorTheorem X Patchₛ-A Patchₛ-A-has-basis hiding (f₊-is-right-adjoint-of-f⁺)
     open AdjointFunctorTheorem Patchₛ-A X X-has-basis
      using ()
      renaming (adjunction-inequality-forward to adjunction-inequality-forward₀)
     open AdjointFunctorTheorem X A A-has-basis
      using (f₊-is-right-adjoint-of-f⁺)
      renaming (right-adjoint-of to right-adjoint-ofₓ;
                f₊-preserves-binary-meets to f₊-preserves-binary-meetsₓ;
                adjunction-inequality-forward to adjunction-inequality-forwardₓ)
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

     open ClosedNucleus X (stone-locales-are-spectral (𝒪 X) 𝕤)
      using ()
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

     open PerfectMaps X A A-has-basis

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

        ‡ : is-scott-continuous (𝒪 A) (𝒪 X) (𝒻 ⋆∙_) holds
        ‡ = join-preserving-implies-scott-continuous
             (𝒪 A)
             (𝒪 X)
             (𝒻 ⋆∙_)
             (frame-homomorphisms-preserve-all-joins (𝒪 A) (𝒪 X) 𝒻)

     f⁻⋆-preserves-joins : is-join-preserving (𝒪 Patchₛ-A) (𝒪 X) f⁻⋆ holds
     f⁻⋆-preserves-joins = aft-forward 𝒻⁻⋆ₘ †
      where
       f⁻₊ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 Patchₛ-A ⟩
       f⁻₊ U = closed-image U , closed-image-is-nucleus U , closed-image-is-sc U

       f⁻*-is-monotone : is-monotonic
                          (poset-of (𝒪 X))
                          (poset-of (𝒪 Patchₛ-A))
                          f⁻₊
                         holds
       f⁻*-is-monotone U V p = {!!}

       f⁻₊ₘ : poset-of (𝒪 X) ─m→ poset-of (𝒪 Patchₛ-A)
       f⁻₊ₘ = f⁻₊ , f⁻*-is-monotone

       open IgorsLemma X A A-has-basis

       f⁻₊-is-right-adjoint-of-f⁻⁺ : (𝒻⁻⋆ₘ ⊣ f⁻₊ₘ) holds
       f⁻₊-is-right-adjoint-of-f⁻⁺ 𝒿@(j , _) U = ϑ₁ , ϑ₂
        where
         ϑ₁ : (f⁻⋆ 𝒿 ≤[ poset-of (𝒪 X) ] U) holds
            → (𝒿 ≤[ poset-of (𝒪 Patchₛ-A) ] (f⁻₊ U)) holds
         ϑ₁ φ i = adjunction-inequality-forwardₓ 𝒻 _ _ ψ
          where
           ψ : (𝒻 ⋆∙ j (β i) ≤[ poset-of (𝒪 X) ] (U ∨[ 𝒪 X ] 𝒻 ⋆∙ β i)) holds
           ψ = igors-lemma-⇐ 𝒻 (j (β i)) (β i) U χ
            where
             χ : (T : ⟨ 𝒪 A ⟩)
               → ((𝒻 ⋆∙ (j (β i) ∨[ 𝒪 A ] T) ∧[ 𝒪 X ] (𝒻 ⋆∙ (β i ==>ₐ T)))
                   ≤[ poset-of (𝒪 X) ]
                  (U ∨[ 𝒪 X ] 𝒻 ⋆∙ T)) holds
             χ = {!!}

         ϑ₂ : (𝒿 ≤[ poset-of (𝒪 Patchₛ-A) ] (f⁻₊ U)) holds
            → (f⁻⋆ 𝒿 ≤[ poset-of (𝒪 X) ] U) holds
         ϑ₂ = {!!}

       † : has-right-adjoint 𝒻⁻⋆ₘ
       † = f⁻₊ₘ , f⁻₊-is-right-adjoint-of-f⁻⁺

\end{code}

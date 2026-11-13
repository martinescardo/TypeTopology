Ayberk Tosun, 2023.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan hiding (𝟚)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.SubtypeClassifier

module Locales.HeytingComplementation (pt : propositional-truncations-exist)
                                      (fe : Fun-Ext)
                                      (sr : Set-Replacement pt) where

open import Locales.Frame              pt fe
open import Locales.HeytingImplication pt fe
open import Locales.Complements        pt fe
open import Locales.Clopen             pt fe sr

open import UF.Logic
open AllCombinators pt fe

open Locale

module HeytingComplementationLemmas (X : Locale 𝓤 𝓥 𝓥)
                                    (𝒷 : has-basis (𝒪 X) holds) where


  open HeytingImplicationConstruction X 𝒷

  complement-is-heyting-complement : (C C′ : ⟨ 𝒪 X ⟩)
                                   → is-boolean-complement-of (𝒪 X) C′ C holds
                                   → C′ ＝ C ==> 𝟎[ 𝒪 X ]
  complement-is-heyting-complement C C′ (p , q) =
   ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
    where
     open PosetReasoning (poset-of (𝒪 X))

     ※ : (((C ==> 𝟎[ 𝒪 X ]) ∧[ 𝒪 X ] (C ∨[ 𝒪 X ] C′)) ≤[ poset-of (𝒪 X) ] C′) holds
     ※ =
      (C ==> 𝟎[ 𝒪 X ]) ∧[ 𝒪 X ] (C ∨[ 𝒪 X ] C′)                             ＝⟨ Ⅰ ⟩ₚ
      ((C ==> 𝟎[ 𝒪 X ]) ∧[ 𝒪 X ] C) ∨[ 𝒪 X ] ((C ==> 𝟎[ 𝒪 X ]) ∧[ 𝒪 X ] C′) ≤⟨ Ⅱ  ⟩
      C′                                                                    ■
       where
        Ⅰ = binary-distributivity (𝒪 X) (C ==> 𝟎[ 𝒪 X ]) C C′
        Ⅱ = ∨[ 𝒪 X ]-least
             ((C ==> 𝟎[ 𝒪 X ]) ∧[ 𝒪 X ] C    ≤⟨ mp-right C 𝟎[ 𝒪 X ]  ⟩
              𝟎[ 𝒪 X ]                       ≤⟨ 𝟎-is-bottom (𝒪 X) C′ ⟩
              C′                             ■)
             (∧[ 𝒪 X ]-lower₂ (C ==> 𝟎[ 𝒪 X ]) C′)

     † : (C′ ≤[ poset-of (𝒪 X) ] (C ==> 𝟎[ 𝒪 X ])) holds
     † = heyting-implication₁ C 𝟎[ 𝒪 X ] C′ †₁
      where
       †₁ : ((C′ ∧[ 𝒪 X ] C) ≤[ poset-of (𝒪 X) ] 𝟎[ 𝒪 X ]) holds
       †₁ = C′ ∧[ 𝒪 X ] C   ＝⟨ ∧[ 𝒪 X ]-is-commutative C′ C ⟩ₚ
            C  ∧[ 𝒪 X ] C′  ＝⟨ p ⟩ₚ
            𝟎[ 𝒪 X ]        ■

     ‡ : (C ==> 𝟎[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] C′) holds
     ‡ = C ==> 𝟎[ 𝒪 X ]          ≤⟨ Ⅰ                ⟩
         (C ∨[ 𝒪 X ] C′) ==> C′  ＝⟨ Ⅱ               ⟩ₚ
         𝟏[ 𝒪 X ] ==> C′         ＝⟨ 𝟏-==>-law C′ ⁻¹ ⟩ₚ
         C′                      ■
          where
           Ⅰ = heyting-implication₁ (C ∨[ 𝒪 X ] C′) C′ (C ==> 𝟎[ 𝒪 X ]) ※
           Ⅱ = ap (λ - → - ==> C′) q

  heyting-complement-is-complement : (C C′ : ⟨ 𝒪 X ⟩)
                                   → is-boolean-complement-of (𝒪 X) C′ C holds
                                   → is-boolean-complement-of (𝒪 X) (C ==> 𝟎[ 𝒪 X ]) C holds
  heyting-complement-is-complement C C′ (p , q) = † , ‡
   where
    † : C ∧[ 𝒪 X ] (C ==> 𝟎[ 𝒪 X ]) ＝ 𝟎[ 𝒪 X ]
    † = C ∧[ 𝒪 X ] (C ==> 𝟎[ 𝒪 X ])  ＝⟨ ※ ⟩
        C ∧[ 𝒪 X ] C′                ＝⟨ p ⟩
        𝟎[ 𝒪 X ]                     ∎
         where
          ※ = ap
               (λ - → C ∧[ 𝒪 X ] -)
               (complement-is-heyting-complement C C′ (p , q) ⁻¹)


    ‡ : C ∨[ 𝒪 X ] (C ==> 𝟎[ 𝒪 X ]) ＝ 𝟏[ 𝒪 X ]
    ‡ = C ∨[ 𝒪 X ] (C ==> 𝟎[ 𝒪 X ])  ＝⟨ ※ ⟩
        C ∨[ 𝒪 X ] C′                ＝⟨ q ⟩
        𝟏[ 𝒪 X ]                     ∎
         where
          ※ = ap
               (λ - → C ∨[ 𝒪 X ] -)
               (complement-is-heyting-complement C C′ (p , q) ⁻¹)

  material-implication : (C U : ⟨ 𝒪 X ⟩)
                       → is-clopen₀ (𝒪 X) C
                       → (C ==> U) ＝ (C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U
  material-implication C U (C′ , p , q) = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
   where
    open PosetReasoning (poset-of (𝒪 X))

    † : ((C ==> U) ≤[ poset-of (𝒪 X) ] ((C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U)) holds
    † = (C ==> U)                                         ≤⟨ Ⅰ ⟩
        (C ∨[ 𝒪 X ] C′) ==> ((C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U) ＝⟨ Ⅱ ⟩ₚ
        𝟏[ 𝒪 X ] ==> ((C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U)        ＝⟨ Ⅲ ⟩ₚ
        (C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U                       ■
         where
          ※ = (C ==> U) ∧[ 𝒪 X ] (C ∨[ 𝒪 X ] C′)                        ＝⟨ Ⅰ ⟩ₚ
              ((C ==> U) ∧[ 𝒪 X ] C) ∨[ 𝒪 X ] ((C ==> U) ∧[ 𝒪 X ] C′)   ≤⟨ Ⅱ  ⟩
              U ∨[ 𝒪 X ] ((C ==> U) ∧[ 𝒪 X ] C′)                        ≤⟨ Ⅲ  ⟩
              U ∨[ 𝒪 X ] C′                                             ＝⟨ Ⅳ ⟩ₚ
              C′ ∨[ 𝒪 X ] U                                             ＝⟨ Ⅴ ⟩ₚ
              (C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U                               ■
               where
                Ⅰ = binary-distributivity (𝒪 X) (C ==> U) C C′
                Ⅱ = ∨[ 𝒪 X ]-left-monotone (mp-right C U)
                Ⅲ = ∨[ 𝒪 X ]-right-monotone (∧[ 𝒪 X ]-lower₂ (C ==> U) C′)
                Ⅳ = ∨[ 𝒪 X ]-is-commutative U C′
                Ⅴ = ap
                     (λ - → - ∨[ 𝒪 X ] U)
                     (complement-is-heyting-complement C C′ (p , q))

          Ⅰ = heyting-implication₁
               (C ∨[ 𝒪 X ] C′)
               ((C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U)
               (C ==> U)
               ※
          Ⅱ = ap (λ - → - ==> ((C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U)) q
          Ⅲ = 𝟏-==>-law ((C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U) ⁻¹

    ‡ : (((C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U) ≤[ poset-of (𝒪 X) ] (C ==> U)) holds
    ‡ = heyting-implication₁ C U ((C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U) ‡₁
     where
      ‡₁ : ((((C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U) ∧[ 𝒪 X ] C)
             ≤[ poset-of (𝒪 X) ]
            U) holds
      ‡₁ = ((C ==> 𝟎[ 𝒪 X ]) ∨[ 𝒪 X ] U) ∧[ 𝒪 X ] C               ＝⟨ Ⅰ ⟩ₚ
           ((C ==> 𝟎[ 𝒪 X ]) ∧[ 𝒪 X ] C) ∨[ 𝒪 X ] (U ∧[ 𝒪 X ] C)  ≤⟨ Ⅱ ⟩
           U                                                      ■
            where
             ※ = (C ==> 𝟎[ 𝒪 X ]) ∧[ 𝒪 X ] C    ≤⟨ mp-right C 𝟎[ 𝒪 X ] ⟩
                 𝟎[ 𝒪 X ]                       ≤⟨ 𝟎-is-bottom (𝒪 X) U ⟩
                 U                              ■

             Ⅰ = binary-distributivity-right (𝒪 X)
             Ⅱ = ∨[ 𝒪 X ]-least ※ (∧[ 𝒪 X ]-lower₁ U C)

  double-negation-elimination : (C : ⟨ 𝒪 X ⟩)
                              → is-clopen₀ (𝒪 X) C
                              → (C ==> 𝟎[ 𝒪 X ]) ==> 𝟎[ 𝒪 X ] ＝ C
  double-negation-elimination C (C′ , p , q) =
   ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
    where
     open PosetReasoning (poset-of (𝒪 X))

     † : (((C ==> 𝟎[ 𝒪 X ]) ==> 𝟎[ 𝒪 X ]) ≤[ poset-of (𝒪 X) ] C) holds
     † = (C ==> 𝟎[ 𝒪 X ]) ==> 𝟎[ 𝒪 X ]        ＝⟨ Ⅰ ⟩ₚ
         C′ ==> 𝟎[ 𝒪 X ]                      ＝⟨ Ⅱ ⟩ₚ
         C                                    ■
          where
           Ⅰ = ap
                (λ - → - ==> 𝟎[ 𝒪 X ])
                (complement-is-heyting-complement C C′ (p , q) ⁻¹)
           Ⅱ = complement-is-heyting-complement C′ C (Ⅱ₁ , Ⅱ₂) ⁻¹
                where
                 Ⅱ₁ = C′ ∧[ 𝒪 X ] C     ＝⟨ ∧[ 𝒪 X ]-is-commutative C′ C ⟩
                      C  ∧[ 𝒪 X ] C′    ＝⟨ p                            ⟩
                      𝟎[ 𝒪 X ]          ∎
                 Ⅱ₂ = C′ ∨[ 𝒪 X ] C     ＝⟨ ∨[ 𝒪 X ]-is-commutative C′ C ⟩
                      C  ∨[ 𝒪 X ] C′    ＝⟨ q                            ⟩
                      𝟏[ 𝒪 X ]          ∎

     ‡ : (C ≤[ poset-of (𝒪 X) ] (C ==> 𝟎[ 𝒪 X ]) ==> 𝟎[ 𝒪 X ]) holds
     ‡ = heyting-implication₁ (C ==> 𝟎[ 𝒪 X ]) 𝟎[ 𝒪 X ] C ‡₁
      where
       ‡₁ : ((C ∧[ 𝒪 X ] (C ==> 𝟎[ 𝒪 X ])) ≤[ poset-of (𝒪 X) ] 𝟎[ 𝒪 X ]) holds
       ‡₁ = mp-left C 𝟎[ 𝒪 X ]

  negation-∨-lemma₁ : {U V W : ⟨ 𝒪 X ⟩}
                    → is-clopen₀ (𝒪 X) V
                    → (U ≤[ poset-of (𝒪 X) ] (V ∨[ 𝒪 X ] W)) holds
                    → ((U ∧[ 𝒪 X ] (V ==> 𝟎[ 𝒪 X ]))
                        ≤[ poset-of (𝒪 X) ]
                       W) holds
  negation-∨-lemma₁ {U} {V} {W} (V′ , p , q) φ =
   U ∧[ 𝒪 X ] (V ==> 𝟎[ 𝒪 X ])               ＝⟨ Ⅰ ⟩ₚ
   U ∧[ 𝒪 X ] V′                             ≤⟨ Ⅱ  ⟩
   (V ∨[ 𝒪 X ] W) ∧[ 𝒪 X ] V′                ＝⟨ Ⅲ ⟩ₚ
   (V ∧[ 𝒪 X ] V′) ∨[ 𝒪 X ] (W ∧[ 𝒪 X ] V′)  ＝⟨ Ⅳ ⟩ₚ
   𝟎[ 𝒪 X ] ∨[ 𝒪 X ] (W ∧[ 𝒪 X ] V′)         ＝⟨ Ⅴ ⟩ₚ
   W ∧[ 𝒪 X ] V′                             ≤⟨  Ⅵ ⟩
   W                                         ■
    where
     open PosetReasoning (poset-of (𝒪 X))

     Ⅰ = ap
          (λ - → U ∧[ 𝒪 X ] -)
          (complement-is-heyting-complement V V′ (p , q) ⁻¹)
     Ⅱ = ∧[ 𝒪 X ]-left-monotone φ
     Ⅲ = binary-distributivity-right (𝒪 X)
     Ⅳ = ap (λ - → - ∨[ 𝒪 X ] (W ∧[ 𝒪 X ] V′)) p
     Ⅴ = 𝟎-right-unit-of-∨ (𝒪 X) (W ∧[ 𝒪 X ] V′)
     Ⅵ = ∧[ 𝒪 X ]-lower₁ W V′

  negation-∨-lemma₂ : {U V W : ⟨ 𝒪 X ⟩}
                 → is-clopen₀ (𝒪 X) V
                  → ((U ∧[ 𝒪 X ] (V ==> 𝟎[ 𝒪 X ]))
                      ≤[ poset-of (𝒪 X) ]
                     W) holds
                  → (U ≤[ poset-of (𝒪 X) ] (V ∨[ 𝒪 X ] W)) holds
  negation-∨-lemma₂ {U} {V} {W} (V′ , p , q) φ =
   U                                                      ＝⟨ Ⅰ ⟩ₚ
   U ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]                                    ＝⟨ Ⅱ ⟩ₚ
   U ∧[ 𝒪 X ] (V ∨[ 𝒪 X ] V′)                             ＝⟨ Ⅲ ⟩ₚ
   (U ∧[ 𝒪 X ] V) ∨[ 𝒪 X ] (U ∧[ 𝒪 X ] V′)                ＝⟨ Ⅳ ⟩ₚ
   (U ∧[ 𝒪 X ] V) ∨[ 𝒪 X ] (U ∧[ 𝒪 X ] (V ==> 𝟎[ 𝒪 X ]))  ≤⟨ Ⅴ  ⟩
   (U ∧[ 𝒪 X ] V) ∨[ 𝒪 X ] W                              ≤⟨ Ⅵ  ⟩
   V ∨[ 𝒪 X ] W                                           ■
    where
     open PosetReasoning (poset-of (𝒪 X))

     Ⅰ =  𝟏-right-unit-of-∧ (𝒪 X) U ⁻¹
     Ⅱ = ap (λ - → U ∧[ 𝒪 X ] -) (q ⁻¹)
     Ⅲ = binary-distributivity (𝒪 X) U V V′
     Ⅳ = ap
          (λ - → (U ∧[ 𝒪 X ] V) ∨[ 𝒪 X ] (U ∧[ 𝒪 X ] -))
          (complement-is-heyting-complement V V′ (p , q))
     Ⅴ = ∨[ 𝒪 X ]-right-monotone φ
     Ⅵ = ∨[ 𝒪 X ]-left-monotone (∧[ 𝒪 X ]-lower₂ U V)

\end{code}

\section{Preamble}

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt

module Locales.HeytingImplication
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
         where

open import Locales.Frame pt fe
open import Locales.GaloisConnection pt fe
open import UF.Logic
open import UF.SubtypeClassifier
open import UF.Subsingletons

open AllCombinators pt fe
open PropositionalTruncation pt

open import Locales.AdjointFunctorTheoremForFrames pt fe

open Locale

is-heyting-implication-of : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ × ⟨ 𝒪 X ⟩ →  Ω (𝓤 ⊔ 𝓥)
is-heyting-implication-of X z (x , y) =
 Ɐ w ꞉ ⟨ 𝒪 X ⟩ , ((w ∧[ 𝒪 X ] x) ≤[ poset-of (𝒪 X) ] y) ⇔ (w ≤[ poset-of (𝒪 X) ] z)

is-heyting-implication-operation : (X : Locale 𝓤 𝓥 𝓦)
                                 → (⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩)
                                 → Ω (𝓤 ⊔ 𝓥)
is-heyting-implication-operation X _==>_ =
 Ɐ x ꞉ ⟨ 𝒪 X ⟩ , Ɐ y ꞉ ⟨ 𝒪 X ⟩ , is-heyting-implication-of X (x ==> y) (x , y)

modus-ponens : (X : Locale 𝓤 𝓥 𝓦) {U V W : ⟨ 𝒪 X ⟩}
             → is-heyting-implication-of X W (U , V) holds
             → ((W ∧[ 𝒪 X ] U) ≤[ poset-of (𝒪 X) ] V) holds
modus-ponens X {x} {y} {z} p = pr₂ (p z) (≤-is-reflexive (poset-of (𝒪 X)) z)
 where
  open PosetReasoning (poset-of (𝒪 X))

module HeytingImplicationConstruction (X : Locale 𝓤  𝓥  𝓥)
                                      (𝒷 : has-basis (𝒪 X) holds) where

\end{code}

\begin{code}

 private
  _≤_ = λ U V → U ≤[ poset-of (𝒪 X) ] V
  L   = 𝒪 X
  Lₚ  = poset-of (𝒪 X)

 open GaloisConnectionBetween
 open AdjointFunctorTheorem X X 𝒷

 ∧-right-preserves-joins : (U : ⟨ 𝒪 X ⟩)
                         → (is-join-preserving (𝒪 X) (𝒪 X) (meet-of (𝒪 X) U)) holds
 ∧-right-preserves-joins = distributivity (𝒪 X)

 meet-right-is-monotonic : (U : ⟨ 𝒪 X ⟩) → is-monotonic Lₚ Lₚ (meet-of (𝒪 X) U) holds
 meet-right-is-monotonic U = scott-continuous-implies-monotone L L (meet-of L U) ν
  where
   ν : is-scott-continuous (𝒪 X) (𝒪 X) (meet-of (𝒪 X) U) holds
   ν = join-preserving-implies-scott-continuous L L (meet-of L U) (∧-right-preserves-joins U)

 meet-rightₘ : ⟨ L ⟩ → Lₚ ─m→ Lₚ
 meet-rightₘ U = (λ V → U ∧[ L ] V) , meet-right-is-monotonic U

 _==>_ : ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩
 _==>_ U = pr₁ (pr₁ (aft-backward (meet-rightₘ U) (∧-right-preserves-joins U)))

 ==>-is-heyting-implication : is-heyting-implication-operation X _==>_ holds
 ==>-is-heyting-implication U V W = β , γ
  where
   open PosetReasoning (poset-of L)

   ψ = aft-backward (meet-rightₘ U) (∧-right-preserves-joins U)

   β : ((W ∧[ L ] U) ≤[ poset-of L ] V ⇒ W ≤[ poset-of L ] (U ==> V)) holds
   β p = pr₁ (pr₂ ψ W V) (U ∧[ L ] W   ＝⟨ ∧[ L ]-is-commutative U W ⟩ₚ
                          W ∧[ L ] U   ≤⟨ p ⟩
                          V            ■)

   † : ((U ∧[ L ] (U ==> V)) ≤[ poset-of L ] V) holds
   † = pr₂ (pr₂ ψ (U ==> V) V) (≤-is-reflexive (poset-of L) (U ==> V))

   γ : (W ≤[ poset-of L ] (U ==> V) ⇒ (W ∧[ L ] U) ≤[ poset-of L ] V) holds
   γ p = W ∧[ L ] U            ≤⟨ ∧[ L ]-left-monotone p            ⟩
         (U ==> V) ∧[ L ] U    ＝⟨ ∧[ L ]-is-commutative (U ==> V) U ⟩ₚ
         U ∧[ L ] (U ==> V)    ≤⟨ †                                 ⟩
         V                     ■

 heyting-implication₁ : (U V W : ⟨ 𝒪 X ⟩)
                      → ((W ∧[ 𝒪 X ] U) ≤ V ⇒ W ≤ (U ==> V))
                         holds
 heyting-implication₁ U V W = pr₁ (==>-is-heyting-implication U V W)

 heyting-implication₂ : (U V W : ⟨ 𝒪 X ⟩)
                      → (W ≤ (U ==> V) ⇒ ((W ∧[ 𝒪 X ] U) ≤ V)) holds
 heyting-implication₂ U V W = pr₂ (==>-is-heyting-implication U V W)

 currying : (U V W : ⟨ 𝒪 X ⟩)
          → (((U ∧[ 𝒪 X ] V) ==> W) ≤ (U ==> (V ==> W))) holds
 currying U V W = heyting-implication₁ U (V ==> W) _ (heyting-implication₁ V W _ γ)
  where
   open PosetReasoning (poset-of (𝒪 X))

   i   = ∧[ 𝒪 X ]-is-associative ((U ∧[ 𝒪 X ] V) ==> W) U V ⁻¹
   ii  = modus-ponens X (==>-is-heyting-implication (U ∧[ 𝒪 X ] V) W)

   γ : ((((U ∧[ 𝒪 X ] V) ==> W) ∧[ 𝒪 X ] U ∧[ 𝒪 X ] V) ≤ W) holds
   γ = ((U ∧[ 𝒪 X ] V) ==> W) ∧[ 𝒪 X ] U ∧[ 𝒪 X ] V    ＝⟨ i  ⟩ₚ
       ((U ∧[ 𝒪 X ] V) ==> W) ∧[ 𝒪 X ] (U ∧[ 𝒪 X ] V)  ≤⟨ ii ⟩
       W                                               ■

 mp-right : (U V : ⟨ 𝒪 X ⟩) → (((U ==> V) ∧[ 𝒪 X ] U) ≤[ poset-of (𝒪 X) ] V) holds
 mp-right U V = modus-ponens X (==>-is-heyting-implication U V)

 mp-left : (U V : ⟨ 𝒪 X ⟩) → ((U ∧[ 𝒪 X ] (U ==> V)) ≤[ poset-of (𝒪 X) ] V) holds
 mp-left U V = U ∧[ 𝒪 X ] (U ==> V)   ＝⟨ ∧[ 𝒪 X ]-is-commutative U (U ==> V) ⟩ₚ
              (U ==> V) ∧[ 𝒪 X ] U    ≤⟨ mp-right U V                        ⟩
              V                       ■
  where
   open PosetReasoning (poset-of (𝒪 X))

 heyting-implication-identity : (U : ⟨ 𝒪 X ⟩) → U ==> U ＝ 𝟏[ 𝒪 X ]
 heyting-implication-identity U = only-𝟏-is-above-𝟏 (𝒪 X) (U ==> U) †
  where
   † : (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X ) ] (U ==> U)) holds
   † = heyting-implication₁ U U 𝟏[ 𝒪 X ] (∧[ 𝒪 X ]-lower₂ 𝟏[ 𝒪 X ] U)

 weakening : (U V : ⟨ 𝒪 X ⟩) → (V ≤[ poset-of (𝒪 X) ] (U ==> V)) holds
 weakening U V = heyting-implication₁ U V V (∧[ 𝒪 X ]-lower₁ V U)

 ex-falso-quodlibet : (U : ⟨ 𝒪 X ⟩)
                    → (𝟏[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] (𝟎[ 𝒪 X ] ==> U)) holds
 ex-falso-quodlibet U = heyting-implication₁ 𝟎[ 𝒪 X ] U 𝟏[ 𝒪 X ] †
  where
   open PosetReasoning (poset-of (𝒪 X))

   † : ((𝟏[ 𝒪 X ] ∧[ 𝒪 X ] 𝟎[ 𝒪 X ]) ≤[ poset-of (𝒪 X) ] U) holds
   † = 𝟏[ 𝒪 X ] ∧[ 𝒪 X ] 𝟎[ 𝒪 X ]  ＝⟨ 𝟏-left-unit-of-∧ (𝒪 X) 𝟎[ 𝒪 X ] ⟩ₚ
       𝟎[ 𝒪 X ]                    ≤⟨ 𝟎-is-bottom (𝒪 X) U ⟩
       U                           ■

 H₈ : (U V : ⟨ 𝒪 X ⟩) → U ＝ (U ∨[ 𝒪 X ] V) ∧[ 𝒪 X ] (V ==> U)
 H₈ U V = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
  where
   open PosetReasoning (poset-of (𝒪 X))

   † : (U ≤[ poset-of (𝒪 X) ] ((U ∨[ 𝒪 X ] V) ∧[ 𝒪 X ] V ==> U)) holds
   † = ∧[ 𝒪 X ]-greatest (U ∨[ 𝒪 X ] V) (V ==> U) U
        (∨[ 𝒪 X ]-upper₁ U V)
        (weakening V U)

   ‡ : (((U ∨[ 𝒪 X ] V) ∧[ 𝒪 X ] (V ==> U)) ≤[ poset-of (𝒪 X) ] U) holds
   ‡ = (U ∨[ 𝒪 X ] V) ∧[ 𝒪 X ] (V ==> U)                        ＝⟨ Ⅰ ⟩ₚ
       (V ==> U) ∧[ 𝒪 X ] (U ∨[ 𝒪 X ] V)                        ＝⟨ Ⅱ ⟩ₚ
       ((V ==> U) ∧[ 𝒪 X ] U) ∨[ 𝒪 X ] ((V ==> U) ∧[ 𝒪 X ] V)   ≤⟨ Ⅲ ⟩
       ((V ==> U) ∧[ 𝒪 X ] U) ∨[ 𝒪 X ] U                        ≤⟨ Ⅳ ⟩
       U ∨[ 𝒪 X ] U                                             ＝⟨ Ⅴ ⟩ₚ
       U                                                        ■
        where
         Ⅰ = ∧[ 𝒪 X ]-is-commutative (U ∨[ 𝒪 X ] V) (V ==> U)
         Ⅱ = binary-distributivity (𝒪 X) (V ==> U) U V
         Ⅲ = ∨[ 𝒪 X ]-right-monotone (mp-right V U)
         Ⅳ = ∨[ 𝒪 X ]-left-monotone (∧[ 𝒪 X ]-lower₂ (V ==> U) U)
         Ⅴ = ∨[ 𝒪 X ]-is-idempotent U ⁻¹

 heyting-implication-law₄ : (U V : ⟨ 𝒪 X ⟩) → (U ==> V) ＝ U ==> (U ∧[ 𝒪 X ] V)
 heyting-implication-law₄ U V = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
  where
   open PosetReasoning (poset-of (𝒪 X))

   † : (U ==> V ≤[ poset-of (𝒪 X) ] U ==> (U ∧[ 𝒪 X ] V)) holds
   † = heyting-implication₁ U (U ∧[ 𝒪 X ] V) (U ==> V) †₁
    where
     †₁ : (((U ==> V) ∧[ 𝒪 X ] U) ≤ (U ∧[ 𝒪 X ] V)) holds
     †₁ = (U ==> V) ∧[ 𝒪 X ] U                  ＝⟨ I   ⟩ₚ
          U ∧[ 𝒪 X ] (U ==> V)                  ＝⟨ II  ⟩ₚ
          (U ∧[ 𝒪 X ] U) ∧[ 𝒪 X ] (U ==> V)     ＝⟨ III ⟩ₚ
          U ∧[ 𝒪 X ] (U ∧[ 𝒪 X ] (U ==> V))     ≤⟨ IV   ⟩
          U ∧[ 𝒪 X ] V                          ■
           where
            I   = ∧[ 𝒪 X ]-is-commutative (U ==> V) U
            II  = ap (λ - → - ∧[ 𝒪 X ] (U ==> V)) (∧[ 𝒪 X ]-is-idempotent U)
            III = ∧[ 𝒪 X ]-is-associative U U (U ==> V) ⁻¹
            IV  = ∧[ 𝒪 X ]-right-monotone (mp-left U V)

   ‡ : (U ==> (U ∧[ 𝒪 X ] V) ≤[ poset-of (𝒪 X) ] (U ==> V)) holds
   ‡ = heyting-implication₁ U V (U ==> (U ∧[ 𝒪 X ] V)) ‡₁
    where
     I  = mp-right U (U ∧[ 𝒪 X ] V)
     II = ∧[ 𝒪 X ]-lower₂ U V

     ‡₁ : ((U ==> (U ∧[ 𝒪 X ] V) ∧[ 𝒪 X ] U) ≤ V) holds
     ‡₁ = (U ==> (U ∧[ 𝒪 X ] V)) ∧[ 𝒪 X ] U     ≤⟨ I  ⟩
          U ∧[ 𝒪 X ] V                          ≤⟨ II ⟩
          V                                     ■

 ==>-right-monotone : {U V W : ⟨ 𝒪 X ⟩}
                    → (V ≤[ poset-of (𝒪 X) ] W) holds
                    → ((U ==> V) ≤[ poset-of (𝒪 X ) ] (U ==> W)) holds
 ==>-right-monotone {U} {V} {W} p = heyting-implication₁ U W (U ==> V) †
  where
   open PosetReasoning (poset-of (𝒪 X))

   † : (((U ==> V) ∧[ 𝒪 X ] U) ≤[ poset-of (𝒪 X) ] W) holds
   † = (U ==> V) ∧[ 𝒪 X ] U ≤⟨ mp-right U V ⟩ V ≤⟨ p ⟩ W ■

 𝟏-==>-law : (U : ⟨ 𝒪 X ⟩) → U ＝ 𝟏[ 𝒪 X ] ==> U
 𝟏-==>-law U = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
  where
   open PosetReasoning (poset-of (𝒪 X))

   † : (U ≤[ poset-of (𝒪 X) ] 𝟏[ 𝒪 X ] ==> U) holds
   † = weakening 𝟏[ 𝒪 X ] U

   ‡ : (𝟏[ 𝒪 X ] ==> U ≤[ poset-of (𝒪 X) ] U) holds
   ‡ = (𝟏[ 𝒪 X ] ==> U)                    ＝⟨ Ⅰ ⟩ₚ
       (𝟏[ 𝒪 X ] ==> U) ∧[ 𝒪 X ] 𝟏[ 𝒪 X ]  ≤⟨ Ⅱ ⟩
       U                                   ■
        where
         Ⅰ = 𝟏-right-unit-of-∧ (𝒪 X) (𝟏[ 𝒪 X ] ==> U) ⁻¹
         Ⅱ = mp-right 𝟏[ 𝒪 X ] U

 ==>-left-reverses-joins : (U V W : ⟨ 𝒪 X ⟩)
                         → U ==> W ∧[ 𝒪 X ] (V ==> W) ＝ (U ∨[ 𝒪 X ] V) ==> W
 ==>-left-reverses-joins U V W = ≤-is-antisymmetric (poset-of (𝒪 X)) † ‡
  where
   open PosetReasoning (poset-of (𝒪 X))
   lhs₁ = U ==> W
   lhs₂ = V ==> W
   lhs₃ = (U ∨[ 𝒪 X ] V) ==> W

   ※ =
    (lhs₁ ∧[ 𝒪 X ] lhs₂) ∧[ 𝒪 X ] (U ∨[ 𝒪 X ] V)                                  ＝⟨ Ⅰ ⟩ₚ
    ((lhs₁ ∧[ 𝒪 X ] lhs₂) ∧[ 𝒪 X ] U) ∨[ 𝒪 X ] ((lhs₁ ∧[ 𝒪 X ] lhs₂) ∧[ 𝒪 X ] V)  ≤⟨ Ⅱ  ⟩
    (lhs₁ ∧[ 𝒪 X ] U) ∨[ 𝒪 X ] ((lhs₁ ∧[ 𝒪 X ] lhs₂) ∧[ 𝒪 X ] V)                  ≤⟨ Ⅲ  ⟩
    (lhs₁ ∧[ 𝒪 X ] U) ∨[ 𝒪 X ] (lhs₂ ∧[ 𝒪 X ] V)                                  ≤⟨ Ⅳ  ⟩
    W                                                                             ■
     where
      Ⅰ = binary-distributivity (𝒪 X) (lhs₁ ∧[ 𝒪 X ] lhs₂) U V
      Ⅱ = ∨[ 𝒪 X ]-left-monotone (∧[ 𝒪 X ]-left-monotone (∧[ 𝒪 X ]-lower₁ lhs₁ lhs₂))
      Ⅲ = ∨[ 𝒪 X ]-right-monotone (∧[ 𝒪 X ]-left-monotone (∧[ 𝒪 X ]-lower₂ lhs₁ lhs₂))
      Ⅳ = ∨[ 𝒪 X ]-least (mp-right U W) (mp-right V W)

   † : ((lhs₁ ∧[ 𝒪 X ] lhs₂) ≤[ poset-of (𝒪 X) ] lhs₃) holds
   † = heyting-implication₁ (U ∨[ 𝒪 X ] V) W ((U ==> W) ∧[ 𝒪 X ] (V ==> W)) ※

   ‡ : (lhs₃ ≤[ poset-of (𝒪 X) ] (lhs₁ ∧[ 𝒪 X ] lhs₂)) holds
   ‡ = ∧[ 𝒪 X ]-greatest lhs₁ lhs₂ lhs₃ ♣ ♠
        where
         ♣ : (lhs₃ ≤[ poset-of (𝒪 X) ] lhs₁) holds
         ♣ = heyting-implication₁ U W lhs₃ ♢
          where
           Ⅰ = ∧[ 𝒪 X ]-right-monotone (∨[ 𝒪 X ]-upper₁ U V)
           Ⅱ = mp-right (U ∨[ 𝒪 X ] V) W
           ♢ = lhs₃ ∧[ 𝒪 X ] U               ≤⟨ Ⅰ ⟩
               lhs₃ ∧[ 𝒪 X ] (U ∨[ 𝒪 X ] V)  ≤⟨ Ⅱ ⟩
               W                             ■

         ♠ : (lhs₃ ≤[ poset-of (𝒪 X) ] lhs₂) holds
         ♠ = heyting-implication₁ V W lhs₃ ♢
          where
           Ⅰ = ∧[ 𝒪 X ]-right-monotone (∨[ 𝒪 X ]-upper₂ U V)
           Ⅱ = mp-right (U ∨[ 𝒪 X ] V) W
           ♢ = lhs₃ ∧[ 𝒪 X ] V               ≤⟨ Ⅰ ⟩
               lhs₃ ∧[ 𝒪 X ] (U ∨[ 𝒪 X ] V)  ≤⟨ Ⅱ ⟩
               W                             ■

\end{code}

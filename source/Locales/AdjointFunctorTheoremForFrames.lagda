--------------------------------------------------------------------------------
author:        Ayberk Tosun
date-started:  2022-03-01
dates-updated: [2024-05-06]
--------------------------------------------------------------------------------

Originally part of `ayberkt/formal-topology-in-UF`. Ported to TypeTopology on
2022-03-01.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module Locales.AdjointFunctorTheoremForFrames
         (pt : propositional-truncations-exist)
         (fe : Fun-Ext)
         where

open import Locales.ContinuousMap.Definition pt fe
open import Locales.ContinuousMap.FrameHomomorphism-Properties pt fe
open import Locales.Frame pt fe
open import Locales.PosetalAdjunction pt fe
open import Slice.Family
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt
open import UF.SubtypeClassifier

open Locale

\end{code}

\begin{code}

module AdjointFunctorTheorem (X : Locale 𝓤' 𝓥 𝓥)
                             (Y : Locale 𝓤  𝓥  𝓥)
                             (𝒷 : has-basis (𝒪 Y) holds) where

\end{code}

\begin{code}

 private
  𝒪Xₚ = poset-of (𝒪 X)
  𝒪Yₚ = poset-of (𝒪 Y)

 open PosetalAdjunctionBetween 𝒪Yₚ 𝒪Xₚ

 aft-forward : (f : 𝒪Yₚ ─m→ 𝒪Xₚ)
             → has-right-adjoint f
             → is-join-preserving (𝒪 Y) (𝒪 X) (f .pr₁) holds
 aft-forward (f , μ) (ℊ@(g , _) , p) S =
  ⋁[ 𝒪 X ]-unique ⁅ f s ∣ s ε S ⁆ (f (⋁[ 𝒪 Y ] S)) (β , γ)
   where
    open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
    open Joins (λ x y → x ≤[ poset-of (𝒪 Y) ] y)
     using () renaming (_is-an-upper-bound-of_ to _is-a-ub-of_)

    β : (f (⋁[ 𝒪 Y ] S) is-an-upper-bound-of ⁅ f s ∣ s ε S ⁆) holds
    β i = μ (S [ i ] , ⋁[ 𝒪 Y ] S) (⋁[ 𝒪 Y ]-upper S i)

    γ : (Ɐ (u , _) ꞉ upper-bound ⁅ f s ∣ s ε S ⁆ , f (⋁[ 𝒪 Y ] S) ≤[ 𝒪Xₚ ] u) holds
    γ (u , q) = pr₂ (p (⋁[ 𝒪 Y ] S) u) (⋁[ 𝒪 Y ]-least S (g u , δ))
     where
      δ : (g u is-a-ub-of S) holds
      δ i = pr₁ (p (S [ i ]) u) (q i)

\end{code}

\begin{code}

 aft-backward : (𝒻 : 𝒪Yₚ ─m→ 𝒪Xₚ)
              → is-join-preserving (𝒪 Y) (𝒪 X) (𝒻 .pr₁) holds
              → has-right-adjoint 𝒻
 aft-backward 𝒻@(f , μf) φ = ∥∥-rec (has-right-adjoint-is-prop 𝒻) γ 𝒷
  where
   open Joins (λ x y → x ≤[ poset-of (𝒪 Y) ] y)
   open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
         using    ()
         renaming (_is-an-upper-bound-of_ to _is-an-ub-of_)

   γ : Σ ℬ ꞉ Fam 𝓥 ⟨ 𝒪 Y ⟩ , is-basis-for (𝒪 Y) ℬ → Σ ℊ ꞉ 𝒪Xₚ ─m→ 𝒪Yₚ , (𝒻 ⊣ ℊ) holds
   γ (ℬ , b) = (g , μ′) , β
    where
     𝒦 : ∣ 𝒪Xₚ ∣ₚ → 𝓥 ̇
     𝒦 y = Σ i ꞉ index ℬ , (f (ℬ [ i ]) ≤[ 𝒪Xₚ ] y) holds

     g : ∣ 𝒪Xₚ ∣ₚ → ∣ 𝒪Yₚ ∣ₚ
     g y = ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y ⁆

     μ′ : is-monotonic 𝒪Xₚ 𝒪Yₚ g holds
     μ′ (y₁ , y₂) p =
      ⋁[ 𝒪 Y ]-least ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y₁ ⁆ (g y₂ , ε)
        where
         open PosetReasoning 𝒪Xₚ

         ε : (g y₂ is-an-upper-bound-of ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y₁ ⁆) holds
         ε 𝒾@(i , q) = ⋁[ 𝒪 Y ]-upper ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 y₂ ⁆ (i , †)
          where
           † : (f (ℬ [ i ]) ≤[ 𝒪Xₚ ] y₂) holds
           † = f (ℬ [ i ]) ≤⟨ q ⟩ y₁ ≤⟨ p ⟩ y₂ ■

     ℊ = g , μ′

     β : (𝒻 ⊣ ℊ) holds
     β U V = β₁ , β₂
      where
       𝒥 : Fam 𝓥 (index ℬ)
       𝒥 = pr₁ (b U)

       c : U ＝ ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆
       c = ⋁[ 𝒪 Y ]-unique ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ U (pr₂ (b U))

       β₁ : (f U ≤[ 𝒪Xₚ ] V ⇒ U ≤[ 𝒪Yₚ ] g V) holds
       β₁ p = U                             ＝⟨ c ⟩ₚ
              ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆  ≤⟨ † ⟩
              g V                           ■
        where
         open PosetReasoning 𝒪Yₚ
         open PosetReasoning 𝒪Xₚ using () renaming (_■ to _■ₗ; _≤⟨_⟩_ to _≤⟨_⟩ₗ_)

         u = ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 V ⁆

         ζ : (u is-an-upper-bound-of ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆) holds
         ζ j = ⋁[ 𝒪 Y ]-upper ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 V ⁆ (𝒥 [ j ] , η)
                where
                 θ : ((ℬ [ 𝒥 [ j ] ]) ≤[ 𝒪Yₚ ] U) holds
                 θ = ℬ [ 𝒥 [ j ] ]                ≤⟨ ⋁[ 𝒪 Y ]-upper _ j ⟩
                     ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ ＝⟨ c ⁻¹             ⟩ₚ
                     U ■

                 η : (f (ℬ [ 𝒥 [ j ] ]) ≤[ 𝒪Xₚ ] V) holds
                 η = f (ℬ [ 𝒥 [ j ] ])  ≤⟨ μf (ℬ [ 𝒥 [ j ] ] , U) θ ⟩ₗ
                     f U                ≤⟨ p ⟩ₗ
                     V                  ■ₗ

         † : ((⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆) ≤[ poset-of (𝒪 Y) ] g V) holds
         † = ⋁[ 𝒪 Y ]-least ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ (g V , ‡)
              where
               ‡ : (g V is-an-upper-bound-of ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆) holds
               ‡ i = ℬ [ 𝒥 [ i ] ]                         ≤⟨ 𝟏    ⟩
                     ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆          ≤⟨ 𝟐    ⟩
                     ⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 V ⁆  ＝⟨ refl ⟩ₚ
                     g V                                   ■
                      where
                       𝟏 = ⋁[ 𝒪 Y ]-upper ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ i
                       𝟐 = ⋁[ 𝒪 Y ]-least ⁅ ℬ [ i ] ∣ i ε 𝒥 ⁆ (u , ζ)

       † : ((⋁[ 𝒪 X ] ⁅ f (ℬ [ i ]) ∣ (i , _) ∶ 𝒦 V ⁆) ≤[ poset-of (𝒪 X) ] V) holds
       † = ⋁[ 𝒪 X ]-least ⁅ f (ℬ [ i ]) ∣ (i , _) ∶ 𝒦 V ⁆ (V , pr₂)

       β₂ : (U ≤[ 𝒪Yₚ ] g V ⇒ f U ≤[ 𝒪Xₚ ] V) holds
       β₂ p =
        f U                                      ≤⟨ μf (U , g V) p                ⟩
        f (g V)                                  ＝⟨ refl                          ⟩ₚ
        f (⋁[ 𝒪 Y ] ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 V ⁆) ＝⟨ φ ⁅ ℬ [ i ] ∣ (i , _) ∶ 𝒦 V ⁆ ⟩ₚ
        ⋁[ 𝒪 X ] ⁅ f (ℬ [ i ]) ∣ (i , _) ∶ 𝒦 V ⁆ ≤⟨ †                             ⟩
        V                                        ■
         where
          open PosetReasoning 𝒪Xₚ

\end{code}

\begin{code}

 open ContinuousMaps
 open FrameHomomorphismProperties

 aft : (𝒻 : 𝒪Yₚ ─m→ 𝒪Xₚ)
     → has-right-adjoint 𝒻 ↔ is-join-preserving (𝒪 Y) (𝒪 X) (𝒻 .pr₁) holds
 aft 𝒻 = aft-forward 𝒻 , aft-backward 𝒻

 right-adjoint-of : (X ─c→ Y) → 𝒪Xₚ ─m→ 𝒪Yₚ
 right-adjoint-of 𝒽@(h , υ@(_ , _ , jp)) = pr₁ (aft-backward hₘ γ)
  where
   hₘ : 𝒪Yₚ ─m→ 𝒪Xₚ
   hₘ = h , frame-morphisms-are-monotonic (𝒪 Y) (𝒪 X) h υ

   γ : is-join-preserving (𝒪 Y) (𝒪 X) h holds
   γ S = ⋁[ 𝒪 X ]-unique ⁅ h s ∣ s ε S ⁆ (h (⋁[ 𝒪 Y ] S)) (jp S)

 infixl 9 _⁎·_

 _⁎·_ : (X ─c→ Y) → ⟨ 𝒪 X ⟩ → ⟨ 𝒪 Y ⟩
 _⁎·_ f U = right-adjoint-of f .pr₁ U

 open ContinuousMapNotation X Y

 adjunction-inequality-forward : (𝒻@(f , _) : X ─c→ Y)
                               → (U : ⟨ 𝒪 X ⟩) (V : ⟨ 𝒪 Y ⟩)
                               → ((𝒻 ⋆∙ V) ≤[ poset-of (𝒪 X) ] U) holds
                               → (V ≤[ poset-of (𝒪 Y) ] (𝒻 ⁎· U)) holds
 adjunction-inequality-forward 𝒻@(f , ϑ@(_ , _ , p)) U V φ =
  pr₁ (pr₂ (aft-backward 𝒻ₘ γ) V U) φ
   where
    𝒻ₘ : poset-of (𝒪 Y) ─m→ poset-of (𝒪 X)
    𝒻ₘ = f , frame-morphisms-are-monotonic (𝒪 Y) (𝒪 X) f ϑ

    γ : is-join-preserving (𝒪 Y) (𝒪 X) (𝒻ₘ .pr₁) holds
    γ S = ⋁[ 𝒪 X ]-unique ⁅ f V ∣ V ε S ⁆ (f (⋁[ 𝒪 Y ] S)) (p S)

 adjunction-inequality-backward : (𝒻@(f , _) : X ─c→ Y)
                                → (U : ⟨ 𝒪 X ⟩) (V : ⟨ 𝒪 Y ⟩)
                                → (V ≤[ poset-of (𝒪 Y) ] (𝒻 ⁎· U)) holds
                                → ((𝒻 ⋆∙ V) ≤[ poset-of (𝒪 X) ] U) holds
 adjunction-inequality-backward 𝒻@(f , ϑ@(_ , _ , p)) U V φ =
  pr₂ (pr₂ (aft-backward 𝒻ₘ γ) V U) φ
   where
    𝒻ₘ : poset-of (𝒪 Y) ─m→ poset-of (𝒪 X)
    𝒻ₘ = f , frame-morphisms-are-monotonic (𝒪 Y) (𝒪 X) f ϑ

    γ : is-join-preserving (𝒪 Y) (𝒪 X) (𝒻ₘ .pr₁) holds
    γ S = ⋁[ 𝒪 X ]-unique ⁅ f V ∣ V ε S ⁆ (f (⋁[ 𝒪 Y ] S)) (p S)

 f₊-is-right-adjoint-of-f⁺ : (𝒻@(f , _) : X ─c→ Y)
                           → let
                              𝒻ₘ = monotone-map-of (𝒪 Y) (𝒪 X) 𝒻
                             in
                              (𝒻ₘ ⊣ right-adjoint-of 𝒻) holds
 f₊-is-right-adjoint-of-f⁺ 𝒻 V U =
  adjunction-inequality-forward 𝒻 U V , adjunction-inequality-backward 𝒻 U V

 f⁺f₊-is-deflationary : (𝒻 : X ─c→ Y)
                      → let
                         𝒻₊ = right-adjoint-of 𝒻 .pr₁
                        in
                         (U : ⟨ 𝒪 X ⟩)
                        → (𝒻 .pr₁ (𝒻₊ U) ≤[ poset-of (𝒪 X) ] U) holds
 f⁺f₊-is-deflationary 𝒻 = counit 𝒻⁺ₘ 𝒻₊ₘ (f₊-is-right-adjoint-of-f⁺ 𝒻)
  where
   𝒻₊   = right-adjoint-of 𝒻 .pr₁
   𝒻₊ₘ  = right-adjoint-of 𝒻
   𝒻⁺ₘ  = monotone-map-of (𝒪 Y) (𝒪 X) 𝒻

 f₊-preserves-binary-meets : (𝒻@(f , _) : X ─c→ Y)
                           → (U V : ⟨ 𝒪 X ⟩)
                           → let
                              𝒻₊ = right-adjoint-of 𝒻 .pr₁
                             in
                              𝒻₊ (U ∧[ 𝒪 X ] V) ＝ 𝒻₊ U ∧[ 𝒪 Y ] 𝒻₊ V
 f₊-preserves-binary-meets 𝒻 U V = ∧[ 𝒪 Y ]-unique †
  where
   open Meets (λ U V → U ≤[ poset-of (𝒪 Y) ] V)

   𝒻₊ = right-adjoint-of 𝒻 .pr₁

   †₁ : (𝒻₊ (U ∧[ 𝒪 X ] V) is-a-lower-bound-of (𝒻₊ U , 𝒻₊ V)) holds
   †₁ = β₁ , β₂
    where
     open PosetReasoning (poset-of (𝒪 X))

     Ⅰ = f⁺f₊-is-deflationary 𝒻 (U ∧[ 𝒪 X ] V)

     β₁ : (𝒻₊ (U ∧[ 𝒪 X ] V) ≤[ poset-of (𝒪 Y) ] (𝒻₊ U)) holds
     β₁ = adjunction-inequality-forward 𝒻 U (𝒻₊ (U ∧[ 𝒪 X ] V)) ※
      where
       ※ : (𝒻 ⋆∙ 𝒻₊ (U ∧[ 𝒪 X ] V) ≤[ poset-of (𝒪 X) ] U) holds
       ※ = 𝒻 ⋆∙ 𝒻₊ (U ∧[ 𝒪 X ] V)     ≤⟨ Ⅰ ⟩
           U ∧[ 𝒪 X ] V               ≤⟨ Ⅱ ⟩
           U                          ■
            where
             Ⅱ = ∧[ 𝒪 X ]-lower₁ U V

     β₂ : (𝒻₊ (U ∧[ 𝒪 X ] V) ≤[ poset-of (𝒪 Y) ] (𝒻₊ V)) holds
     β₂ = adjunction-inequality-forward 𝒻 V (𝒻₊ (U ∧[ 𝒪 X ] V)) ※
      where
       ※ : (𝒻 ⋆∙ 𝒻₊ (U ∧[ 𝒪 X ] V) ≤[ poset-of (𝒪 X) ] V) holds
       ※ = 𝒻 ⋆∙ 𝒻₊ (U ∧[ 𝒪 X ] V)     ≤⟨ Ⅰ ⟩
           U ∧[ 𝒪 X ] V               ≤⟨ Ⅱ ⟩
           V                          ■
            where
             Ⅱ = ∧[ 𝒪 X ]-lower₂ U V

   †₂ : ((u , _) : lower-bound (𝒻₊ U , 𝒻₊ V))
      → (u ≤[ poset-of (𝒪 Y) ] 𝒻₊ (U ∧[ 𝒪 X ] V)) holds
   †₂ (u , p , q) = adjunction-inequality-forward 𝒻 (U ∧[ 𝒪 X ] V) u ※
    where
     ♣₁ : (𝒻 ⋆∙ u ≤[ poset-of (𝒪 X) ] U) holds
     ♣₁ = adjunction-inequality-backward 𝒻 U u p

     ♣₂ : (𝒻 ⋆∙ u ≤[ poset-of (𝒪 X) ] V) holds
     ♣₂ = adjunction-inequality-backward 𝒻 V u q

     ※ : (𝒻 ⋆∙ u ≤[ poset-of (𝒪 X) ]  (U ∧[ 𝒪 X ] V)) holds
     ※ = ∧[ 𝒪 X ]-greatest U V (𝒻 ⋆∙ u) ♣₁ ♣₂

   † : (𝒻₊ (U ∧[ 𝒪 X ] V) is-glb-of (𝒻₊ U , 𝒻₊ V)) holds
   † = †₁ , †₂

\end{code}

Added on 2024-05-06.

Monotone equivalences are adjoints.

\begin{code}

 monotone-equivalences-are-adjoints
  : (sₘ@(s , _) : poset-of (𝒪 X) ─m→ poset-of (𝒪 Y))
  → (rₘ@(r , _) : poset-of (𝒪 Y) ─m→ poset-of (𝒪 X))
  → s ∘ r ∼ id
  → r ∘ s ∼ id
  → (rₘ ⊣ sₘ) holds
 monotone-equivalences-are-adjoints (s , 𝓂₁) (r , 𝓂₂) φ ψ U V = † , ‡
  where
   open PosetReasoning 𝒪Xₚ

   † : (r U ≤[ 𝒪Xₚ ] V ⇒ U ≤[ 𝒪Yₚ ] s V) holds
   † p =
    sections-are-order-embeddings (poset-of (𝒪 Y)) (poset-of (𝒪 X)) r s 𝓂₁ φ ※
     where
      ※ : (r U ≤[ 𝒪Xₚ ] r (s V)) holds
      ※ = r U ≤⟨ p ⟩ V ＝⟨ ψ V ⁻¹ ⟩ₚ r (s V) ■

   ‡ : (U ≤[ 𝒪Yₚ ] s V ⇒ r U ≤[ 𝒪Xₚ ] V) holds
   ‡ p = r U ≤⟨ 𝓂₂ (U , _) p ⟩ r (s V) ＝⟨ ψ V ⟩ₚ V ■

\end{code}

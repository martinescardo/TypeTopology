J. A. Carr 8 July 2025.

The untruncated form of the at-most-two elements is equivalent
to the statement that Aut Ω has exactly 1 or 2 elements
(and hence every element is either identity or negation)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.DiscreteAndSeparated
open import TypeTopology.SigmaDiscreteAndTotallySeparated
open import UF.Equiv hiding (_≅_)
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.Subsingletons
open import Fin.Type
open import Fin.Topology
open import Fin.Pigeonhole

module Higgs.UntruncatedAtMostTwo
        {𝓤 : Universe}
        (fe : Fun-Ext)
        (pe : propext 𝓤)
        (pt : propositional-truncations-exist)
       where

open import Higgs.Rigidity fe pe
open import Higgs.InvolutionTheorem fe pe
open import Higgs.AutomorphismsOfOmegaWEM fe pe pt

open Conjunction
open Implication fe
open Universal fe

\end{code}

Assuming function extensionality, having an untruncated pigeonhole principle
reflects discreteness to the codomain.

The core method is to note that the pidgeonhole function must respect equality
of functions, so we produce a pair of functions, where equality of their results
holds if and only if the two elements of the codomain are equal.

\begin{code}

constantly : {𝓤 𝓥 : Universe}
           → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
           → Y → X → Y
constantly y _ = y

almost-constantly-inner : {𝓤 𝓥 : Universe}
                  → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → (x' : X) → Y → Y → (x : X)
                  → ((x' ＝ x) + (x' ≠ x))
                  → Y
almost-constantly-inner _ y' y _ (inl _) = y'
almost-constantly-inner _ y' y _ (inr _) = y

almost-constantly : {𝓤 𝓥 : Universe}
                  → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → is-discrete X
                  → X → Y → Y → X
                  → Y
almost-constantly X-discrete x' y' y x =
 almost-constantly-inner x' y' y x (X-discrete x' x)

almost-constantly-eq : {𝓤 𝓥 : Universe}
                     → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                     → (X-discrete : is-discrete X)
                     → (x : X)
                     → (y' y : Y)
                     → almost-constantly X-discrete x y' y x ＝ y'
almost-constantly-eq X-discrete x y' y =
 almost-constantly X-discrete x y' y x               ＝⟨refl⟩
 almost-constantly-inner x y' y x (X-discrete x x)   ＝⟨ I ⟩
 almost-constantly-inner x y' y x (inl refl)         ＝⟨refl⟩
 y'                                                  ∎
 where
  I : almost-constantly-inner x y' y x (X-discrete x x)
      ＝ almost-constantly-inner x y' y x (inl refl)
  I = ap (almost-constantly-inner x y' y x)
         (discrete-inl-refl X-discrete x)

almost-constantly-neq : {𝓤 𝓥 : Universe}
                      → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                      → (X-discrete : is-discrete X)
                      → (x' x : X)
                      → (y' y : Y)
                      → (x' ≠ x)
                      → almost-constantly X-discrete x' y' y x ＝ y
almost-constantly-neq X-discrete x' x y' y ν =
 almost-constantly X-discrete x' y' y x               ＝⟨refl⟩
 almost-constantly-inner x' y' y x (X-discrete x' x)  ＝⟨ I ⟩
 almost-constantly-inner x' y' y x (inr ν)            ＝⟨refl⟩
 y                                                    ∎
 where
  I :  almost-constantly-inner x' y' y x (X-discrete x' x)
       ＝ almost-constantly-inner x' y' y x (inr ν)
  I = ap (almost-constantly-inner x' y' y x)
         (discrete-inr fe X-discrete x' x ν)


almost-constantly-is-constant
 : {𝓤 𝓥 : Universe}
 → {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
 → (X-discrete : is-discrete X)
 → (x' : X)
 → (y y' : Y)
 → y ＝ y'
 → constantly y ＝ almost-constantly X-discrete x' y' y
almost-constantly-is-constant {_} {_} {X} {Y} X-discrete x' y _ refl = dfunext fe III
 where
  I : constantly y x' ＝ y
  I = refl

  II : (x : X)
     → ((x' ＝ x) + (x' ≠ x))
     → almost-constantly X-discrete x' y y x ＝ y
  II _ (inl refl) = almost-constantly-eq X-discrete x' y y
  II x (inr ν) = almost-constantly-neq X-discrete x' x y y ν

  III : (x : X) → constantly y x' ＝ almost-constantly X-discrete x' y y x
  III x = I ∙ II x (X-discrete x' x) ⁻¹


at-most-discrete-gives-discrete
 : {𝓤 𝓥 : Universe}
 → (X : 𝓤 ̇) (Y : 𝓥 ̇)
 → is-discrete X
 → ((f : X → Y) → f has-a-repetition)
 → is-discrete Y
at-most-discrete-gives-discrete X Y X-discrete f-ph y y' = V VI
 where

  repeat-indices : (X → Y)
                 → X × X
  repeat-indices f =
    (λ (x , x' , _) → (x , x'))
    (f-ph f)

  repeat-is-repeat : (f : X → Y)
                   → let (x , x') = repeat-indices f
                     in f x ＝ f x'
  repeat-is-repeat f =
    let (x , x' , _ , pf) = f-ph f
    in pf

  repeat-distinct : (f : X → Y)
                  → let (x , x') = repeat-indices f
                    in x ≠ x'
  repeat-distinct f =
    let (x , x' , pf , _) = f-ph f
    in pf

  f₁ = constantly y
  ix₁ = repeat-indices f₁
  f₂ = almost-constantly X-discrete (pr₁ ix₁) y' y
  ix₂ = repeat-indices f₂

  I : y ＝ y' → ix₁ ＝ ix₂
  I e = ap repeat-indices
           (almost-constantly-is-constant X-discrete (pr₁ ix₁) y y' e)

  II : (x : X)
     → (pr₁ ix₁ ≠ x)
     → y ＝ f₂ x
  II x ne = almost-constantly-neq X-discrete (pr₁ ix₁) x y' y ne ⁻¹

  III : f₂ (pr₁ ix₁) ＝ y'
  III = almost-constantly-eq X-discrete (pr₁ ix₁) y' y

  IV : ix₁ ＝ ix₂ → y ＝ y'
  IV e =
   y                            ＝⟨ II (pr₂ ix₁) (repeat-distinct f₁) ⟩
   f₂ (pr₂ ix₁)                 ＝⟨ ap (f₂ ∘ pr₂) e ⟩
   f₂ (pr₂ ix₂)                 ＝⟨refl⟩
   f₂ (pr₂ (repeat-indices f₂)) ＝⟨ repeat-is-repeat f₂ ⁻¹ ⟩
   f₂ (pr₁ (repeat-indices f₂)) ＝⟨refl⟩
   f₂ (pr₁ ix₂)                 ＝⟨ ap (f₂ ∘ pr₁) (e ⁻¹) ⟩
   f₂ (pr₁ ix₁)                 ＝⟨ III ⟩
   y'                           ∎

  V : is-decidable (ix₁ ＝ ix₂) → is-decidable (y ＝ y')
  V (inl e) = inl (IV e)
  V (inr ne) = inr (ne ∘ I)

  VI : is-decidable (ix₁ ＝ ix₂)
  VI = ×-is-discrete X-discrete X-discrete ix₁ ix₂

\end{code}

We may write the untruncated form of the at-most-2 lemma in this form

\begin{code}

at-most-two-is-pigeonhole
 : {𝓤 : Universe}
 → {X : 𝓤 ̇}
 → ((x y z : X) → (z ＝ x) + (x ＝ y) + (y ＝ z))
 → (f : Fin 3 → X)
 → f has-a-repetition
at-most-two-is-pigeonhole at-most-2 f = II I
 where
  v1 v2 v3 : Fin 3
  v1 = inr ⋆
  v2 = inl (inr ⋆)
  v3 = inl (inl (inr ⋆))

  true-when-eq : Fin 3
               → Fin 3
               → 𝓤 ⁺ ̇
  true-when-eq (inl (inl _)) (inl (inl _)) = 𝟙
  true-when-eq (inl (inl _)) (inl (inr _)) = 𝟘
  true-when-eq (inl (inl _)) (inr _) = 𝟘

  true-when-eq (inl (inr _)) (inl (inl _)) = 𝟘
  true-when-eq (inl (inr _)) (inl (inr _)) = 𝟙
  true-when-eq (inl (inr _)) (inr _) = 𝟘

  true-when-eq (inr _) (inl (inl _)) = 𝟘
  true-when-eq (inr _) (inl (inr _)) = 𝟘
  true-when-eq (inr _) (inr _) = 𝟙

  v3-not-1 : v3 ≠ v1
  v3-not-1 e = 𝟘-elim (transport (true-when-eq v3) e ⋆)
  v1-not-2 : v1 ≠ v2
  v1-not-2 e = 𝟘-elim (transport (true-when-eq v1) e ⋆)
  v2-not-3 : v2 ≠ v3
  v2-not-3 e = 𝟘-elim (transport (true-when-eq v2) e ⋆)

  I : (f v3 ＝ f v1) + (f v1 ＝ f v2) + (f v2 ＝ f v3)
  I = at-most-2 (f v1) (f v2) (f v3)

  II : (f v3 ＝ f v1) + (f v1 ＝ f v2) + (f v2 ＝ f v3)
     → f has-a-repetition
  II (inl e31)       = ( v3 , v1 , v3-not-1 , e31 )
  II (inr (inl e12)) = ( v1 , v2 , v1-not-2 , e12 )
  II (inr (inr e23)) = ( v2 , v3 , v2-not-3 , e23 )

aut-Ω-discrete-has-em
 : is-discrete (Aut Ω)
 → (𝕗 : Aut Ω)
 → (𝕗 ＝ 𝕚𝕕) + (𝕗 ≠ 𝕚𝕕)
aut-Ω-discrete-has-em aut-disc 𝕗 = aut-disc 𝕗 𝕚𝕕

untruncated-at-most-two-iff-em
 : ((f g h : Aut Ω) → (h ＝ f) + (f ＝ g) + (g ＝ h))
 ↔ ((𝕗 : Aut Ω) → (𝕗 ＝ 𝕚𝕕) + (𝕗 ≠ 𝕚𝕕))
untruncated-at-most-two-iff-em = (FW , BW)
 where
  FW : ((f g h : Aut Ω) → (h ＝ f) + (f ＝ g) + (g ＝ h))
     → ((𝕗 : Aut Ω) → (𝕗 ＝ 𝕚𝕕) + (𝕗 ≠ 𝕚𝕕))
  FW at-most-two = aut-Ω-discrete-has-em
   (at-most-discrete-gives-discrete
    (Fin 3) (Aut Ω)
    Fin-is-discrete
    (at-most-two-is-pigeonhole at-most-two))

  I : {f g : Aut Ω}
    → (f ≠ 𝕚𝕕)
    → (g ≠ 𝕚𝕕)
    → (f ＝ g)
  I {f} f-not g-not = ((not-id-is-not f-not em) ∙ (not-id-is-not g-not em) ⁻¹)
   where
    em = Ω-automorphism-distinct-from-𝕚𝕕-gives-EM (f , f-not)

  II : {f g h : Aut Ω}
     → ((f ＝ 𝕚𝕕) + (f ≠ 𝕚𝕕))
     → ((g ＝ 𝕚𝕕) + (g ≠ 𝕚𝕕))
     → ((h ＝ 𝕚𝕕) + (h ≠ 𝕚𝕕))
     → (h ＝ f) + (f ＝ g) + (g ＝ h)
  II (inl  ef) (inl  eg) (_      ) = inr (inl (ef ∙ eg ⁻¹))
  II (inl  _ ) (inr neg) (inr neh) = inr (inr (I neg neh))
  II (inl  ef) (inr neg) (inl  eh) = inl (eh ∙ ef ⁻¹)
  II (inr  _ ) (inl  eg) (inl  eh) = inr (inr (eg ∙ eh ⁻¹))
  II (inr nef) (inr neg) (_      ) = inr (inl (I nef neg))
  II (inr nef) (inl  _ ) (inr neh) = inl (I neh nef)

  BW : ((𝕗 : Aut Ω) → (𝕗 ＝ 𝕚𝕕) + (𝕗 ≠ 𝕚𝕕))
     → ((f g h : Aut Ω) → (h ＝ f) + (f ＝ g) + (g ＝ h))
  BW em f g h = II (em f) (em g) (em h)


\end{code}

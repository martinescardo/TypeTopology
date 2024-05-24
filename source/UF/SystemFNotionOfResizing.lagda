---
title:        System F Resizing considered as an axiom
author:       Ayberk Tosun and Sam Speight
date-started: 2024-05-21
---

This module contains some notes from various discussions with Sam Speight.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module UF.SystemFNotionOfResizing
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import InjectiveTypes.Resizing
open import MLTT.Spartan
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Logic
open import UF.NotNotStablePropositions
open import UF.Retracts
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe

\end{code}

\section{Introduction}

One can consider System F resizing in a universe polymorphic form, but we think
this should be inconsistent due to some form of Girard’s Paradox. This is
because it gives nested impredicative universes which is known to be
inconsistent. However, there are lots of details to check here.

\begin{code}

Generalized-System-F-Resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺  ̇
Generalized-System-F-Resizing 𝓤 𝓥 =
 (A : 𝓤 ⊔ 𝓥  ̇) → (B : A → 𝓤  ̇) → (Π x ꞉ A , B x) is 𝓤 small

\end{code}

TODO: prove that this generalized form is inconsistent.


The special case of this notion of resizing where we pick `𝓤 := 𝓤₀` and
`𝓥 := 𝓤₁` should be consistent.

\begin{code}

System-F-Resizing : 𝓤₂  ̇
System-F-Resizing =
 (A : 𝓤₁  ̇) → (B : A → 𝓤₀  ̇) → (Π x ꞉ A , B x) is 𝓤₀ small

\end{code}

\section{Propositional System F resizing}

One could also consider the propositional form of this notion of resizing.

\begin{code}

Propositional-System-F-Resizing : 𝓤₂  ̇
Propositional-System-F-Resizing =
 (A : 𝓤₁  ̇) →
  (P : A → Ω 𝓤₀) →
   (Ɐ x ꞉ A , P x) holds is 𝓤₀ small

system-F-resizing-implies-prop-system-F-resizing
 : System-F-Resizing → Propositional-System-F-Resizing
system-F-resizing-implies-prop-system-F-resizing 𝕣 A P = 𝕣 A (_holds ∘ P)

\end{code}

The propositional version is of course trivially implied by propositional
resizing.

\begin{code}

prop-resizing-implies-prop-f-resizing
 : propositional-resizing 𝓤₁ 𝓤₀
 → Propositional-System-F-Resizing
prop-resizing-implies-prop-f-resizing 𝕣 A P = 𝕣 (Π x ꞉ A , P x holds) †
 where
  † : is-prop (Π x ꞉ A , P x holds)
  † = holds-is-prop (Ɐ x ꞉ A , P x)

\end{code}

\section{System F resizing implies Ω¬¬-resizing}

We now prove that propositional System F resizing implies `Ω¬¬`-resizing.

First, we define the following abbreviation for asserting a ¬¬-stable
proposition.

\begin{code}

_holds· : {𝓤 : Universe} → Ω¬¬ 𝓤 → 𝓤  ̇
_holds· (P , f) = P holds

\end{code}

We also define a version of the `resize-up` map on ¬¬-stable propositions.

\begin{code}

resize-up-¬¬ : Ω¬¬ 𝓤₀ → Ω¬¬ 𝓤₁
resize-up-¬¬ (P , φ) = P⁺ , γ
 where
  † : P holds is 𝓤₁ small
  † = resize-up (P holds)

  e : P holds ≃ resized (P holds) †
  e = ≃-sym (resizing-condition †)

  P⁺ : Ω 𝓤₁
  P⁺ = resized (P holds) † , equiv-to-prop (≃-sym e) (holds-is-prop P)

  s : (P ⇒ P⁺) holds
  s = ⌜ e ⌝

  r : (P⁺ ⇒ P) holds
  r = ⌜ ≃-sym e ⌝

  β : ¬¬ (P⁺ holds) → ¬¬ (P holds)
  β f p = f (p ∘ r)

  γ : ¬¬-stable (P⁺ holds)
  γ f = φ (β f) , ⋆

\end{code}

We now prove that propositional System F resizing implies Ω¬¬-resizing.

\begin{code}

prop-F-resizing-implies-Ω¬¬-resizing : Propositional-System-F-Resizing
                                     → Ω¬¬-Resizing 𝓤₁ 𝓤₁
prop-F-resizing-implies-Ω¬¬-resizing 𝕣 = Ω¬¬ 𝓤₀ , †
 where

\end{code}

Note that we denote by `𝕣` the assumption of propositional System F resizing.

The map going upward is `resize-up-¬¬`.

\begin{code}

  s : Ω¬¬ 𝓤₀ → Ω¬¬ 𝓤₁
  s = resize-up-¬¬

\end{code}

We now define the map going downward which we call `r`. We first give the
preliminary version in `r₀`, without the proof of ¬¬-stability, which we then
package up with the proof of ¬¬-stability in `r`.

\begin{code}

  r₀ : Ω¬¬ 𝓤₁ → Ω 𝓤₀
  r₀ (P , φ) = resized (¬¬ (P holds)) γ , i
   where
    γ : ¬¬ (P holds) is 𝓤₀ small
    γ = 𝕣 (¬ (P holds)) λ _ → ⊥

    P⁻ : 𝓤₀  ̇
    P⁻ = resized (¬¬ (P holds)) γ

    i : is-prop P⁻
    i = equiv-to-prop (resizing-condition γ) (Π-is-prop fe λ _ → 𝟘-is-prop)

  r : Ω¬¬ 𝓤₁ → Ω¬¬ 𝓤₀
  r (P , φ) = r₀ (P , φ) , ψ
   where
    γ : ¬¬ (P holds) is 𝓤₀ small
    γ = 𝕣 (¬ (P holds)) λ _ → ⊥

    P⁻ : 𝓤₀  ̇
    P⁻ = resized (¬¬ (P holds)) γ

    f : P holds → P⁻
    f p = ⌜ ≃-sym (resizing-condition γ) ⌝ λ f → 𝟘-elim (f p)

    g : P⁻ → P holds
    g p⁻ = φ (eqtofun (resizing-condition γ) p⁻)

    ψ : ¬¬ P⁻ → P⁻
    ψ q = f (φ nts)
     where
      nts : ¬¬ (P holds)
      nts u = q (λ p⁻ → u (g p⁻))

\end{code}

The proposition `s P` trivially implies `P`.

\begin{code}

  ϑ : (P : Ω¬¬ 𝓤₀) → s P holds· → P holds·
  ϑ P (p , ⋆) = p

\end{code}

The converse.

\begin{code}

  ι : (P : Ω¬¬ 𝓤₀) → P holds· → (s P) holds·
  ι P p = (p , ⋆)

\end{code}

The proposition `r P` implies `P`.

\begin{code}

  μ : (P : Ω¬¬ 𝓤₁) → (r P) holds· → P holds·
  μ (P , φ) p = ξ (ψ λ u → 𝟘-elim (u p))
   where
    β : ¬ (P holds) is 𝓤₀ small
    β = 𝕣 (P holds) (λ _ → ⊥)

    γ : ¬¬ (P holds) is 𝓤₀ small
    γ = 𝕣 (¬ (P holds)) λ _ → ⊥

    P⁻ : 𝓤₀  ̇
    P⁻ = resized (¬¬ (P holds)) γ

    ζ : P holds → P⁻
    ζ p = ⌜ ≃-sym (resizing-condition γ) ⌝ λ f → 𝟘-elim (f p)

    ξ : P⁻ → P holds
    ξ p⁻ = φ (eqtofun (resizing-condition γ) p⁻)

    ψ : ¬¬ P⁻ → P⁻
    ψ q = ζ (φ †)
     where
      † : ¬¬ (P holds)
      † u = q (λ p⁻ → u (ξ p⁻))

\end{code}

The converse of this implication.

\begin{code}

  ν : (P : Ω¬¬ 𝓤₁) → P holds· → (r P) holds·
  ν (P , φ) p = ⌜ ≃-sym (resizing-condition γ) ⌝ λ f → 𝟘-elim (f p)
   where
    γ : ¬¬ (P holds) is 𝓤₀ small
    γ = 𝕣 (¬ (P holds)) λ _ → ⊥

\end{code}

We now combine these implications to get implications

  - `r (s P) ⇔ P`, for every ¬¬-stable 𝓤₀-proposition `P`
  - `s (r P) ⇔ P`, for every ¬¬-stable 𝓤₁-proposition `P`.

\begin{code}

  rs₁ : (P : Ω¬¬ 𝓤₀) → r (s P) holds· → P holds·
  rs₁ P = ϑ P ∘ μ (s P)

  rs₂ : (P : Ω¬¬ 𝓤₀) → P holds· → r (s P) holds·
  rs₂ P = ν (s P) ∘ ι P

  sr₁ : (P : Ω¬¬ 𝓤₁) → s (r P) holds· → P holds·
  sr₁ P = μ P ∘ ϑ (r P)

  sr₂ : (P : Ω¬¬ 𝓤₁) → P holds· → s (r P) holds·
  sr₂ P = ι (r P) ∘ ν P

\end{code}

It follows easily from this then `Ω¬¬ 𝓤₀` is equivalent to `Ω¬¬ 𝓤₁`.

\begin{code}

  † : Ω¬¬ 𝓤₀ ≃ Ω¬¬ 𝓤₁
  † = s , qinvs-are-equivs s (r , †₁ , †₂)
   where
    †₁ : (r ∘ resize-up-¬¬) ∼ id
    †₁ (P , f) =
     to-subtype-＝
      (λ P → being-¬¬-stable-is-prop fe (holds-is-prop P))
      (⇔-gives-＝ pe _ _ (holds-gives-equal-⊤ pe fe _ (rs₁ (P , f) , rs₂ (P , f))))

    †₂ : resize-up-¬¬ ∘ r ∼ id
    †₂ (P , f) =
     to-subtype-＝
      (λ Q → being-¬¬-stable-is-prop fe (holds-is-prop Q))
      (⇔-gives-＝ pe _ P (holds-gives-equal-⊤ pe fe _ (sr₁ (P , f) , sr₂ (P , f))))

\end{code}

One might be tempted to consider Σ-resizing, but this immediately gives that 𝓤₀
is 𝓤₀-small (thanks to Jon Sterling who pointed this out in a code review).

\begin{code}

Σ-Resizing : 𝓤₂  ̇
Σ-Resizing = (A : 𝓤₁  ̇) → (B : A → 𝓤₀  ̇) → (Σ x ꞉ A , B x) is 𝓤₀ small

Σ-resizing-gives-𝓤₀-is-𝓤₀-small : Σ-Resizing → (𝓤₀  ̇) is 𝓤₀ small
Σ-resizing-gives-𝓤₀-is-𝓤₀-small ψ = resized ((𝓤₀  ̇) × 𝟙 {𝓤₀}) † , e
 where
  † : ((𝓤₀  ̇) × 𝟙 {𝓤₀}) is 𝓤₀ small
  † = ψ (𝓤₀  ̇) (λ _ → 𝟙 {𝓤₀})

  Ⅰ : resized ((𝓤₀  ̇) × 𝟙 {𝓤₀}) † ≃ (𝓤₀  ̇) × 𝟙 {𝓤₀}
  Ⅰ = resizing-condition †

  s : resized ((𝓤₀  ̇) × 𝟙 {𝓤₀}) † → 𝓤₀  ̇
  s = pr₁ ∘ ⌜ Ⅰ ⌝

  r : 𝓤₀  ̇ → resized ((𝓤₀  ̇) × 𝟙 {𝓤₀}) †
  r A = ⌜ ≃-sym Ⅰ ⌝ (A , ⋆)

  e : resized ((𝓤₀  ̇) × 𝟙 {𝓤₀}) † ≃ 𝓤₀  ̇
  e = resized ((𝓤₀  ̇) × 𝟙 {𝓤₀}) †  ≃⟨ Ⅰ ⟩
      (𝓤₀  ̇) × 𝟙 {𝓤₀}              ≃⟨ Ⅱ ⟩
      𝓤₀  ̇                         ■
       where
        Ⅱ = 𝟙-rneutral {𝓤₁} {𝓤₀} {Y = (𝓤₀  ̇)}

\end{code}

The version of this notion of resizing with truncation, which we denote
∃-resizing is equivalent to propositional resizing.

\begin{code}

∃-Resizing : 𝓤₂  ̇
∃-Resizing = (A : 𝓤₁  ̇) → (B : A → 𝓤₀  ̇) → (Ǝ x ꞉ A , B x) holds is 𝓤₀ small

prop-resizing-implies-∃-resizing : propositional-resizing 𝓤₁ 𝓤₀ → ∃-Resizing
prop-resizing-implies-∃-resizing 𝕣 A B =
 𝕣 ((Ǝ x ꞉ A , B x) holds) (holds-is-prop (Ǝ x ꞉ A , B x))

\end{code}

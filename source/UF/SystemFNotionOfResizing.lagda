--------------------------------------------------------------------------------
title:        System F Resizing considered as an axiom
authors:      ["Sam Speight", "Ayberk Tosun"]
date-started: 2024-05-15
--------------------------------------------------------------------------------

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
open import UF.Logic
open import UF.NotNotStablePropositions
open import UF.Retracts
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open AllCombinators pt fe

\end{code}

One can consider System F resizing in a universe polymorphic form, but we think
this should be inconsistent due to some form of Girard’s Paradox, as it gives
nested impredicative universes which is known to be inconsistent. However,
there are lots of details to check here. It would be nice to have this paradox
in TypeTopology.

\begin{code}

Generalized-System-F-Resizing : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺  ̇
Generalized-System-F-Resizing 𝓤 𝓥 =
 (A : 𝓤 ⊔ 𝓥  ̇) → (B : A → 𝓤  ̇) → (Π x ꞉ A , B x) is 𝓤 small

\end{code}

The special case of this notion of resizing where we pick `𝓤 := 𝓤₀` and
`𝓥 := 𝓤₁` should be consistent.

\begin{code}

System-F-Resizing : 𝓤₂  ̇
System-F-Resizing =
 (A : 𝓤₁  ̇) → (B : A → 𝓤₀  ̇) → (Π x ꞉ A , B x) is 𝓤₀ small

\end{code}

One could also consider the propositional form of this notion of resizing.

\begin{code}

Propositional-System-F-Resizing : 𝓤₂  ̇
Propositional-System-F-Resizing =
 (A : 𝓤₁  ̇) →
  (P : A → Ω 𝓤₀) →
   (Ɐ x ꞉ A , P x) holds is 𝓤₀ small

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

TODO: prove that propositional System F resizing implies `Ω¬¬`-resizing.

\begin{code}

_holds· : {𝓤 : Universe} → Ω¬¬ 𝓤 → 𝓤  ̇
_holds· (P , f) = P holds

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

prop-F-resizing-implies-Ω¬¬-resizing : Propositional-System-F-Resizing
                                     → Ω¬¬-Resizing 𝓤₁ 𝓤₁
prop-F-resizing-implies-Ω¬¬-resizing 𝕣 = Ω¬¬ 𝓤₀ , †
 where
  s : Ω¬¬ 𝓤₀ → Ω¬¬ 𝓤₁
  s = resize-up-¬¬

  r : Ω¬¬ 𝓤₁ → Ω¬¬ 𝓤₀
  r (P , φ) = (resized (¬¬ (P holds)) γ , i) , ψ
   where
    β : ¬ (P holds) is 𝓤₀ small
    β = 𝕣 (P holds) (λ _ → ⊥)

    γ : ¬¬ (P holds) is 𝓤₀ small
    γ = 𝕣 (¬ (P holds)) λ _ → ⊥

    P⁻ : 𝓤₀  ̇
    P⁻ = resized (¬¬ (P holds)) γ

    i : is-prop P⁻
    i = equiv-to-prop (resizing-condition γ) (Π-is-prop fe λ _ → 𝟘-is-prop)

    f : P holds → P⁻
    f p = ⌜ ≃-sym (resizing-condition γ) ⌝ λ f → 𝟘-elim (f p)

    g : P⁻ → P holds
    g p⁻ = φ (eqtofun (resizing-condition γ) p⁻)

    ψ : ¬¬ P⁻ → P⁻
    ψ q = f (φ nts)
     where
      nts : ¬¬ (P holds)
      nts u = q (λ p⁻ → u (g p⁻))

  foo : (P : Ω¬¬ 𝓤₀) → s P holds· → P holds·
  foo P (p , ⋆) = p

  bar : (P : Ω¬¬ 𝓤₀) → P holds· → (s P) holds·
  bar P p = p , ⋆

  baz : (P : Ω¬¬ 𝓤₁) → (r P) holds· → P holds·
  baz (P , f) p = {!!}

  sr : (P : Ω¬¬ 𝓤₀) → r (s P) holds· → P holds·
  sr (P , f) = {!!}

  † : Ω¬¬ 𝓤₀ ≃ Ω¬¬ 𝓤₁
  † = s , qinvs-are-equivs s (r , †₁ , †₂)
   where
    †₁ : (r ∘ resize-up-¬¬) ∼ id
    †₁ (P , f) =
     to-subtype-＝
      (λ P → being-¬¬-stable-is-prop fe (holds-is-prop P))
      (⇔-gives-＝ pe _ _ (holds-gives-equal-⊤ pe fe _ (goal₁ , goal₂)))
       where
        goal₁ : r (s (P , f)) holds· → P holds
        goal₁ = sr (P , f)

        goal₂ : P holds → r (s (P , f)) holds·
        goal₂ p = {!!}

    †₂ : resize-up-¬¬ ∘ r ∼ id
    †₂ = {!!}

\end{code}

We could also consider Σ-resizing.

\begin{code}

Σ-Resizing : 𝓤₂  ̇
Σ-Resizing = (A : 𝓤₁  ̇) → (B : A → 𝓤₀  ̇) → (Σ x ꞉ A , B x) is 𝓤₀ small

\end{code}

Similarly, ∃-resizing.

\begin{code}

∃-Resizing : 𝓤₂  ̇
∃-Resizing = (A : 𝓤₁  ̇) → (B : A → 𝓤₀  ̇) → (Ǝ x ꞉ A , B x) holds is 𝓤₀ small

\end{code}

\begin{code}

prop-resizing-implies-∃-resizing : propositional-resizing 𝓤₁ 𝓤₀ → ∃-Resizing
prop-resizing-implies-∃-resizing 𝕣 A B =
 𝕣 ((Ǝ x ꞉ A , B x) holds) (holds-is-prop (Ǝ x ꞉ A , B x))

\end{code}

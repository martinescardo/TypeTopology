Andrew Swan, 6th February 2024

Σ-closed reflective subuniverse is one of the three definitions of
modalities given in [1] (Definition 1.3). The aim of this file is
to collect together results about them. For now we just have one
result that is often useful in practice: for Σ-closed universes, we have
not just recursion, but induction.

[1] Rijke, Shulman, Spitters, Modalities in homotopy type theory,
https://doi.org/10.23638/LMCS-16(1:2)2020

\begin{code}
{-# OPTIONS --safe --without-K --exact-split --auto-inline #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import Modal.Subuniverse

module Modal.SigmaClosedReflectiveSubuniverse
 (P : subuniverse 𝓤 𝓥)
 (P-is-reflective : subuniverse-is-reflective P)
 (P-is-sigma-closed : subuniverse-is-sigma-closed P)
 where
\end{code}

A Σ-closed reflective subuniverse is in particular a reflective
subuniverse, so we first import everything already proved for
reflective subuniverses in general.

\begin{code}
open import Modal.ReflectiveSubuniverse P P-is-reflective public
\end{code}

We can now prove the induction principle. We do this as a direct
proof from the Σ-closed condition, using it together with the
recursion principle to construct a map g : ○ A → Σ a : ○ A, B a and
then using uniqueness to show that composition pr₁ ∘ g is the identity
on ○ A.

\begin{code}
○-induction
 : (fe : funext 𝓤 𝓤)
 → (A : 𝓤 ̇)
 → (B : ○ A → 𝓤 ̇)
 → (B-modal : (α : ○ A) → is-modal (B α))
 → ((a : A) → B (η A a))
 → (α : ○ A) → B α
○-induction fe A B B-modal f α = transport B (happly h α) (pr₂ (g α))
 where
  g : ○ A → Σ B
  g = ○-rec
       _ _
       (P-is-sigma-closed _ _ (○-is-modal _) B-modal)
       λ a → (η _ a) , (f a)

  h : pr₁ ∘ g ＝ id
  h = ○-rec-ext
       _ _
       (○-is-modal _)
       _ _
       (dfunext fe (λ a → ap pr₁ (○-rec-compute _ _ _ _ a)))
\end{code}

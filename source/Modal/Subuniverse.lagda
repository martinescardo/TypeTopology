Jon Sterling, started 27th Sep 2022
Andrew Swan, 7th Februrary 2024, definition of Σ-closed subuniverse added

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Modal.Subuniverse where

open import MLTT.Spartan
open import UF.Subsingletons
open import UF.Base
open import UF.FunExt
open import UF.Equiv
open import UF.Univalence

subuniverse
 : (𝓤 𝓥 : Universe)
 → (𝓤 ⊔ 𝓥)⁺ ̇
subuniverse 𝓤 𝓥 =
 Σ P ꞉ (𝓤 ̇ → 𝓥 ̇ ),
 Π A ꞉ 𝓤 ̇ ,
 is-prop (P A)

subuniverse-contains
 : subuniverse 𝓤 𝓥
 → 𝓤 ̇
 → 𝓥 ̇
subuniverse-contains P A =
 pr₁ P A

subuniverse-member
 : subuniverse 𝓤 𝓥
 → 𝓤 ⁺ ⊔ 𝓥  ̇
subuniverse-member P =
 Σ (subuniverse-contains P)

reflection-candidate
 : subuniverse 𝓤 𝓥
 → 𝓤 ̇
 → 𝓤 ⁺ ⊔ 𝓥  ̇
reflection-candidate P A =
 Σ A' ꞉ subuniverse-member P ,
 (A → pr₁ A')

is-reflection
 : (P : subuniverse 𝓤 𝓥)
 → (A : 𝓤 ̇)
 → reflection-candidate P A
 → 𝓤 ⁺ ⊔ 𝓥  ̇
is-reflection P A (A' , η) =
 (B : _)
 → subuniverse-contains P B
 → is-equiv λ (f : pr₁ A' → B) → f ∘ η

subuniverse-reflects
 : subuniverse 𝓤 𝓥
 → 𝓤 ̇
 → 𝓤 ⁺ ⊔ 𝓥  ̇
subuniverse-reflects P A =
 Σ A' ꞉ reflection-candidate P A ,
 is-reflection P A A'

subuniverse-is-reflective
 : subuniverse 𝓤 𝓥
 → 𝓤 ⁺ ⊔ 𝓥  ̇
subuniverse-is-reflective P =
 Π (subuniverse-reflects P)

subuniverse-is-replete
 : subuniverse 𝓤 𝓥
 → 𝓤 ⁺ ⊔ 𝓥  ̇
subuniverse-is-replete P =
 (A B : _)
 → A ≃ B
 → subuniverse-contains P B
 → subuniverse-contains P A

univalence-implies-subuniverse-is-replete
 : (ua : is-univalent 𝓤)
 → (P : subuniverse 𝓤 𝓥)
 → subuniverse-is-replete P
univalence-implies-subuniverse-is-replete ua P A B e =
 transport⁻¹
  (subuniverse-contains P)
  (eqtoid ua A B e)

subuniverse-is-sigma-closed
 : (P : subuniverse 𝓤 𝓥)
 → 𝓤 ⁺ ⊔ 𝓥  ̇
subuniverse-is-sigma-closed P =
 (A : _) →
 (B : A → _) →
 pr₁ P A →
 ((a : A) → pr₁ P (B a)) →
 pr₁ P (Σ B)
\end{code}

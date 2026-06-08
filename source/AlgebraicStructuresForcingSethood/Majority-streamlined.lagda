Tom de Jong, 16 & 18 March 2026.
Updated on 8 June 2026 by Tom de Jong to use minimal library imports.

We show that the proof given by Jakub Opršal in
AlgebraicStructuresForcingSethood.Majority factors through a simple lemma about
loop spaces (see the module Ω-trivial-criterion).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module AlgebraicStructuresForcingSethood.Majority-streamlined where

open import MLTT.Universes
open import MLTT.Id
open import UF.Base using
  ( ap₂
  ; ＝-cong
  ; ＝-cong-refl
  ; refl-left-neutral
  ; refl-right-neutral
  ; conjugate-loop )

module _
        (A : 𝓤 ̇ )
        (a₀ b₀ : A)
       where

 Ωᵃ : 𝓤 ̇
 Ωᵃ = a₀ ＝ a₀

 Ωᵇ : 𝓤 ̇
 Ωᵇ = b₀ ＝ b₀

 module Ω-trivial-criterion
         (f                            : Ωᵃ → Ωᵃ → Ωᵇ)
         (γ                            : b₀ ＝ a₀)
         (idempotent-up-to-conjugation : (p : Ωᵃ)
                                       → conjugate-loop γ (f p p) ＝ p)
         (left-nilpotent               : (p : Ωᵃ) → f p refl ＝ refl)
         (right-nilpotent              : (q : Ωᵃ) → f refl q ＝ refl)
         (homomorphism                 : (p q r s : Ωᵃ)
                                       → f (p ∙ r) (q ∙ s) ＝ f p q ∙ f r s)
        where

  nilpotent : (p : Ωᵃ) → f p p ＝ refl
  nilpotent p =
   f p p                   ＝⟨ I    ⟩
   f (p ∙ refl) (refl ∙ p) ＝⟨ II   ⟩
   f p refl ∙ f refl p     ＝⟨ III  ⟩
   refl ∙ refl             ＝⟨ refl ⟩
   refl                    ∎
    where
     I   = (ap₂ f (refl-right-neutral p) refl-left-neutral) ⁻¹
     II  = homomorphism p refl refl p
     III = ap₂ _∙_ (left-nilpotent p) (right-nilpotent p)

  Ω-trivial : (p : Ωᵃ) → p ＝ refl
  Ω-trivial p =
   p                        ＝⟨ (idempotent-up-to-conjugation p) ⁻¹ ⟩
   conjugate-loop γ (f p p) ＝⟨ ap (conjugate-loop γ) (nilpotent p) ⟩
   conjugate-loop γ refl    ＝⟨ ＝-cong-refl γ ⟩
   refl                     ∎

\end{code}

Finally, we show that it applies to Jakub's setting: any type with a ternary
majority operation must be a set.

\begin{code}

open import AlgebraicStructuresForcingSethood.Majority

majorities-only-act-on-sets : (M : 𝓤 ̇ ) (m : M → M → M → M)
                            → ((a b : M) → m b a a ＝ a)
                            → ((a b : M) → m a b a ＝ a)
                            → ((a b : M) → m a a b ＝ a)
                            → (m₀ : M) → (p : m₀ ＝ m₀) → p ＝ refl
majorities-only-act-on-sets M m eq₀ eq₁ eq₂ m₀ =
 Ω-trivial
  M
  m₀
  (m m₀ m₀ m₀)
  f
  idem₁
  side₁-is-p
  side₀-is-refl
  side₂-is-refl
  (λ p q r s → (m'-is-homo p r refl refl q s) ⁻¹)
   where
    open Ω-trivial-criterion
    open type-with-majority M m eq₀ eq₁ eq₂ m₀
    f : (m₀ ＝ m₀) → (m₀ ＝ m₀) → m m₀ m₀ m₀ ＝ m m₀ m₀ m₀
    f p q = m' p refl q

\end{code}

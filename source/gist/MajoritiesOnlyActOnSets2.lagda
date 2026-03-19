Tom de Jong, 16 & 18 March 2026.

We show that the proof given by Jakub Opršal in gist.MajoritiesOnlyActOnSets
factors through a simple lemma about loop spaces (see the module
Ω-trivial-criterion).

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.MajoritiesOnlyActOnSets2 where

open import Agda.Primitive renaming (Set to Type)

\end{code}

To be compatible with Jakub's file, we also build on Martín's file
gist.ThereAreNoHigherSemilattices, but with minimal imports.

\begin{code}

open import gist.ThereAreNoHigherSemilattices
 using (_＝_ ; _∙_ ; refl ; sym ; ap ; ap₂ ; eq-congr)

\end{code}

We introduce a little additional boilerplate on top of our minimal imports.

\begin{code}

_＝⟨_⟩_ : {X : Type} (x : X) {y z : X} → x ＝ y → y ＝ z → x ＝ z
_ ＝⟨ p ⟩ q = p ∙ q

_∎ : {X : Type} (x : X) → x ＝ x
_∎ _ = refl

infix  1 _∎
infixr 0 _＝⟨_⟩_

refl-left-neutral : {X : Type} {x y : X} (p : x ＝ y) → refl ∙ p ＝ p
refl-left-neutral refl = refl

refl-right-neutral : {X : Type} {x y : X} (p : x ＝ y) → p ∙ refl ＝ p
refl-right-neutral refl = refl

module _
        {A : Type}
        {a b : A}
       where

 conjugate-loop : a ＝ b → a ＝ a → b ＝ b
 conjugate-loop p = eq-congr p p

 conjugate-loop-refl : (p : a ＝ b) → conjugate-loop p refl ＝ refl
 conjugate-loop-refl refl = refl

 NB₁ : (p : a ＝ b) (q : a ＝ a) → conjugate-loop p q ＝ (sym p) ∙ q ∙ p
 NB₁ refl q = sym (refl-left-neutral (q ∙ refl) ∙ refl-right-neutral q)

\end{code}

We now present the lemma about trivial loop spaces.

\begin{code}

module _
        (A : Type)
        (a₀ b₀ : A)
       where

 Ωᵃ : Type
 Ωᵃ = a₀ ＝ a₀

 Ωᵇ : Type
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
     I   = sym (ap₂ f (refl-right-neutral p) (refl-left-neutral p))
     II  = homomorphism p refl refl p
     III = ap₂ _∙_ (left-nilpotent p) (right-nilpotent p)

  Ω-trivial : (p : Ωᵃ) → p ＝ refl
  Ω-trivial p =
   p                        ＝⟨ sym (idempotent-up-to-conjugation p) ⟩
   conjugate-loop γ (f p p) ＝⟨ ap (conjugate-loop γ) (nilpotent p) ⟩
   conjugate-loop γ refl    ＝⟨ conjugate-loop-refl γ ⟩
   refl                     ∎

\end{code}

Finally, we show that it applies to Jakub's setting: any type with a ternary
majority operation must be a set.

\begin{code}

open import gist.MajoritiesOnlyActOnSets

majorities-only-act-on-sets : (M : Type) (m : M → M → M → M)
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
  (λ p q r s → sym (m'-is-homo p r refl refl q s))
   where
    open Ω-trivial-criterion
    open type-with-majority M m eq₀ eq₁ eq₂ m₀
    f : (m₀ ＝ m₀) → (m₀ ＝ m₀) → m m₀ m₀ m₀ ＝ m m₀ m₀ m₀
    f p q = m' p refl q

\end{code}

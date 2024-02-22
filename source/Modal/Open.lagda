Andrew Swan, started 12 February 2024

This is an implementation of open modalities. Like the other results
in this directory, it is covered in [1].

[1] Rijke, Shulman, Spitters, Modalities in homotopy type theory,
https://doi.org/10.23638/LMCS-16(1:2)2020


\begin{code}
{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import Modal.Subuniverse

open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.Subsingletons

module Modal.Open

\end{code}

Function extensionality is required for even some quite basic results
about open modalities, so we will assume it throughout.

\begin{code}

 (fe : funext 𝓤 𝓤)
 
\end{code}

There is an open modality for each proposition P. We fix such a
proposition throughout.

\begin{code}

 (P : 𝓤 ̇  )
 (P-is-prop : is-prop P)
 where

open-unit : (A : 𝓤 ̇ ) → A → (P → A)
open-unit A a _ = a

is-open-modal : 𝓤 ̇ → 𝓤 ̇
is-open-modal A = is-equiv (open-unit A)

open-subuniverse : subuniverse 𝓤 𝓤
open-subuniverse =
 is-open-modal , λ A → being-equiv-is-prop'' fe _

\end{code}

The reflection has a very simple description - it just sends A to the
exponential P → A. We then need to check that it is a reflection.

\begin{code}

exponential-is-modal : (A : 𝓤 ̇ ) → is-open-modal (P → A)
exponential-is-modal A =
 ((λ f p → f p p) ,
  (λ f →
   dfunext
    fe
    (λ p → dfunext fe (λ q → ap (λ r → f r q) (P-is-prop _ _))))) ,
 (λ f p → f p p) ,
 (λ f → refl)

exponential-is-reflection
 : (A : 𝓤 ̇ )
 → is-reflection open-subuniverse
  A
  (((P → A) , (exponential-is-modal A)) , λ a _ → a)
exponential-is-reflection A B B-modal =
 qinvs-are-equivs
  _
  ((λ g → pr₁ (pr₂ B-modal) ∘ λ f → g ∘ f) ,
   (λ j → dfunext fe (is-retraction j)) ,
   λ g → dfunext fe (λ a → pr₂ (pr₂ B-modal) (g a)))
 where
  lemma
   : (j : (P → A) → B)
   → (λ f → (j ∘ open-unit A ∘ f)) ∼ (open-unit B) ∘ j
  lemma j f =
   dfunext fe
    (λ z → ap j (dfunext fe (λ z' → ap f (P-is-prop z z'))))

  is-retraction
   : (j : (P → A) → B)
   → pr₁ (pr₂ B-modal) ∘ (λ f → (j ∘ open-unit A ∘ f)) ∼ j
  is-retraction j f =
   pr₁ (pr₂ B-modal) (j ∘ open-unit A ∘ f)
    ＝⟨ ap (pr₁ (pr₂ B-modal)) (lemma j f) ⟩
   pr₁ (pr₂ B-modal) (open-unit B (j f))
    ＝⟨ pr₂ (pr₂ B-modal) (j f) ⟩
   j f ∎
 
open-is-reflective : subuniverse-is-reflective open-subuniverse
open-is-reflective A =
 (((P → A) , (exponential-is-modal A)) , (open-unit A)) ,
 exponential-is-reflection A

\end{code}

We can show moreover that the reflective subuniverse is replete,
using only function extensionality rather than univalence, and that it
is Σ-closed. This confirms that it is a modality.

\begin{code}

open-is-replete : subuniverse-is-replete open-subuniverse
open-is-replete A B e B-modal =
 ≃-2-out-of-3-left
  (pr₂ (→cong' fe fe e))
  (∘-is-equiv ⌜ e ⌝-is-equiv B-modal)
 
open-is-sigma-closed : subuniverse-is-sigma-closed open-subuniverse
open-is-sigma-closed A B A-modal B-modal =
 ≃-2-out-of-3-left
  ⌜ ΠΣ-distr-≃ ⌝-is-equiv
  ⌜ unit-equiv ⌝-is-equiv
 where
  unit-equiv : Σ B ≃ (Σ f ꞉ (P → A) , ((z : P) → B (f z)))
  unit-equiv =
   Σ-bicong _ _
    ((open-unit A) , A-modal)
    (λ a → (open-unit (B a)) , (B-modal a))

\end{code}

We add a useful lemma for the absoluteness of compactness: if P is a
true proposition then the open modality is trivial, in the sense that
all types are modal.

\begin{code}

P-true-implies-all-modal
 : (z : P) → (A : 𝓤 ̇ ) → is-open-modal A
P-true-implies-all-modal z A =
 qinvs-are-equivs
  (open-unit A)
  ((λ f → f z) ,
   ((λ a → refl) ,
   (λ f → dfunext fe (λ z' → ap f (P-is-prop z z')))))

\end{code}

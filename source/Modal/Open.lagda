Andrew Swan, started 12 February 2024

This is an implementation of open modalities.

\begin{code}

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
exponential P → A.

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
 ((λ g → pr₁ (pr₂ B-modal) ∘ λ f → g ∘ f) ,
  λ g → dfunext fe (λ a → pr₂ (pr₂ B-modal) (g a))) ,
 (λ g → pr₁ (pr₂ B-modal) ∘ λ f → g ∘ f) ,
  (λ h → dfunext fe (λ f → is-retraction h f))
 where
  lemma
   : (h : (P → A) → B)
   → (λ f → (h ∘ open-unit A ∘ f)) ∼ (open-unit B) ∘ h
  lemma h f =
   dfunext fe
    (λ z → ap h (dfunext fe (λ z' → ap f (P-is-prop z z'))))

  is-retraction
   : (h : (P → A) → B)
   → pr₁ (pr₂ B-modal) ∘ (λ f → (h ∘ open-unit A ∘ f)) ∼ h
  is-retraction h f =
   pr₁ (pr₂ B-modal) (h ∘ open-unit A ∘ f)
    ＝⟨ ap (pr₁ (pr₂ B-modal)) (lemma h f) ⟩
   pr₁ (pr₂ B-modal) (open-unit B (h f))
    ＝⟨ pr₂ (pr₂ B-modal) (h f) ⟩
   h f ∎
 
open-is-reflective : subuniverse-is-reflective open-subuniverse
open-is-reflective A =
 (((P → A) , (exponential-is-modal A)) , (open-unit A)) ,
 exponential-is-reflection A

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

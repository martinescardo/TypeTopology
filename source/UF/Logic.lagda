---
title:        Logic
author:       Martín Escardó and Ayberk Tosun
date-started: 2021-03-10
---

Based in part by the `Cubical.Functions.Logic` module of `agda/cubical`.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Logic where

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.Sets

\end{code}

\section{Negation}

\begin{code}

module Negation (fe : funext 𝓤 𝓤₀) where

 ⇁_ : Ω 𝓤 → Ω 𝓤
 ⇁_ = not fe

 ⇁⇁_ : Ω 𝓤 → Ω 𝓤
 ⇁⇁ p = ⇁(⇁ p)

\end{code}

\section{Conjunction}

\begin{code}

module Conjunction where

 _∧_ : Ω 𝓤 → Ω 𝓥 → Ω (𝓤 ⊔ 𝓥)
 P ∧ Q = (P holds × Q holds) , γ
  where
   γ = ×-is-prop (holds-is-prop P) (holds-is-prop Q)

 infixr 4 _∧_

\end{code}

Added by Martin Escardo 1st Nov 2023.

\begin{code}

 ∧-Intro :  (p : Ω 𝓤) (q : Ω 𝓥) → p holds → q holds → (p ∧ q) holds
 ∧-Intro p q a b = (a , b)

 ∧-Elim-L : (p : Ω 𝓤) (q : Ω 𝓥) → (p ∧ q) holds → p holds
 ∧-Elim-L p q = pr₁

 ∧-Elim-R :  (p : Ω 𝓤) (q : Ω 𝓥) → (p ∧ q) holds → q holds
 ∧-Elim-R p q = pr₂

 module _ (pe : propext 𝓤) (fe : funext 𝓤 𝓤) where

  ∧-intro :  (p q : Ω 𝓤) → p ＝ ⊤ → q ＝ ⊤ → p ∧ q ＝ ⊤
  ∧-intro p q a b = holds-gives-equal-⊤ pe fe (p ∧ q)
                     (∧-Intro p q
                       (equal-⊤-gives-holds p a)
                       (equal-⊤-gives-holds q b))

  ∧-elim-L :  (p q : Ω 𝓤) → p ∧ q ＝ ⊤ → p ＝ ⊤
  ∧-elim-L p q c = holds-gives-equal-⊤ pe fe p
                    (∧-Elim-L p q (equal-⊤-gives-holds (p ∧ q) c))

  ∧-elim-R :  (p q : Ω 𝓤) → p ∧ q ＝ ⊤ → q ＝ ⊤
  ∧-elim-R p q c = holds-gives-equal-⊤ pe fe q
                    (∧-Elim-R p q (equal-⊤-gives-holds (p ∧ q) c))

\end{code}

Added by Martin Escardo 8th September 2025.

\begin{code}

 module _ (pe : propext 𝓤)
          (fe : funext 𝓤 𝓤)
        where

  ⊤-is-∧-left-neutral : (p : Ω 𝓤) → ⊤ {𝓤} ∧ p ＝ p
  ⊤-is-∧-left-neutral p =
   Ω-extensionality pe fe
    pr₂
    (λ p-holds → ⋆ , p-holds)

  ⊤-is-∧-right-neutral : (p : Ω 𝓤) → p ∧ ⊤ {𝓤} ＝ p
  ⊤-is-∧-right-neutral p =
   Ω-extensionality pe fe
    pr₁
    (λ p-holds → p-holds , ⋆)

  ⊥-is-∧-left-absorbtive : (p : Ω 𝓤) → ⊥ {𝓤} ∧ p ＝ ⊥
  ⊥-is-∧-left-absorbtive p =
   Ω-extensionality pe fe
    pr₁
    𝟘-elim

  ∧-is-idempotent : (p : Ω 𝓤) → p ∧ p ＝ p
  ∧-is-idempotent p =
   Ω-extensionality pe fe
    pr₁
    (λ p-holds → p-holds , p-holds)

\end{code}

TODO. Add all the semilattice equations.

End of addition.

\section{Universal quantification}

\begin{code}

module Universal (fe : Fun-Ext) where

 ∀[꞉]-syntax : (I : 𝓤 ̇ ) → (I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
 ∀[꞉]-syntax I P = ((i : I) → P i holds) , γ
  where
   γ : is-prop ((i : I) → P i holds)
   γ = Π-is-prop fe (holds-is-prop ∘ P)


 ∀[]-syntax : {I : 𝓤 ̇ } → (I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
 ∀[]-syntax {I = I} P = ∀[꞉]-syntax I P

 infixr -1 ∀[꞉]-syntax
 infixr -1 ∀[]-syntax

 syntax ∀[꞉]-syntax I (λ i → e) = Ɐ i ꞉ I , e
 syntax ∀[]-syntax    (λ i → e) = Ɐ i , e

 ∀₂[꞉]-syntax : (I : 𝓤 ̇ )→ (I → I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
 ∀₂[꞉]-syntax I P = ((i j : I) → P i j holds) , γ
  where
   γ : is-prop ((i j : I) → P i j holds)
   γ = Π₂-is-prop fe λ i j → holds-is-prop (P i j)

 infixr -1 ∀₂[꞉]-syntax

 syntax ∀₂[꞉]-syntax I (λ i j → e) = Ɐ i j ꞉ I , e

 ∀₃[꞉]-syntax : (I : 𝓤 ̇ )→ (I → I → I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
 ∀₃[꞉]-syntax I P = Ɐ i ꞉ I , Ɐ j ꞉ I , Ɐ k ꞉ I , P i j k

 infixr -1 ∀₃[꞉]-syntax

 syntax ∀₃[꞉]-syntax I (λ i j k → e) = Ɐ i j k ꞉ I , e

\end{code}

\section{Implication}

\begin{code}

module Implication (fe : Fun-Ext) where

 infixr 3 _⇒_

 _⇒_ : Ω 𝓤 → Ω 𝓥 → Ω (𝓤 ⊔ 𝓥)
 P ⇒ Q = (P holds → Q holds) , γ
  where
   γ : is-prop (P holds → Q holds)
   γ = Π-is-prop fe λ _ → holds-is-prop Q

 open Conjunction

 _⇔_ : Ω 𝓤 → Ω 𝓥 → Ω (𝓤 ⊔ 𝓥)
 P ⇔ Q = (P ⇒ Q) ∧ (Q ⇒ P)

 infixr 3 _⇔_

 biimplication-forward : (P : Ω 𝓤) (Q : Ω 𝓥)
                       → (P ⇔ Q) holds → (P ⇒ Q) holds
 biimplication-forward P Q (φ , _) = φ

 biimplication-backward : (P : Ω 𝓤) (Q : Ω 𝓥)
                        → (P ⇔ Q) holds → (Q ⇒ P) holds
 biimplication-backward P Q (_ , ψ) = ψ

 infix 3 ¬ₚ_

 ¬ₚ_ : Ω 𝓤 → Ω 𝓤
 ¬ₚ_ {𝓤} P = P ⇒ ⊥ {𝓤}

 ¬¬ₚ_ : Ω 𝓤 → Ω 𝓤
 ¬¬ₚ p = ¬ₚ(¬ₚ p)

 ¬¬¬ₚ_ : Ω 𝓤 → Ω 𝓤
 ¬¬¬ₚ p = ¬ₚ(¬¬ₚ p)

\end{code}

Added by Martin Escardo 1st Nov 2023.

\begin{code}

 ⇔-gives-⇒ = biimplication-forward
 ⇔-gives-⇐ = biimplication-backward

 module _ (pe : propext 𝓤) where

  ⊤-⇔-neutral : (p : Ω 𝓤) → (p ⇔ ⊤) ＝ p
  ⊤-⇔-neutral p =
   Ω-extensionality pe fe
   (λ (h : (p ⇔ ⊤ {𝓤}) holds) → ⇔-gives-⇐ p ⊤ h ⊤-holds)
   (λ (h : p holds) → (λ _ → ⊤-holds) , (λ _ → h))

  ⇔-swap :  (p : Ω 𝓤) (q : Ω 𝓥) → (p ⇔ q) holds → (q ⇔ p) holds
  ⇔-swap p q (h , k) = (k , h)

  ⇔-swap' :  (p q : Ω 𝓤) → (p ⇔ q) ＝ ⊤ → (q ⇔ p) ＝ ⊤
  ⇔-swap' p q e = holds-gives-equal-⊤ pe fe (q ⇔ p)
                   (⇔-swap p q (equal-⊤-gives-holds (p ⇔ q) e))

  ⇔-sym :  (p q : Ω 𝓤) → (p ⇔ q) ＝ (q ⇔ p)
  ⇔-sym p q = Ω-ext pe fe (⇔-swap' p q) (⇔-swap' q p)

  ⊤-⇔-neutral' : (p : Ω 𝓤) → (⊤ ⇔ p) ＝ p
  ⊤-⇔-neutral' p = (⊤ ⇔ p ＝⟨ ⇔-sym ⊤ p ⟩
                    p ⇔ ⊤ ＝⟨ ⊤-⇔-neutral p ⟩
                    p     ∎)

  ⇔-refl : (p : Ω 𝓤) → (p ⇔ p) ＝ ⊤
  ⇔-refl p = holds-gives-equal-⊤ pe fe
              (p ⇔ p)
              (id , id)

  ＝-gives-⇔  :  (p q : Ω 𝓤) →  p ＝ q → (p ⇔ q) ＝ ⊤
  ＝-gives-⇔ p p refl = ⇔-refl p

  ⇔-gives-＝ :  (p q : Ω 𝓤) → (p ⇔ q) ＝ ⊤ → p ＝ q
  ⇔-gives-＝ p q e = Ω-extensionality pe fe f g
   where
    f : p holds → q holds
    f = ⇔-gives-⇒ p q (equal-⊤-gives-holds (p ⇔ q) e)

    g : q holds → p holds
    g = ⇔-gives-⇐ p q (equal-⊤-gives-holds (p ⇔ q) e)

  ⇔-equiv-to-＝ :  (p q : Ω 𝓤) → ((p ⇔ q) ＝ ⊤) ≃ (p ＝ q)
  ⇔-equiv-to-＝ p q = qinveq
                       (⇔-gives-＝ p q)
                       (＝-gives-⇔ p q ,
                       (λ _ → Ω-is-set fe pe _ _) ,
                       (λ _ → Ω-is-set fe pe _ _))

\end{code}

Added by Martin Escardo 8th September 2025.

\begin{code}

  ⊥⇒anything-is-⊤ : (p : Ω 𝓤) → (⊥ {𝓤} ⇒ p) ＝ ⊤ {𝓤}
  ⊥⇒anything-is-⊤ p =
   Ω-extensionality pe fe
    (λ (a : 𝟘 → p holds) → ⋆)
    (λ ⋆ → 𝟘-elim)

  ⊤⇒anything-is-the-thing : (p : Ω 𝓤) → (⊤ {𝓤} ⇒ p) ＝ p
  ⊤⇒anything-is-the-thing p =
   Ω-extensionality pe fe
    (λ (f : 𝟙 → p holds) → f ⋆)
    (λ p-holds ⋆ → p-holds)

  anything-implies-itself-is-⊤ : (p : Ω 𝓤) → (p ⇒ p) ＝ ⊤
  anything-implies-itself-is-⊤ p =
   Ω-extensionality pe fe
    (λ _ → ⋆)
    (λ _ → id)

\end{code}

End of addition.

\section{Disjunction}

\begin{code}

module Disjunction (pt : propositional-truncations-exist) where

 open propositional-truncations-exist pt

 _∨_ : Ω 𝓤 → Ω 𝓥 → Ω (𝓤 ⊔ 𝓥)
 P ∨ Q = ∥ P holds + Q holds ∥ , ∥∥-is-prop

 infixr 3 _∨_

\end{code}

Added by Ayberk Tosun 2024-05-28.

\begin{code}

 ∨-elim : (P : Ω 𝓤) (Q : Ω 𝓥) (R : Ω 𝓦)
        → (P holds → R holds)
        → (Q holds → R holds)
        → ((P ∨ Q) holds → R holds)
 ∨-elim P Q R φ ψ = ∥∥-rec (holds-is-prop R) †
  where
   † : P holds + Q holds → R holds
   † (inl p) = φ p
   † (inr q) = ψ q

\end{code}

\section{Truncation}

\begin{code}

module Truncation (pt : propositional-truncations-exist) where

  open PropositionalTruncation pt

  ∥_∥Ω : 𝓤 ̇ → Ω 𝓤
  ∥ A ∥Ω = ∥ A ∥ , ∥∥-is-prop

  ∥∥Ω-rec : {X : 𝓤 ̇ } {P : Ω 𝓥} → (X → P holds) → ∥ X ∥ → P holds
  ∥∥Ω-rec {𝓤} {𝓥} {X} {P} = ∥∥-rec (holds-is-prop P)

\end{code}

\section{Existential quantification}

\begin{code}

module Existential (pt : propositional-truncations-exist) where

 open Truncation pt

 ∃[꞉]-syntax : (I : 𝓤 ̇ )→ (I → 𝓥 ̇ )→ Ω (𝓤 ⊔ 𝓥)
 ∃[꞉]-syntax I A = ∥ Σ i ꞉ I , A i ∥Ω

 ∃[]-syntax : {I : 𝓤 ̇ } → (I → 𝓥 ̇ )→ Ω (𝓤 ⊔ 𝓥)
 ∃[]-syntax {I = I} P = ∃[꞉]-syntax I P

 ∃ₚ[꞉]-syntax : (I : 𝓤 ̇ )→ (I → Ω 𝓥)→ Ω (𝓤 ⊔ 𝓥)
 ∃ₚ[꞉]-syntax I A = Ǝ i ꞉ I , A i holds

 infixr -1 ∃[꞉]-syntax
 infixr -1 ∃[]-syntax

 syntax ∃[꞉]-syntax I (λ i → e) = Ǝ i ꞉ I , e
 syntax ∃[]-syntax    (λ i → e) = Ǝ i , e
 syntax ∃ₚ[꞉]-syntax I (λ i → e) = Ǝₚ i ꞉ I , e

\end{code}

\section{Negation of equality}

\begin{code}

module Negation-of-equality (fe : Fun-Ext) where

 _≢_ : {X : 𝓤 ̇ } → X → X → Ω 𝓤
 x ≢ y = (x ≠ y) , Π-is-prop fe (λ _ → 𝟘-is-prop)

\end{code}

\section{Equality}

The following was added by Ayberk Tosun on 2024-05-16.

\begin{code}

module Equality {X : 𝓤 ̇ } (s : is-set X) where

 _＝ₚ_ : X → X → Ω 𝓤
 _＝ₚ_ x y = (x ＝ y) , s

 infix 0 _＝ₚ_

\end{code}

End of addition.

\section{A module for importing all combinators}

\begin{code}

module AllCombinators
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

 open Conjunction             public
 open Universal            fe public
 open Implication          fe public
 open Disjunction          pt public
 open Existential          pt public
 open Truncation           pt public
 open Negation-of-equality fe public

\end{code}

TODO. Prove the all the missing equations for Heyting algebras for Ω.

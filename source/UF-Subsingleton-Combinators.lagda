Ayberk Tosun, 10 March 2021.

Based in part by the `Cubical.Functions.Logic` module of
`agda/cubical`.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Subsingleton-Combinators where

open import SpartanMLTT
open import UF-Subsingletons
open import UF-PropTrunc
open import UF-FunExt
open import UF-Subsingletons-FunExt

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

\section{Universal quantification}

\begin{code}

module Universal (fe : Fun-Ext) where

 ∀[∶]-syntax : (I : 𝓤 ̇) → (I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
 ∀[∶]-syntax I P = ((i : I) → P i holds) , γ
  where
   γ : is-prop ((i : I) → P i holds)
   γ = Π-is-prop fe (holds-is-prop ∘ P)


 ∀[]-syntax : {I : 𝓤 ̇} → (I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
 ∀[]-syntax {I = I} P = ∀[∶]-syntax I P

 infix 3 ∀[∶]-syntax
 infix 3 ∀[]-syntax

 syntax ∀[∶]-syntax I (λ i → e) = ∀[ i ∶ I ] e
 syntax ∀[]-syntax    (λ i → e) = ∀[ i ] e

\end{code}

\section{Implication}

\begin{code}

module Implication (fe : Fun-Ext) where

 open Universal fe

 infixr 3 _⇒_

 _⇒_ : Ω 𝓤 → Ω 𝓥 → Ω (𝓤 ⊔ 𝓥)
 P ⇒ Q = (P holds → Q holds) , γ
  where
   γ : is-prop (P holds → Q holds)
   γ = Π-is-prop fe λ _ → holds-is-prop Q

\end{code}

\section{Disjunction}

\begin{code}

module Disjunction (pt : propositional-truncations-exist) where

 open propositional-truncations-exist pt

 _∨_ : Ω 𝓤 → Ω 𝓥 → Ω (𝓤 ⊔ 𝓥)
 P ∨ Q = ∥ P holds + Q holds ∥ , ∥∥-is-prop

 infix 3 _∨_

\end{code}

\section{Existential quantification}

\begin{code}

module Existential (pt : propositional-truncations-exist) where

 open propositional-truncations-exist pt

 ∃[∶]-syntax : (I : 𝓤 ̇) → (I → 𝓥 ̇) → Ω (𝓤 ⊔ 𝓥)
 ∃[∶]-syntax I A = ∥ Σ i ꞉ I , A i ∥ , ∥∥-is-prop

 ∃[]-syntax : {I : 𝓤 ̇} → (I → 𝓥 ̇) → Ω (𝓤 ⊔ 𝓥)
 ∃[]-syntax {I = I} P = ∃[∶]-syntax I P

 infix 2 ∃[∶]-syntax
 infix 2 ∃[]-syntax

 syntax ∃[∶]-syntax I (λ i → e) = ∃[ i ∶ I ] e
 syntax ∃[]-syntax    (λ i → e) = ∃[ i ] e

\end{code}

\section{A module for importing all combinators}

\begin{code}

module AllCombinators
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
       where

 open Conjunction    public
 open Universal   fe public
 open Implication fe public
 open Disjunction pt public
 open Existential pt public

\end{code}

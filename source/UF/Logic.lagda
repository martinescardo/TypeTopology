Ayberk Tosun, 10 March 2021.

Based in part by the `Cubical.Functions.Logic` module UF.of
`agda/cubical`.

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

 ∧-intro' : (p q : Ω 𝓤) → p holds → q holds → (p ∧ q) holds
 ∧-intro' p q a b = (a , b)

 ∧-elim-L' : (p q : Ω 𝓤) → (p ∧ q) holds → p holds
 ∧-elim-L' p q = pr₁

 ∧-elim-R' : (p q : Ω 𝓤) → (p ∧ q) holds → q holds
 ∧-elim-R' p q = pr₂

 module _ (pe : propext 𝓤) (fe : funext 𝓤 𝓤) where

  ∧-intro : (p q : Ω 𝓤) → p ＝ ⊤ → q ＝ ⊤ → p ∧ q ＝ ⊤
  ∧-intro p q a b = holds-gives-equal-⊤ pe fe (p ∧ q)
                     (∧-intro' p q
                       (equal-⊤-gives-holds p a)
                       (equal-⊤-gives-holds q b))

  ∧-elim-L : (p q : Ω 𝓤) → p ∧ q ＝ ⊤ → p ＝ ⊤
  ∧-elim-L p q c = holds-gives-equal-⊤ pe fe p
                    (∧-elim-L' p q (equal-⊤-gives-holds (p ∧ q) c))

  ∧-elim-R : (p q : Ω 𝓤) → p ∧ q ＝ ⊤ → q ＝ ⊤
  ∧-elim-R p q c = holds-gives-equal-⊤ pe fe q
                    (∧-elim-R' p q (equal-⊤-gives-holds (p ∧ q) c))

\end{code}

End of addition.

\section{Universal quantification}

\begin{code}

module Universal (fe : Fun-Ext) where

 ∀[꞉]-syntax : (I : 𝓤 ̇ )→ (I → Ω 𝓥) → Ω (𝓤 ⊔ 𝓥)
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
 ¬ₚ_ {𝓤} P = _⇒_ P (𝟘 {𝓤} , 𝟘-is-prop)

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

  ⇔-swap : (p q : Ω 𝓤) → (p ⇔ q) holds → (q ⇔ p) holds
  ⇔-swap p q (h , k) = (k , h)

  ⇔-swap' : (p q : Ω 𝓤) → (p ⇔ q) ＝ ⊤ → (q ⇔ p) ＝ ⊤
  ⇔-swap' p q e = holds-gives-equal-⊤ pe fe (q ⇔ p)
                   (⇔-swap p q (equal-⊤-gives-holds (p ⇔ q) e))

  ⇔-sym : (p q : Ω 𝓤) → (p ⇔ q) ＝ (q ⇔ p)
  ⇔-sym p q = Ω-ext pe fe (⇔-swap' p q) (⇔-swap' q p)

  ⊤-⇔-neutral' : (p : Ω 𝓤) → (⊤ ⇔ p) ＝ p
  ⊤-⇔-neutral' p = (⊤ ⇔ p ＝⟨ ⇔-sym ⊤ p ⟩
                    p ⇔ ⊤ ＝⟨ ⊤-⇔-neutral p ⟩
                    p     ∎)

  ⇔-refl : (p : Ω 𝓤) → (p ⇔ p) ＝ ⊤
  ⇔-refl p = holds-gives-equal-⊤ pe fe
              (p ⇔ p)
              (id , id)

  ＝-gives-⇔  : (p q : Ω 𝓤) →  p ＝ q → (p ⇔ q) ＝ ⊤
  ＝-gives-⇔ p p refl = ⇔-refl p

  ⇔-gives-＝ : (p q : Ω 𝓤) → (p ⇔ q) ＝ ⊤ → p ＝ q
  ⇔-gives-＝ p q e = Ω-extensionality pe fe f g
   where
    f : p holds → q holds
    f = ⇔-gives-⇒ p q (equal-⊤-gives-holds (p ⇔ q) e)

    g : q holds → p holds
    g = ⇔-gives-⇐ p q (equal-⊤-gives-holds (p ⇔ q) e)

  ⇔-equiv-to-＝ : (p q : Ω 𝓤) → ((p ⇔ q) ＝ ⊤) ≃ (p ＝ q)
  ⇔-equiv-to-＝ p q = qinveq
                       (⇔-gives-＝ p q)
                       (＝-gives-⇔ p q ,
                       (λ _ → Ω-is-set fe pe _ _) ,
                       (λ _ → Ω-is-set fe pe _ _))

\end{code}

End of addition.

\section{Disjunction}

\begin{code}

module Disjunction (pt : propositional-truncations-exist) where

 open propositional-truncations-exist pt

 _∨_ : Ω 𝓤 → Ω 𝓥 → Ω (𝓤 ⊔ 𝓥)
 P ∨ Q = ∥ P holds + Q holds ∥ , ∥∥-is-prop

 infix 3 _∨_

\end{code}

\section{Truncation}

\begin{code}
module Truncation (pt : propositional-truncations-exist) where

  open PropositionalTruncation pt

  ∥_∥Ω : 𝓤 ̇  → Ω 𝓤
  ∥ A ∥Ω = ∥ A ∥ , ∥∥-is-prop

  ∥∥Ω-rec : {X : 𝓤  ̇} {P : Ω 𝓥} → (X → P holds) → ∥ X ∥ → P holds
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

 infixr -1 ∃[꞉]-syntax
 infixr -1 ∃[]-syntax

 syntax ∃[꞉]-syntax I (λ i → e) = Ǝ i ꞉ I , e
 syntax ∃[]-syntax    (λ i → e) = Ǝ i , e

\end{code}

\section{Negation of equality}

\begin{code}

module Negation-of-equality (fe : Fun-Ext) where

 _≢_ : {X : 𝓤 ̇ } → X → X → Ω 𝓤
 x ≢ y = (x ≠ y) , Π-is-prop fe (λ _ → 𝟘-is-prop)

\end{code}

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

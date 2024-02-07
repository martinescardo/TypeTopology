Martin Escardo, 8th December 2019.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Fin.Bishop where

open import Fin.Properties
open import Fin.Type
open import MLTT.Spartan
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.UA-FunExt
open import UF.Univalence
open import UF.UniverseEmbedding

\end{code}

One defines a type to be finite, in univalent mathematics, if it is
isomorphic to Fin n for some n. But one has to be careful to express
this, if we want finiteness to be property rather than structure, with
a suitably chosen notion of existence.

The following is structure rather than property. It amounts to the
type of finite linear orders on X.

\begin{code}

finite-linear-order : 𝓤 ̇ → 𝓤 ̇
finite-linear-order X = Σ n ꞉ ℕ , X ≃ Fin n

\end{code}

There are two ways of making 𝟙 + 𝟙 into a linear order. We choose the
following one.

\begin{code}

𝟙+𝟙-natural-finite-linear-order : finite-linear-order (𝟙 {𝓤} + 𝟙 {𝓤})
𝟙+𝟙-natural-finite-linear-order {𝓤} = 2 , g
 where
  f : 𝟙 {𝓤} + 𝟙 {𝓤} ≃ (𝟘 {𝓤₀} + 𝟙 {𝓤₀}) + 𝟙 {𝓤₀}
  f = +-cong 𝟘-lneutral'' one-𝟙-only

  f' : 𝟙 {𝓤} + 𝟙 {𝓤} ≃ Fin 2
  f' = f

  g : 𝟙 {𝓤} + 𝟙 {𝓤} ≃ Fin 2
  g = +comm ● f'

  observation : (⌜ g ⌝ (inl ⋆) ＝ 𝟎) × (⌜ g ⌝ (inr ⋆) ＝ 𝟏)
  observation = refl , refl

\end{code}

Exercise: If X ≃ Fin n, then the type finite-linear-order X has n! elements (solved
elsewhere in TypeTopology).

\begin{code}

type-of-linear-orders-is-ℕ : Univalence → (Σ X ꞉ 𝓤 ̇ , finite-linear-order X) ≃ ℕ
type-of-linear-orders-is-ℕ {𝓤} ua =
  (Σ X ꞉ 𝓤 ̇ , Σ n ꞉ ℕ , X ≃ Fin n)          ≃⟨ i ⟩
  (Σ X ꞉ 𝓤 ̇ , Σ n ꞉ ℕ , Fin n ≃ X)          ≃⟨ ii ⟩
  (Σ X ꞉ 𝓤 ̇ , Σ n ꞉ ℕ , Lift 𝓤 (Fin n) ≃ X) ≃⟨ iii ⟩
  (Σ X ꞉ 𝓤 ̇ , Σ n ꞉ ℕ , Lift 𝓤 (Fin n) ＝ X) ≃⟨ iv ⟩
  ℕ                                         ■
 where
  fe : FunExt
  fe = Univalence-gives-FunExt ua

  i   = Σ-cong (λ X → Σ-cong (λ n → ≃-Sym fe))
  ii  = Σ-cong (λ X → Σ-cong (λ n → ≃-cong-left fe (≃-Lift 𝓤 (Fin n))))
  iii = Σ-cong (λ X → Σ-cong (λ n → ≃-sym (univalence-≃ (ua 𝓤) (Lift 𝓤 (Fin n)) X)))
  iv  = total-fiber-is-domain (Lift 𝓤 ∘ Fin)

\end{code}

Hence one considers the following notion of finiteness, which is
property rather than structure:

\begin{code}

module finiteness (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 _has-cardinality_ : 𝓤 ̇ → ℕ → 𝓤 ̇
 X has-cardinality n = ∥ X ≃ Fin n ∥

 is-finite : 𝓤 ̇ → 𝓤 ̇
 is-finite X = Σ n ꞉ ℕ , X has-cardinality n

 cardinality : (X : 𝓤 ̇ ) → is-finite X → ℕ
 cardinality X = pr₁

 cardinality-≃ : (X : 𝓤 ̇ ) (φ : is-finite X) → X has-cardinality (cardinality X φ)
 cardinality-≃ X = pr₂

 being-finite-is-prop : (X : 𝓤 ̇ ) → is-prop (is-finite X)
 being-finite-is-prop X (m , d) (n , e) = γ
  where
   α : (m n : ℕ) → X ≃ Fin m → X ≃ Fin n → m ＝ n
   α m n d e = Fin-lc m n (≃-sym d ● e)

   β : (m n : ℕ) → ∥ X ≃ Fin m ∥ → ∥ X ≃ Fin n ∥ → m ＝ n
   β m n = ∥∥-rec₂ ℕ-is-set (α m n)

   γ : m , d ＝ n , e
   γ = to-Σ-＝ (β m n d e , ∥∥-is-prop _ _)

\end{code}

Equivalently, one can define finiteness as follows, with the
truncation outside the Σ:

\begin{code}

 is-finite' : 𝓤 ̇ → 𝓤 ̇
 is-finite' X = ∃ n ꞉ ℕ , X ≃ Fin n

 being-finite'-is-prop : (X : 𝓤 ̇ ) → is-prop (is-finite' X)
 being-finite'-is-prop X = ∃-is-prop

 finite'-gives-finite : (X : 𝓤 ̇ ) → is-finite' X → is-finite X
 finite'-gives-finite X = ∥∥-rec (being-finite-is-prop X) γ
  where
   γ : (Σ n ꞉ ℕ , X ≃ Fin n) → Σ n ꞉ ℕ , ∥ X ≃ Fin n ∥
   γ (n , e) = n , ∣ e ∣

 finite-gives-finite' : (X : 𝓤 ̇ ) → is-finite X → is-finite' X
 finite-gives-finite' X (n , s) = ∥∥-rec ∥∥-is-prop (λ e → ∣ n , e ∣) s

\end{code}

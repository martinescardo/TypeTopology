Martin Escardo, November-December 2019

We consider a situation in which anonymous existence gives explicit
existence.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module Fin.Choice where

open import Fin.Order
open import Fin.Properties
open import Fin.Type
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import Notation.Order
open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable
open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 Σ-min-from-∃ : FunExt → {n : ℕ} (A : Fin n → 𝓤 ̇ )
             → is-complemented A
             → is-prop-valued-family A
             → ∃ A
             → Σ-min A

 Σ-min-from-∃ fe A δ h = ∥∥-rec (Σ-min-is-prop fe A h) (Σ-gives-Σ-min A δ)

 Fin-Σ-from-∃' : FunExt
               → {n : ℕ} (A : Fin n → 𝓤 ̇ )
               → is-complemented A
               → is-prop-valued-family A
               → ∃ A
               → Σ A

 Fin-Σ-from-∃' fe A δ h e = Σ-min-gives-Σ A (Σ-min-from-∃ fe A δ h e)

\end{code}

But the prop-valuedness of A is actually not needed, with more work:

\begin{code}

 Fin-Σ-from-∃ : FunExt
              → {n : ℕ} (A : Fin n → 𝓤 ̇ )
              → is-complemented A
              → ∃ A
              → Σ A

 Fin-Σ-from-∃ {𝓤} fe {n} A δ e = γ
  where
   A' : Fin n → 𝓤 ̇
   A' x = ∥ A x ∥

   δ' : is-complemented A'
   δ' x = d (δ x)
    where
     d : is-decidable (A x) → is-decidable (A' x)
     d (inl a) = inl ∣ a ∣
     d (inr u) = inr (∥∥-rec 𝟘-is-prop u)

   f : Σ A → Σ A'
   f (x , a) = x , ∣ a ∣

   e' : ∃ A'
   e' = ∥∥-functor f e

   σ' : Σ A'
   σ' = Fin-Σ-from-∃' fe A' δ' (λ x → ∥∥-is-prop) e'

   g : Σ A' → Σ A
   g (x , a') = x , ¬¬-elim (δ x) (λ (u : ¬ A x) → ∥∥-rec 𝟘-is-prop u a')

   γ : Σ A
   γ = g σ'

\end{code}

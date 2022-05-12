Tom de Jong, 24 January 2022
(Refactored from FreeJoinSemiLattice.lagda)

We define join-semilattices using a record. We also introduce convenient helpers
and syntax for reasoning about the order ⊑ and we construct finite joins using
the least element and binary joins.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module JoinSemiLattices where

open import SpartanMLTT

open import Fin

open import UF-Subsingletons

record JoinSemiLattice (𝓥 𝓣 : Universe) : 𝓤ω where
  field
    L : 𝓥 ̇
    L-is-set : is-set L
    _⊑_ : L → L → 𝓣 ̇
    ⊑-is-prop-valued : (x y : L) → is-prop (x ⊑ y)
    ⊑-is-reflexive : (x : L) → x ⊑ x
    ⊑-is-transitive : (x y z : L) → x ⊑ y → y ⊑ z → x ⊑ z
    ⊑-is-antisymmetric : (x y : L) → x ⊑ y → y ⊑ x → x ≡ y
    ⊥ : L
    ⊥-is-least : (x : L) → ⊥ ⊑ x
    _∨_ : L → L → L
    ∨-is-upperbound₁ : (x y : L) → x ⊑ (x ∨ y)
    ∨-is-upperbound₂ : (x y : L) → y ⊑ (x ∨ y)
    ∨-is-lowerbound-of-upperbounds : (x y z : L) → x ⊑ z → y ⊑ z → (x ∨ y) ⊑ z

  transitivity' : (x : L) {y z : L}
                → x ⊑ y → y ⊑ z → x ⊑ z
  transitivity' x {y} {z} = ⊑-is-transitive x y z

  syntax transitivity' x u v = x ⊑⟨ u ⟩ v
  infixr 0 transitivity'

  reflexivity' : (x : L) → x ⊑ x
  reflexivity' x = ⊑-is-reflexive x

  syntax reflexivity' x = x ⊑∎
  infix 1 reflexivity'

  ≡-to-⊑ : {x y : L} → x ≡ y → x ⊑ y
  ≡-to-⊑ {x} {x} refl = reflexivity' x

  ∨ⁿ : {n : ℕ} → (Fin n → L) → L
  ∨ⁿ {zero}   e = ⊥
  ∨ⁿ {succ m} e = (∨ⁿ (e ∘ suc)) ∨ (e 𝟎)

  ∨ⁿ-is-upperbound : {n : ℕ} (σ : Fin n → L)
                   → (k : Fin n) → σ k ⊑ ∨ⁿ σ
  ∨ⁿ-is-upperbound {succ n} σ 𝟎       = ∨-is-upperbound₂ _ _
  ∨ⁿ-is-upperbound {succ n} σ (suc k) = σ (suc k)    ⊑⟨ IH ⟩
                                        ∨ⁿ (σ ∘ suc) ⊑⟨ ∨-is-upperbound₁ _ _ ⟩
                                        ∨ⁿ σ         ⊑∎
   where
    IH = ∨ⁿ-is-upperbound (σ ∘ suc) k

  ∨ⁿ-is-lowerbound-of-upperbounds : {n : ℕ} (σ : Fin n → L)
                                    (x : L)
                                  → ((k : Fin n) → σ k ⊑ x)
                                  → ∨ⁿ σ ⊑ x
  ∨ⁿ-is-lowerbound-of-upperbounds {zero}   σ x ub = ⊥-is-least x
  ∨ⁿ-is-lowerbound-of-upperbounds {succ n} σ x ub =
   ∨-is-lowerbound-of-upperbounds _ _ _ u v
    where
     u : ∨ⁿ (σ ∘ suc) ⊑ x
     u = ∨ⁿ-is-lowerbound-of-upperbounds {n} (σ ∘ suc) x (ub ∘ suc)
     v : σ 𝟎 ⊑ x
     v = ub 𝟎

\end{code}

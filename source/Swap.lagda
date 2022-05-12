Martin Escardo, November 2019.

The swap automorphism.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module Swap where

open import SpartanMLTT
open import Plus-Properties
open import DiscreteAndSeparated
open import UF-Equiv
open import UF-Miscelanea

\end{code}

We change the value of one isolated argument of a function, and no
other value, with patch. Recall that a point x:X is called isolated if
x=y is decidable for all y:X.

\begin{code}

module _ {𝓤 𝓥} {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (a : X) (b : Y) (i : is-isolated a) (f : X → Y) where

 private
  φ : (x : X) → (a ≡ x) + (a ≢ x) → Y
  φ x (inl p) = b
  φ x (inr u) = f x

  f' : X → Y
  f' x = φ x (i x)

  γ : (z : (a ≡ a) + (a ≢ a)) → i a ≡ z → φ a z ≡ b
  γ (inl p) q = refl
  γ (inr u) q = 𝟘-elim (u refl)

  δ : (x : X) (u : a ≢ x) (z : (a ≡ x) + (a ≢ x)) → i x ≡ z → φ x z ≡ f x
  δ x u (inl p) q = 𝟘-elim (u p)
  δ x u (inr v) q = refl

 patch : X → Y
 patch = f'

 patch-equation₀ : f' a ≡ b
 patch-equation₀ = γ (i a) refl

 patch-equation₁ : (x : X) → a ≢ x → f' x ≡ f x
 patch-equation₁ x u = δ x u (i x) refl

\end{code}

The (involutive) swap automorphism is obtained by patching the
identity function twice:

\begin{code}

swap : {X : 𝓤 ̇ } (a b : X) → is-isolated a → is-isolated b → X → X
swap a b i j = patch a b i (patch b a j id)

swap-equation₀ : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → swap a b i j a ≡ b
swap-equation₀ a b i j = patch-equation₀ a b i (patch b a j id)

swap-equation₁ : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → swap a b i j b ≡ a
swap-equation₁ a b i j = γ (j a)
 where
  γ : (b ≡ a) + (b ≢ a) → swap a b i j b ≡ a
  γ (inl r) =
      swap a b i j b ≡⟨ ap (swap a b i j) r ⟩
      swap a b i j a ≡⟨ swap-equation₀ a b i j ⟩
      b              ≡⟨ r ⟩
      a              ∎
  γ (inr n) =
      swap a b i j b                 ≡⟨ refl   ⟩
      patch a b i (patch b a j id) b ≡⟨ patch-equation₁ a b i (patch b a j id) b (≢-sym n) ⟩
      patch b a j id b               ≡⟨ patch-equation₀ b a j id ⟩
      a                              ∎

swap-equation₂ : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → (x : X) → a ≢ x → b ≢ x → swap a b i j x ≡ x
swap-equation₂ a b i j x m n =
  swap a b i j x                 ≡⟨ refl ⟩
  patch a b i (patch b a j id) x ≡⟨ patch-equation₁ a b i (patch b a j id) x m ⟩
  patch b a j id x               ≡⟨ patch-equation₁ b a j id x n ⟩
  x                              ∎

swap-symmetric : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → swap a b i j ∼ swap b a j i
swap-symmetric a b i j x = γ (i x) (j x)
 where
  γ : (a ≡ x) + (a ≢ x) → (b ≡ x) + (b ≢ x) → swap a b i j x ≡ swap b a j i x
  γ (inl p) _ =
    swap a b i j x ≡⟨ ap (swap a b i j) (p ⁻¹) ⟩
    swap a b i j a ≡⟨ swap-equation₀ a b i j ⟩
    b              ≡⟨ (swap-equation₁ b a j i)⁻¹ ⟩
    swap b a j i a ≡⟨ ap (swap b a j i) p ⟩
    swap b a j i x ∎
  γ (inr _) (inl q) =
    swap a b i j x ≡⟨ ap (swap a b i j) (q ⁻¹) ⟩
    swap a b i j b ≡⟨ swap-equation₁ a b i j ⟩
    a              ≡⟨ (swap-equation₀ b a j i)⁻¹ ⟩
    swap b a j i b ≡⟨ ap (swap b a j i) q ⟩
    swap b a j i x ∎
  γ (inr m) (inr n) =
    swap a b i j x ≡⟨ swap-equation₂ a b i j x m n ⟩
    x              ≡⟨ (swap-equation₂ b a j i x n m)⁻¹ ⟩
    swap b a j i x ∎

swap-involutive : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
                → swap a b i j ∘ swap a b i j ∼ id
swap-involutive a b i j x = γ (i x) (j x)
 where
  γ : (a ≡ x) + (a ≢ x) → (b ≡ x) + (b ≢ x) → swap a b i j (swap a b i j x) ≡ x
  γ (inl p) _ =
    swap a b i j (swap a b i j x) ≡⟨ ap (λ - → swap a b i j (swap a b i j -)) (p ⁻¹) ⟩
    swap a b i j (swap a b i j a) ≡⟨ ap (swap a b i j) (swap-equation₀ a b i j) ⟩
    swap a b i j b                ≡⟨ swap-equation₁ a b i j ⟩
    a                             ≡⟨ p    ⟩
    x                             ∎
  γ (inr _) (inl q) =
    swap a b i j (swap a b i j x) ≡⟨ ap (λ - → swap a b i j (swap a b i j -)) (q ⁻¹) ⟩
    swap a b i j (swap a b i j b) ≡⟨ ap (swap a b i j) (swap-equation₁ a b i j) ⟩
    swap a b i j a                ≡⟨ swap-equation₀ a b i j ⟩
    b                             ≡⟨ q    ⟩
    x                             ∎
  γ (inr m) (inr n) =
    swap a b i j (swap a b i j x) ≡⟨ ap (swap a b i j) (swap-equation₂ a b i j x m n) ⟩
    swap a b i j x                ≡⟨ swap-equation₂ a b i j x m n ⟩
    x                             ∎

swap-is-equiv : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
              → is-equiv (swap a b i j)
swap-is-equiv a b i j = qinvs-are-equivs
                         (swap a b i j)
                         (swap a b i j , (swap-involutive a b i j , swap-involutive a b i j))

≃-swap : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b) → X ≃ X
≃-swap a b i j = swap a b i j , swap-is-equiv a b i j

\end{code}

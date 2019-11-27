Martin Escardo, November 2019.

The swap automorphism.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module Swap (fe : FunExt) where

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

patch : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (a : X) (b : Y)
      → is-isolated a → (X → Y) → (X → Y)
patch a b i f x = Cases (i x)
                    (λ (_ : a ≡ x) → b)
                    (λ (_ : a ≢ x) → f x)

patch-equation₀ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (a : X) (b : Y)
                  (i : is-isolated a) (f : X → Y)
                → patch a b i f a ≡ b
patch-equation₀ a b i f = Cases-equality-l (λ _ → b) (λ _ → f a) (i a) refl γ
 where
  γ : i a ≡ inl refl
  γ = isolated-inl a i a refl

patch-equation₁ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (a : X) (b : Y)
                  (i : is-isolated a) (f : X → Y)
                → (x : X) → a ≢ x → patch a b i f x ≡ f x
patch-equation₁ {𝓤} {X} a b i f x n = Cases-equality-r (λ _ → b) (λ _ → f x) (i x) n γ
 where
  γ : i x ≡ inr n
  γ = isolated-inr (fe 𝓤 𝓤₀) a i x n

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
      swap a b i j b ≡⟨ ap (swap a b i j) r    ⟩
      swap a b i j a ≡⟨ swap-equation₀ a b i j ⟩
      b              ≡⟨ r                      ⟩
      a              ∎
  γ (inr n) =
      swap a b i j b                 ≡⟨ refl                                               ⟩
      patch a b i (patch b a j id) b ≡⟨ patch-equation₁ a b i (patch b a j id) b (≢-sym n) ⟩
      patch b a j id b               ≡⟨ patch-equation₀ b a j id                           ⟩
      a                              ∎

swap-equation₂ : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → (x : X) → a ≢ x → b ≢ x → swap a b i j x ≡ x
swap-equation₂ a b i j x m n =
  swap a b i j x                 ≡⟨ refl                                       ⟩
  patch a b i (patch b a j id) x ≡⟨ patch-equation₁ a b i (patch b a j id) x m ⟩
  patch b a j id x               ≡⟨ patch-equation₁ b a j id x n               ⟩
  x                              ∎

swap-symmetric : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
               → swap a b i j ∼ swap b a j i
swap-symmetric a b i j x = γ (i x) (j x)
 where
  γ : (a ≡ x) + (a ≢ x) → (b ≡ x) + (b ≢ x) → swap a b i j x ≡ swap b a j i x
  γ (inl p) _ =
    swap a b i j x ≡⟨ ap (swap a b i j) (p ⁻¹)         ⟩
    swap a b i j a ≡⟨ swap-equation₀ a b i j           ⟩
    b              ≡⟨ (swap-equation₁ b a j i)⁻¹       ⟩
    swap b a j i a ≡⟨ ap (swap b a j i) p              ⟩
    swap b a j i x ∎
  γ (inr _) (inl q) =
    swap a b i j x ≡⟨ ap (swap a b i j) (q ⁻¹)         ⟩
    swap a b i j b ≡⟨ swap-equation₁ a b i j           ⟩
    a              ≡⟨ (swap-equation₀ b a j i)⁻¹       ⟩
    swap b a j i b ≡⟨ ap (swap b a j i) q              ⟩
    swap b a j i x ∎
  γ (inr m) (inr n) =
    swap a b i j x ≡⟨ swap-equation₂ a b i j x m n     ⟩
    x              ≡⟨ (swap-equation₂ b a j i x n m)⁻¹ ⟩
    swap b a j i x ∎

swap-involutive : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
                → swap a b i j ∘ swap a b i j ∼ id
swap-involutive a b i j x = γ (i x) (j x)
 where
  γ : (a ≡ x) + (a ≢ x) → (b ≡ x) + (b ≢ x) → swap a b i j (swap a b i j x) ≡ x
  γ (inl p) _ =
    swap a b i j (swap a b i j x) ≡⟨ ap (λ - → swap a b i j (swap a b i j -)) (p ⁻¹)  ⟩
    swap a b i j (swap a b i j a) ≡⟨ ap (swap a b i j) (swap-equation₀ a b i j)       ⟩
    swap a b i j b                ≡⟨ swap-equation₁ a b i j                           ⟩
    a                             ≡⟨ p                                                ⟩
    x                             ∎
  γ (inr _) (inl q) =
    swap a b i j (swap a b i j x) ≡⟨ ap (λ - → swap a b i j (swap a b i j -)) (q ⁻¹)  ⟩
    swap a b i j (swap a b i j b) ≡⟨ ap (swap a b i j) (swap-equation₁ a b i j)       ⟩
    swap a b i j a                ≡⟨ swap-equation₀ a b i j                           ⟩
    b                             ≡⟨ q                                                ⟩
    x                             ∎
  γ (inr m) (inr n) =
    swap a b i j (swap a b i j x) ≡⟨ ap (swap a b i j) (swap-equation₂ a b i j x m n) ⟩
    swap a b i j x                ≡⟨ swap-equation₂ a b i j x m n                     ⟩
    x                             ∎

swap-is-equiv : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b)
              → is-equiv (swap a b i j)
swap-is-equiv a b i j = qinvs-are-equivs
                         (swap a b i j)
                         (swap a b i j , (swap-involutive a b i j , swap-involutive a b i j))

≃-swap : {X : 𝓤 ̇ } (a b : X) (i : is-isolated a) (j : is-isolated b) → X ≃ X
≃-swap a b i j = swap a b i j , swap-is-equiv a b i j

\end{code}

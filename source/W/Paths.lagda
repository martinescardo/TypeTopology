Martin Escardo, June 2023.

Paths in W-types.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan

module W.Paths where

open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import W.Type
open import W.Numbers
open import W.Properties

module _ (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) where

 private
  𝕎 = W X A

 Path₀ : 𝕎 → 𝓤 ⊔ 𝓥 ̇
 Path₀ (ssup x φ) = is-empty (A x) + (Σ a ꞉ A x , Path₀ (φ a))

 Path₀-length : (w : 𝕎) → Path₀ w → ℕ
 Path₀-length (ssup x φ) (inl _)        = 0
 Path₀-length (ssup x φ) (inr (a , as)) = succ (Path₀-length (φ a) as)

 open import UF.PropTrunc

 module stronger-notion-of-path
         (pt : propositional-truncations-exist)
        where

  open PropositionalTruncation pt

  Path : 𝕎 → 𝓤 ⊔ 𝓥 ̇
  Path (ssup x φ) = ∥ A x ∥ → Σ a ꞉ A x , Path (φ a)

  head : (w : 𝕎) → ∥ A (W-root w) ∥ → Path w → A (W-root w)
  head (ssup x φ) s as = pr₁ (as s)

  tail : (w : 𝕎) (s : ∥ A (W-root w) ∥) (as : Path w) → Path (W-forest w (head w s as))
  tail (ssup x φ) s as = pr₂ (as s)


  Path₀-gives-Path : (w : 𝕎) → Path₀ w → Path w
  Path₀-gives-Path (ssup x φ) (inl e)         a₀ = 𝟘-elim (∥∥-rec 𝟘-is-prop e a₀)
  Path₀-gives-Path (ssup x φ) (inr (a , as))  a₀ = a , Path₀-gives-Path (φ a) as

  Path-length : (w : 𝕎) → Path w → 𝓝 𝓥
  Path-length (ssup x φ) as = ssup (∥ A x ∥ , ∥∥-is-prop)
                              (λ s → Path-length (φ (pr₁ (as s))) (pr₂ (as s)))
\end{code}

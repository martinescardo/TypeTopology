Martin Escardo, 2nd May 2022

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-Univalence

module OrdinalsSupSum
        (ua : Univalence)
       where

open import SpartanMLTT
open import OrdinalNotions
open import OrdinalsType
open import OrdinalOfOrdinals ua
open import CanonicalMapNotation

open import UF-FunExt
open import UF-UA-FunExt
open import UF-ExcludedMiddle

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

order-preserving-gives-not-⊲ : (α β : Ordinal 𝓤)
                             → (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-order-preserving α β f)
                             → ¬ (β ⊲ α)
order-preserving-gives-not-⊲ {𝓤} α β σ (x₀ , refl) = γ σ
 where
  γ : ¬ (Σ f ꞉ (⟨ α ⟩ → ⟨ α ↓ x₀ ⟩) , is-order-preserving α (α ↓ x₀) f)
  γ (f , fop) = κ
   where
    g : ⟨ α ⟩ → ⟨ α ⟩
    g x = pr₁ (f x)

    h : (x : ⟨ α ⟩) → g x ≺⟨ α ⟩ x₀
    h x = pr₂ (f x)

    δ : (n : ℕ) → (g ^ succ n) x₀ ≺⟨ α ⟩ (g ^ n) x₀
    δ 0        = h x₀
    δ (succ n) = fop _ _ (δ n)

    A : ⟨ α ⟩ → 𝓤 ̇
    A x = Σ n ꞉ ℕ , (g ^ n) x₀ ≡ x

    d : (x : ⟨ α ⟩) → A x → Σ y ꞉ ⟨ α ⟩ , (y ≺⟨ α ⟩ x) × A y
    d x (n , refl) = g x , δ n , succ n , refl

    κ : 𝟘
    κ = no-minimal-is-empty' (underlying-order α) (Well-foundedness α)
         A d (x₀ , 0 , refl)

order-preserving-gives-≼ : EM (𝓤 ⁺)
                         → (α β : Ordinal 𝓤)
                         → (Σ f ꞉ (⟨ α ⟩ → ⟨ β ⟩) , is-order-preserving α β f)
                         → α ≼ β
order-preserving-gives-≼ em α β σ = δ
 where
  γ : (α ≼ β) + (β ⊲ α) → α ≼ β
  γ (inl l) = l
  γ (inr m) = 𝟘-elim (order-preserving-gives-not-⊲ α β σ m)

  δ : α ≼ β
  δ = γ (≼-or-> _⊲_ fe' em ⊲-is-well-order α β)

\end{code}

To be continued. The main thing we wanted to add here is not yet written down.

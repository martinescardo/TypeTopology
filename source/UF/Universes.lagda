Martin Escardo

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Universes where

open import MLTT.Plus-Properties
open import MLTT.Spartan hiding (𝟚)
open import UF.Equiv
open import UF.Sets
open import UF.Univalence

universes-are-not-sets : is-univalent 𝓤 → ¬ (is-set (𝓤 ̇ ))
universes-are-not-sets {𝓤} ua = γ
 where
  𝟚 : 𝓤 ̇
  𝟚 = 𝟙 {𝓤} + 𝟙 {𝓤}

  swap : 𝟚 → 𝟚
  swap (inl ⋆) = inr ⋆
  swap (inr ⋆) = inl ⋆

  swap-involutive : (b : 𝟚) → swap (swap b) ＝ b
  swap-involutive (inl ⋆) = refl
  swap-involutive (inr ⋆) = refl

  e₀ e₁ : 𝟚 ≃ 𝟚
  e₀ = ≃-refl 𝟚
  e₁ = qinveq swap (swap , swap-involutive , swap-involutive)

  e₀-is-not-e₁ : e₀ ≠ e₁
  e₀-is-not-e₁ p = +disjoint r
   where
    q : id ＝ swap
    q = ap ⌜_⌝ p

    r : inl ⋆ ＝ inr ⋆
    r = ap (λ - → - (inl ⋆)) q

  p₀ p₁ : 𝟚 ＝ 𝟚
  p₀ = eqtoid ua 𝟚 𝟚 e₀
  p₁ = eqtoid ua 𝟚 𝟚 e₁

  p₀-is-not-p₁ : p₀ ≠ p₁
  p₀-is-not-p₁ q = e₀-is-not-e₁ r
   where
    r = e₀            ＝⟨ (inverses-are-sections (idtoeq 𝟚 𝟚) (ua 𝟚 𝟚) e₀)⁻¹ ⟩
        idtoeq 𝟚 𝟚 p₀ ＝⟨ ap (idtoeq 𝟚 𝟚) q                                  ⟩
        idtoeq 𝟚 𝟚 p₁ ＝⟨ inverses-are-sections (idtoeq 𝟚 𝟚) (ua 𝟚 𝟚) e₁     ⟩
        e₁            ∎

  γ : ¬ (is-set (𝓤 ̇ ))
  γ s = p₀-is-not-p₁ q
   where
    q : p₀ ＝ p₁
    q = s p₀ p₁

\end{code}

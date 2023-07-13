```agda

{-# OPTIONS --without-K --exact-split --safe #-}

open import MLTT.Spartan
open import TypeTopology.DiscreteAndSeparated
open import UF.Subsingletons
open import UF.Miscelanea
open import UF.Equiv

module TWA.Thesis.Chapter2.FiniteDiscrete where

open import Naturals.Addition renaming (_+_ to _+ℕ_)

is-even : ℕ → 𝓤₀ ̇
is-even 0 = 𝟙
is-even 1 = 𝟘
is-even (succ (succ n)) = is-even n

ℕₑ : 𝓤₀ ̇
ℕₑ = Σ n ꞉ ℕ , is-even n

-- sample-proof : ((n , _) : ℕₑ) → Σ m ꞉ ℕ , n +ℕ n ＝ m 
-- Doesn't termination check
{-


sample-proof' : (n : ℕ) → is-even n → Σ m ꞉ ℕ , n +ℕ n ＝ m 
sample-proof' 0 ⋆               = 0 , refl
sample-proof' 1 ()
sample-proof' (succ (succ n)) e
 = succ (succ m') , ap (succ ∘ succ) {!e'!}
 where
  IH : Σ m' ꞉ ℕ , ((n +ℕ n) ＝ m')
  IH = sample-proof' n e
  m' = pr₁ IH
  e' = pr₂ IH

sample-proof : ((n , _) : ℕₑ) → Σ m ꞉ ℕ , n +ℕ n ＝ m 
sample-proof (0 , ⋆)  = 0 , refl
sample-proof (1 , ())
sample-proof (succ (succ n) , e)
 = {!!} , {!!}
 where
  IH : Σ m' ꞉ ℕ , ((n +ℕ n) ＝ m')
  IH = sample-proof (n , e)
  m' = pr₁ IH
  e' = pr₂ IH
-}

𝔽 : ℕ → 𝓤₀  ̇
𝔽 0 = 𝟘
𝔽 (succ n) = 𝟙 + 𝔽 n

-- Definition 3.1.6
-- COMMENT: Change to finite-linear-order (see Fin)
finite-discrete : 𝓤 ̇ → 𝓤  ̇
finite-discrete X = Σ n ꞉ ℕ , 𝔽 n ≃ X

-- Lemma 3.1.7
𝔽-is-discrete : (n : ℕ) → is-discrete (𝔽 n)
𝔽-is-discrete 0 = 𝟘-is-discrete
𝔽-is-discrete (succ n) = +-is-discrete 𝟙-is-discrete (𝔽-is-discrete n)

{- finite-discrete-is-discrete
 : {X : 𝓤 ̇ } → finite-discrete X → is-discrete X
finite-discrete-is-discrete (n , e)
 = equiv-to-discrete e (𝔽-is-discrete n) -}

-- Extras
𝔽-is-set : {n : ℕ} → is-set (𝔽 n)
𝔽-is-set {succ n} = +-is-set 𝟙 (𝔽 n) 𝟙-is-set 𝔽-is-set

finite-is-set : {F : 𝓤 ̇ } → (f : finite-discrete F) → is-set F
finite-is-set (n , f) = equiv-to-set (≃-sym f) 𝔽-is-set

𝟚-finite : finite-discrete 𝟚
𝟚-finite = 2 , qinveq g (h , η , μ)
 where
  g : 𝔽 2 → 𝟚
  g (inl ⋆) = ₀
  g (inr (inl ⋆)) = ₁
  h : 𝟚 → 𝔽 2
  h ₀ = inl ⋆
  h ₁ = inr (inl ⋆)
  η : h ∘ g ∼ id
  η (inl ⋆) = refl
  η (inr (inl ⋆)) = refl
  μ : g ∘ h ∼ id
  μ ₀ = refl
  μ ₁ = refl

```

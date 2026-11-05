Chuangjie Xu, November 2026

\begin{code}

{-# OPTIONS --without-K --safe #-}

module gist.InductiveBars.Sequences where

open import MLTT.Spartan
open import MLTT.List
open import Naturals.Order

length-++-right : {A : 𝓤 ̇} (s t : List A)
                → length t ≤ℕ length (s ++ t)
length-++-right [] t = ≤-refl (length t)
length-++-right (a ∷ s) t
 = ≤-trans (length t) (length (s ++ t)) (succ (length (s ++ t)))
    (length-++-right s t) (≤-succ (length (s ++ t)))

_extends_ : {A : 𝓤 ̇} → (ℕ → A) → List A → 𝓤 ̇
α extends [] = 𝟙
α extends (n ∷ s) = (α 0 ＝ n) × ((α ∘ succ) extends s)

extends-++ : {A : 𝓤 ̇} (α : ℕ → A) (s t : List A)
           → α extends (s ++ t) → α extends s
extends-++ α [] t e = ⋆
extends-++ α (n ∷ s) t e = pr₁ e , extends-++ (α ∘ succ) s t (pr₂ e)

infixr 2 _++∞_

_++∞_ : {A : 𝓤 ̇} → List A → (ℕ → A) → (ℕ → A)
([]      ++∞ α)  i       = α i
((x ∷ s) ++∞ α)  0       = x
((x ∷ s) ++∞ α) (succ i) = (s ++∞ α) i

++∞-extends : {A : 𝓤 ̇} (s : List A) (α : ℕ → A)
            → (s ++∞ α) extends s
++∞-extends []      α = ⋆
++∞-extends (x ∷ s) α = refl , ++∞-extends s α

pad : List ℕ → (ℕ → ℕ)
pad s = s ++∞ (λ _ → 0)

pad-extends : (s : List ℕ) → pad s extends s
pad-extends s = ++∞-extends s (λ _ → 0)

prefix : {A : 𝓤 ̇} → ℕ → (ℕ → A) → List A
prefix 0        α = []
prefix (succ n) α = α 0 ∷ prefix n (α ∘ succ)

extends-prefix-decomposition
 : {A : 𝓤 ̇} (α : ℕ → A) (s : List A) (n : ℕ)
 → α extends s
 → n ≤ℕ length s
 → Σ t ꞉ List A , prefix n α ++ t ＝ s
extends-prefix-decomposition α s 0 _ _ = s , refl
extends-prefix-decomposition α [] (succ n) _ ()
extends-prefix-decomposition α (a ∷ s) (succ n) (refl , e) r
 = t , ap (α 0 ∷_) p
 where
  ih : Σ t ꞉ _ , prefix n (α ∘ succ) ++ t ＝ s
  ih = extends-prefix-decomposition (α ∘ succ) s n e r
  t = pr₁ ih
  p = pr₂ ih

lookup : {A : 𝓤 ̇} (s : List A) {i : ℕ} → i <ℕ length s → A
lookup [] ()
lookup (a ∷ s) {0} ⋆ = a
lookup (a ∷ s) {succ i} r = lookup s r

extends-lookup : {A : 𝓤 ̇} (s : List A) (i : ℕ) (r : i <ℕ length s)
               → (α : ℕ → A) → α extends s
               → α i ＝ lookup s r
extends-lookup [] _ ()
extends-lookup (n ∷ s) 0 r α e = pr₁ e
extends-lookup (n ∷ s) (succ i) r α e
 = extends-lookup s i r (α ∘ succ) (pr₂ e)

finite-upper-bound : (α : ℕ → ℕ) (k : ℕ)
                   → Σ M ꞉ ℕ , ((i : ℕ) → i ≤ℕ k → α i ≤ℕ M)
finite-upper-bound α 0 = α 0 , upper
 where
  upper : (i : ℕ) → i ≤ℕ 0 → α i ≤ℕ α 0
  upper 0 r = ≤-refl (α 0)
  upper (succ i) ()
finite-upper-bound α (succ k) with finite-upper-bound (α ∘ succ) k
... | M , upper = M' , upper'
 where
  M' : ℕ
  M' = max M (α 0)
  upper' : (i : ℕ) → i ≤ℕ succ k → α i ≤ℕ M'
  upper' 0 r = max-≤-upper-bound' (α 0) M
  upper' (succ i) r = ≤-trans (α (succ i)) M M'
                              (upper i r)
                              (max-≤-upper-bound M (α 0))

infix 30 _≤¹_

_≤¹_ : (ℕ → ℕ) → (ℕ → ℕ) → 𝓤₀ ̇
α ≤¹ δ = (i : ℕ) → α i ≤ℕ δ i

\end{code}

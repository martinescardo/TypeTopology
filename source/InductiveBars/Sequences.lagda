Chuangjie Xu, November 2026

\begin{code}

{-# OPTIONS --without-K --safe #-}

module InductiveBars.Sequences where

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
α extends (a ∷ s) = (α 0 ＝ a) × ((α ∘ succ) extends s)

extends-++ : {A : 𝓤 ̇} (α : ℕ → A) (s t : List A)
           → α extends (s ++ t) → α extends s
extends-++ α [] t e = ⋆
extends-++ α (_ ∷ s) t e = pr₁ e , extends-++ (α ∘ succ) s t (pr₂ e)

extends-next : {A : 𝓤 ̇} (α : ℕ → A) (s : List A)
             → α extends s
             → α extends (s ++ [ α (length s) ])
extends-next α [] e = refl , ⋆
extends-next α (_ ∷ s) (p , q) = p , extends-next (α ∘ succ) s q

infixr 2 _++∞_

_++∞_ : {A : 𝓤 ̇} → List A → (ℕ → A) → (ℕ → A)
([]      ++∞ α)  i       = α i
((a ∷ _) ++∞ α)  0       = a
((_ ∷ s) ++∞ α) (succ i) = (s ++∞ α) i

++∞-extends : {A : 𝓤 ̇} (s : List A) (α : ℕ → A)
            → (s ++∞ α) extends s
++∞-extends []      α = ⋆
++∞-extends (_ ∷ s) α = refl , ++∞-extends s α

pad-with : {A : 𝓤 ̇} → A → List A → ℕ → A
pad-with a s = s ++∞ (λ _ → a)

pad : List ℕ → (ℕ → ℕ)
pad = pad-with 0

pad-extends : {A : 𝓤 ̇} {a : A} → (s : List A) → (pad-with a s) extends s
pad-extends {a = a} s = ++∞-extends s (λ _ → a)

prefix : {A : 𝓤 ̇} → ℕ → (ℕ → A) → List A
prefix 0        α = []
prefix (succ n) α = α 0 ∷ prefix n (α ∘ succ)

extends-prefix : {A : 𝓤 ̇} (α : ℕ → A) (n : ℕ) → α extends (prefix n α)
extends-prefix α 0 = ⋆
extends-prefix α (succ n) = refl , extends-prefix (α ∘ succ) n

extends-prefix-decomposition
 : {A : 𝓤 ̇} (α : ℕ → A) (s : List A) (n : ℕ)
 → α extends s
 → n ≤ℕ length s
 → Σ t ꞉ List A , prefix n α ++ t ＝ s
extends-prefix-decomposition α s 0 _ _ = s , refl
extends-prefix-decomposition α [] (succ n) _ ()
extends-prefix-decomposition α (a ∷ s) (succ n) (refl , e) r
 using (t , p) ← extends-prefix-decomposition (α ∘ succ) s n e r
 = t , ap (α 0 ∷_) p

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
finite-upper-bound α (succ k)
 using (M , upper) ← finite-upper-bound (α ∘ succ) k
 = M' , upper'
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

_＝⦅_⦆_ : {A : 𝓤 ̇} → (ℕ → A) → ℕ → (ℕ → A) → 𝓤 ̇
α ＝⦅ 0      ⦆ β = 𝟙
α ＝⦅ succ n ⦆ β = (α 0 ＝ β 0) × (α ∘ succ) ＝⦅ n ⦆ (β ∘ succ)

＝⦅⦆-≤ : {A : 𝓤 ̇} (α β : ℕ → A) {m n : ℕ} → m ≤ℕ n
      → α ＝⦅ n ⦆ β → α ＝⦅ m ⦆ β
＝⦅⦆-≤ α β {0} {n} ⋆ _ = ⋆
＝⦅⦆-≤ α β {succ m} {0} ()
＝⦅⦆-≤ α β {succ m} {succ n} r e
 = pr₁ e , ＝⦅⦆-≤ (α ∘ succ) (β ∘ succ) r (pr₂ e)

agreement-preserves-extension
 : {A : 𝓤 ̇} (α β : ℕ → A) (s : List A)
 → α extends s
 → α ＝⦅ length s ⦆ β
 → β extends s
agreement-preserves-extension α β [] eαs es = ⋆
agreement-preserves-extension α β (n ∷ s) (refl , p) (e , q) = e' , IH
 where
  e' : β 0 ＝ α 0
  e' = e ⁻¹
  IH : (β ∘ succ) extends s
  IH = agreement-preserves-extension (α ∘ succ) (β ∘ succ) s p q

agreement-implies-extends-prefix
 : {A : 𝓤 ̇} (α β : ℕ → A) (n : ℕ)
 → α ＝⦅ n ⦆ β
 → β extends (prefix n α)
agreement-implies-extends-prefix α β 0 e = ⋆
agreement-implies-extends-prefix α β (succ n) (p , q)
 = (p ⁻¹) , agreement-implies-extends-prefix (α ∘ succ) (β ∘ succ) n q

extends-prefix-implies-agreement
 : {A : 𝓤 ̇} (α β : ℕ → A) (n : ℕ)
 → β extends (prefix n α)
 → α ＝⦅ n ⦆ β
extends-prefix-implies-agreement α β 0 e = ⋆
extends-prefix-implies-agreement α β (succ n) (p , q)
 = (p ⁻¹) , extends-prefix-implies-agreement (α ∘ succ) (β ∘ succ) n q

\end{code}

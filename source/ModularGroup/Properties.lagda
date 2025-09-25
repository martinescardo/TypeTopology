Lane Biocini, 17 October 2023

Elementary proofs about 𝓜

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module ModularGroup.Properties where

open import MLTT.Spartan
open import MLTT.Plus-Properties using (+functor)
open import MLTT.Unit-Properties using (𝟙-is-not-𝟘)

open import UF.DiscreteAndSeparated using (is-discrete; discrete-types-are-sets)
open import UF.Sets using (is-set)

open import ModularGroup.Type

s-quotiented : id ∼ s ∘ s
s-quotiented E = refl
s-quotiented S = refl
s-quotiented (𝒔 x) = refl
s-quotiented (θ x) = refl

r-quotiented : id ∼ r ∘ r ∘ r
r-quotiented (η x) = refl
r-quotiented (𝒓 x) = refl
r-quotiented (𝒓² x) = refl

s-left-cancellable : left-cancellable s
s-left-cancellable {x} {y} p = s-quotiented x ∙ ap s p ∙ s-quotiented y ⁻¹

r-left-cancellable : left-cancellable r
r-left-cancellable {x} {y} p = r-quotiented x ∙ ap r² p ∙ r-quotiented y ⁻¹

r²-left-cancellable : left-cancellable r²
r²-left-cancellable = r-left-cancellable ∘ r-left-cancellable

if-s-equals-id : (x : 𝓜) → s x ＝ E → x ＝ S
if-s-equals-id x = s-left-cancellable

if-r-equals-id : (x : 𝓜) → r x ＝ E → x ＝ R²
if-r-equals-id x = r-left-cancellable

if-r²-equals-id : (x : 𝓜) → r² x ＝ E → x ＝ R
if-r²-equals-id x = r²-left-cancellable

η-left-cancellable : left-cancellable η
θ-left-cancellable : left-cancellable θ
η-left-cancellable {𝐸} {𝐸} p = refl
η-left-cancellable {𝑆} {𝑆} p = refl
η-left-cancellable {𝑠 x} {𝑠 y} p = ap 𝑠 (θ-left-cancellable (ap tail p))
θ-left-cancellable {𝑟 x} {𝑟 y} p = ap 𝑟 (η-left-cancellable (ap tail p))
θ-left-cancellable {𝑟² x} {𝑟² y} p = ap 𝑟² (η-left-cancellable (ap tail (ap tail p)))

\end{code}

Negation proofs

\begin{code}

S-is-not-E : S ≠ E
S-is-not-E p = 𝟙-is-not-𝟘 (g (η-left-cancellable p))
 where
  f : (x : 𝓢) → 𝓤₀ ̇
  f 𝐸 = 𝟘
  f 𝑆 = 𝟙
  f (𝑠 x) = 𝟘

  g : 𝑆 ＝ 𝐸 → 𝟙 ＝ 𝟘
  g = ap f

η-is-not-θ : (x : 𝓢) (y : 𝓡) → η x ≠ θ y
η-is-not-θ x y p = 𝟙-is-not-𝟘 (g p)
 where
  f : 𝓜 → 𝓤₀ ̇
  f (η x) = 𝟙
  f (θ x) = 𝟘

  g : η x ＝ θ y → 𝟙 ＝ 𝟘
  g = ap f

θ-is-not-η : (x : 𝓡) (y : 𝓢) → θ x ≠ η y
θ-is-not-η x y p = η-is-not-θ y x (p ⁻¹)

\end{code}

Proofs about the decidability of 𝓜

\begin{code}

fibers-of-η-over-E : (x : 𝓢) → is-decidable (η x ＝ E)
fibers-of-η-over-E 𝐸 = inl refl
fibers-of-η-over-E 𝑆 = inr S-is-not-E
fibers-of-η-over-E (𝑠 x) = inr (λ p → θ-is-not-η x 𝑆 (ap s p))

fibers-of-η-over-S : (x : 𝓢) → is-decidable (η x ＝ S)
fibers-of-η-over-S 𝐸 = inr (λ p → S-is-not-E (p ⁻¹))
fibers-of-η-over-S 𝑆 = inl refl
fibers-of-η-over-S (𝑠 x) = inr λ p → θ-is-not-η x 𝐸 (ap s p)

fibers-of-η-over-𝑠 : (x : 𝓢) (y : 𝓡) → is-decidable (η x ＝ η (𝑠 y))
fibers-of-θ-over-𝑟 : (x : 𝓡) (y : 𝓢) → is-decidable (θ x ＝ θ (𝑟 y))
fibers-of-θ-over-𝑟² : (x : 𝓡) (y : 𝓢) → is-decidable (θ x ＝ θ (𝑟² y))

η-is-decidable : (x y : 𝓢) → is-decidable (η x ＝ η y)
θ-is-decidable : (x y : 𝓡) → is-decidable (θ x ＝ θ y)

fibers-of-η-over-𝑠 𝐸 y = inr (𝟘-elim ∘ η-is-not-θ 𝑆 y ∘ ap s)
fibers-of-η-over-𝑠 𝑆 y = inr (𝟘-elim ∘ η-is-not-θ 𝐸 y ∘ ap s)
fibers-of-η-over-𝑠 (𝑠 x) y =
  +functor (ap s) (contrapositive s-left-cancellable) (θ-is-decidable x y)

fibers-of-θ-over-𝑟 (𝑟 x) y =
  +functor (ap r) (contrapositive r-left-cancellable) (η-is-decidable x y)
fibers-of-θ-over-𝑟 (𝑟² x) y = inr (𝟘-elim ∘ η-is-not-θ x (𝑟² y) ∘ ap r)

fibers-of-θ-over-𝑟² (𝑟 x) y = inr (𝟘-elim ∘ η-is-not-θ x (𝑟 y) ∘ ap r²)
fibers-of-θ-over-𝑟² (𝑟² x) y =
  +functor (ap r²) (contrapositive r²-left-cancellable) (η-is-decidable x y)

η-is-decidable x 𝐸 = fibers-of-η-over-E x
η-is-decidable x 𝑆 = fibers-of-η-over-S x
η-is-decidable x (𝑠 y) = fibers-of-η-over-𝑠 x y

θ-is-decidable x (𝑟 y) = fibers-of-θ-over-𝑟 x y
θ-is-decidable x (𝑟² y) = fibers-of-θ-over-𝑟² x y

𝓜-is-discrete : is-discrete 𝓜
𝓜-is-discrete (η x) (η y) = η-is-decidable x y
𝓜-is-discrete (η x) (θ y) = inr (η-is-not-θ x y)
𝓜-is-discrete (θ x) (η y) = inr (≠-sym (η-is-not-θ y x))
𝓜-is-discrete (θ x) (θ y) = θ-is-decidable x y

𝓜-is-set : is-set 𝓜
𝓜-is-set = discrete-types-are-sets 𝓜-is-discrete

\end{code}

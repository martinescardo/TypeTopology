Martin Escardo

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-PropTruncAlternative where

open import SpartanMLTT
open import UF-Base public
open import UF-Subsingletons public
open import UF-FunExt public
open import UF-Subsingletons-FunExt public

\end{code}

We can work with propositional truncation as an assumption, but the
drawback is that we can only eliminate in the same universe we
truncate, at least if we don't want to pass the target universe as an
extra parameter in everything. So we are not using this anymore (but
we could now, given that Uω has become available).

\begin{code}

propositional-truncations-exist : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
propositional-truncations-exist 𝓤  𝓥 = (X : 𝓤 ̇) → Σ \(X' : 𝓤 ̇) → is-prop X' × (X → X')
                                        × ((P : 𝓥 ̇) → is-prop P → (X → P) → X' → P)

propositional-truncations-exist' : ∀ 𝓤 → 𝓤 ⁺ ̇
propositional-truncations-exist' 𝓤 = propositional-truncations-exist 𝓤 𝓤

module PropositionalTruncation' (pt : ∀ 𝓤 → propositional-truncations-exist' 𝓤) where

 ∥_∥ : 𝓤 ̇ → 𝓤 ̇
 ∥ X ∥ = pr₁ (pt (universe-of X) X)

 propositional-truncation-is-a-prop : {X : 𝓤 ̇} → is-prop(∥ X ∥)
 propositional-truncation-is-a-prop {𝓤} {X} = pr₁(pr₂(pt (universe-of X) X))

 ∣_∣ : {X : 𝓤 ̇} → X → ∥ X ∥
 ∣ x ∣ = pr₁(pr₂(pr₂(pt (universe-of(type-of x)) (type-of x)))) x

 ptrec : {X Y : 𝓤 ̇} → is-prop Y → (X → Y) → ∥ X ∥ → Y
 ptrec {𝓤} {X} {Y} isp f = pr₂(pr₂(pr₂(pt (universe-of X) X))) Y isp f

 ptfunct : {X Y : 𝓤 ̇} → (X → Y) → ∥ X ∥ → ∥ Y ∥
 ptfunct f = ptrec propositional-truncation-is-a-prop (λ x → ∣ f x ∣)

 ∃ : {X : 𝓤 ̇} → (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
 ∃ Y = ∥ Σ Y ∥

 _∨_  : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
 P ∨ Q = ∥ P + Q ∥

 infixr 0 _∨_
 infix 0 ∥_∥
 infix 0 ∣_∣

\end{code}

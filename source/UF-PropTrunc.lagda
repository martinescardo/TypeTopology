\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-PropTrunc where

open import SpartanMLTT
open import UF-Base public
open import UF-Subsingletons public
open import UF-FunExt public
open import UF-Subsingletons-FunExt public

\end{code}

To use propositional truncation, one needs to assume an element of
PropTrunc, which is a postulated type with no postulated element. This
is use to keep track of which modules or functions depend on
propositional truncation.

\begin{code}

postulate PropTrunc : 𝓤₀ ̇

module PropositionalTruncation (pt : PropTrunc) where

 postulate
   ∥_∥ : 𝓤 ̇ → 𝓤 ̇
   propositional-truncation-is-a-prop : {X : 𝓤 ̇} → is-prop ∥ X ∥
   ∣_∣ : {X : 𝓤 ̇} → X → ∥ X ∥
   ptrec : {X : 𝓤 ̇} {Y : 𝓥 ̇} → is-prop Y → (X → Y) → ∥ X ∥ → Y

 is-singleton'-is-prop : {X : 𝓤 ̇} → funext 𝓤 𝓤 → is-prop(is-prop X × ∥ X ∥)
 is-singleton'-is-prop fe = Σ-is-prop (being-a-prop-is-a-prop fe) (λ _ → propositional-truncation-is-a-prop)

 c-es₁ : {X : 𝓤 ̇} → is-singleton X ⇔ is-prop X × ∥ X ∥
 c-es₁ {𝓤} {X} = f , g
  where
   f : is-singleton X → is-prop X × ∥ X ∥
   f (x , φ) = singletons-are-props (x , φ) , ∣ x ∣

   g : is-prop X × ∥ X ∥ → is-singleton X
   g (i , s) = ptrec i id s , i (ptrec i id s)

 ptfunct : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → ∥ X ∥ → ∥ Y ∥
 ptfunct f = ptrec propositional-truncation-is-a-prop (λ x → ∣ f x ∣)

 ∃ : {X : 𝓤 ̇} → (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
 ∃ Y = ∥ Σ Y ∥

 _∨_  : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
 P ∨ Q = ∥ P + Q ∥

 left-fails-then-right-holds : {P : 𝓤 ̇} {Q : 𝓥 ̇} → is-prop Q → P ∨ Q → ¬ P → Q
 left-fails-then-right-holds i d u = ptrec i (λ d → Left-fails-then-right-holds d u) d

 right-fails-then-left-holds : {P : 𝓤 ̇} {Q : 𝓥 ̇} → is-prop P → P ∨ Q → ¬ Q → P
 right-fails-then-left-holds i d u = ptrec i (λ d → Right-fails-then-left-holds d u) d

 pt-gdn : {X : 𝓤 ̇} → ∥ X ∥ → ∀ {𝓥} (P : 𝓥 ̇) → is-prop P → (X → P) → P
 pt-gdn {𝓤} {X} s {𝓥} P isp u = ptrec isp u s

 gdn-pt : {X : 𝓤 ̇} → (∀ {𝓥} (P : 𝓥 ̇) → is-prop P → (X → P) → P) → ∥ X ∥
 gdn-pt {𝓤} {X} φ = φ ∥ X ∥ propositional-truncation-is-a-prop ∣_∣

 pt-dn : {X : 𝓤 ̇} → ∥ X ∥ → ¬¬ X
 pt-dn s = pt-gdn s 𝟘 𝟘-is-prop

 binary-choice : {X : 𝓤 ̇} {Y : 𝓥 ̇} → ∥ X ∥ → ∥ Y ∥ → ∥ X × Y ∥
 binary-choice s t = ptrec propositional-truncation-is-a-prop (λ x → ptrec propositional-truncation-is-a-prop (λ y → ∣ x , y ∣) t) s

 infixr 0 _∨_
 infix 0 ∥_∥

\end{code}

Or we can work with propositional truncation as an assumption, but the
drawback is that we can only eliminate in the same universe we
truncate, at least if we don't want to pass the target universe as an
extra parameter in everything. So we are not using this anymore.

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

\end{code}

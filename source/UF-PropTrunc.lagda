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

postulate PropTrunc : U₀ ̇

module PropositionalTruncation (pt : PropTrunc) where

 postulate
   ∥_∥ : U ̇ → U ̇
   ptisp : {X : U ̇} → is-prop ∥ X ∥
   ∣_∣ : {X : U ̇} → X → ∥ X ∥
   ptrec : {X : U ̇} {Y : V ̇} → is-prop Y → (X → Y) → ∥ X ∥ → Y

 is-singleton'-is-prop : {X : U ̇} → funext U U → is-prop(is-prop X × ∥ X ∥)
 is-singleton'-is-prop fe = Σ-is-prop (is-prop-is-prop fe) (λ _ → ptisp)

 c-es₁ : {X : U ̇} → is-singleton X ⇔ is-prop X × ∥ X ∥
 c-es₁ {U} {X} = f , g
  where
   f : is-singleton X → is-prop X × ∥ X ∥
   f (x , φ) = is-singleton-is-prop (x , φ) , ∣ x ∣

   g : is-prop X × ∥ X ∥ → is-singleton X
   g (i , s) = ptrec i id s , i (ptrec i id s)

 ptfunct : {X : U ̇} {Y : V ̇} → (X → Y) → ∥ X ∥ → ∥ Y ∥
 ptfunct f = ptrec ptisp (λ x → ∣ f x ∣)

 ∃ : {X : U ̇} → (Y : X → V ̇) → U ⊔ V ̇
 ∃ Y = ∥ Σ Y ∥

 _∨_  : U ̇ → V ̇ → U ⊔ V ̇
 P ∨ Q = ∥ P + Q ∥

 left-fails-then-right-holds : {P : U ̇} {Q : V ̇} → is-prop Q → P ∨ Q → ¬ P → Q
 left-fails-then-right-holds i d u = ptrec i (λ d → Left-fails-then-right-holds d u) d

 right-fails-then-left-holds : {P : U ̇} {Q : V ̇} → is-prop P → P ∨ Q → ¬ Q → P
 right-fails-then-left-holds i d u = ptrec i (λ d → Right-fails-then-left-holds d u) d

 pt-gdn : {X : U ̇} → ∥ X ∥ → ∀ {V} (P : V ̇) → is-prop P → (X → P) → P
 pt-gdn {U} {X} s {V} P isp u = ptrec isp u s

 gdn-pt : {X : U ̇} → (∀ {V} (P : V ̇) → is-prop P → (X → P) → P) → ∥ X ∥
 gdn-pt {U} {X} φ = φ ∥ X ∥ ptisp ∣_∣

 pt-dn : {X : U ̇} → ∥ X ∥ → ¬¬ X
 pt-dn s = pt-gdn s 𝟘 𝟘-is-prop

 binary-choice : {X : U ̇} {Y : V ̇} → ∥ X ∥ → ∥ Y ∥ → ∥ X × Y ∥
 binary-choice s t = ptrec ptisp (λ x → ptrec ptisp (λ y → ∣ x , y ∣) t) s

 infixr 0 _∨_
 infix 0 ∥_∥

\end{code}

Or we can work with propositional truncation as an assumption, but the
drawback is that we can only eliminate in the same universe we
truncate, at least if we don't want to pass the target universe as an
extra parameter in everything. So we are not using this anymore.

\begin{code}

propositional-truncations-exist : ∀ U V → U ′ ⊔ V ′ ̇
propositional-truncations-exist U V = (X : U ̇) → Σ \(X' : U ̇) → is-prop X' × (X → X')
                                        × ((P : V ̇) → is-prop P → (X → P) → X' → P)

propositional-truncations-exist' : ∀ U → U ′ ̇
propositional-truncations-exist' U = propositional-truncations-exist U U

module PropositionalTruncation' (pt : ∀ U → propositional-truncations-exist' U) where

 ∥_∥ : U ̇ → U ̇
 ∥ X ∥ = pr₁ (pt (universe-of X) X)

 ptisp : {X : U ̇} → is-prop(∥ X ∥)
 ptisp {U} {X} = pr₁(pr₂(pt (universe-of X) X))

 ∣_∣ : {X : U ̇} → X → ∥ X ∥
 ∣ x ∣ = pr₁(pr₂(pr₂(pt (universe-of(type-of x)) (type-of x)))) x

 ptrec : {X Y : U ̇} → is-prop Y → (X → Y) → ∥ X ∥ → Y
 ptrec {U} {X} {Y} isp f = pr₂(pr₂(pr₂(pt (universe-of X) X))) Y isp f

 ptfunct : {X Y : U ̇} → (X → Y) → ∥ X ∥ → ∥ Y ∥
 ptfunct f = ptrec ptisp (λ x → ∣ f x ∣)

 ∃ : {X : U ̇} → (Y : X → V ̇) → U ⊔ V ̇
 ∃ Y = ∥ Σ Y ∥

 _∨_  : U ̇ → V ̇ → U ⊔ V ̇
 P ∨ Q = ∥ P + Q ∥

 infixr 0 _∨_
 infix 0 ∥_∥

\end{code}

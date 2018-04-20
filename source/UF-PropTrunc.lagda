\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-PropTrunc where

open import SpartanMLTT public
open import UF-Base public
open import UF-Subsingletons public
open import UF-Yoneda public
open import UF-Retracts public
open import UF-Subsingleton-Retracts public
open import UF-Equiv public
open import UF-LeftCancellable public
open import UF-FunExt public
open import UF-Univalence public
open import UF-Embedding public
open import UF-Subsingleton-FunExt public
open import UF-Retracts-FunExt public

\end{code}

To use propositional truncation, one needs to assume an element of
PropTrunc, which is a postulated type with no postulated element. This
is use to keep track of which modules or functions depend on
propositional truncation.

\begin{code}

postulate PropTrunc : U₀ ̇

module PropositionalTruncation (pt : PropTrunc) where

 postulate
   ∥_∥ : ∀ {U} → U ̇ → U ̇
   ptisp : ∀ {U} {X : U ̇} → isProp ∥ X ∥
   ∣_∣ : ∀ {U} {X : U ̇} → X → ∥ X ∥
   ptrec : ∀ {U V} {X : U ̇} {Y : V ̇} → isProp Y → (X → Y) → ∥ X ∥ → Y

 isSingleton'-isProp : ∀ {U} {X : U ̇} → FunExt U U → isProp(isProp X × ∥ X ∥)
 isSingleton'-isProp fe = isProp-closed-under-Σ (isProp-isProp fe) (λ _ → ptisp)

 c-es₁ : ∀ {U} {X : U ̇} → isSingleton X ⇔ isProp X × ∥ X ∥
 c-es₁ {U} {X} = f , g
  where
   f : isSingleton X → isProp X × ∥ X ∥ 
   f (x , φ) = isSingleton-isProp (x , φ) , ∣ x ∣
   
   g : isProp X × ∥ X ∥ → isSingleton X
   g (i , s) = ptrec i id s , i (ptrec i id s)
   
 ptfunct : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → ∥ X ∥ → ∥ Y ∥
 ptfunct f = ptrec ptisp (λ x → ∣ f x ∣)

 ∃ : ∀ {U V} {X : U ̇} → (Y : X → V ̇) → U ⊔ V ̇
 ∃ Y = ∥ Σ Y ∥

 _∨_ : ∀ {U} {V} → U ̇ → V ̇ → U ⊔ V ̇
 P ∨ Q = ∥ P + Q ∥

 left-fails-then-right-holds : ∀ {U} {V} {P : U ̇} {Q : V ̇} → isProp Q → P ∨ Q → ¬ P → Q
 left-fails-then-right-holds i d u = ptrec i (λ d → Left-fails-then-right-holds d u) d

 right-fails-then-left-holds : ∀ {U} {V} {P : U ̇} {Q : V ̇} → isProp P → P ∨ Q → ¬ Q → P
 right-fails-then-left-holds i d u = ptrec i (λ d → Right-fails-then-left-holds d u) d

 pt-gdn : ∀ {U} {X : U ̇} → ∥ X ∥ → ∀ {V} (P : V ̇) → isProp P → (X → P) → P
 pt-gdn {U} {X} s {V} P isp u = ptrec isp u s

 gdn-pt : ∀ {U} {X : U ̇} → (∀ {V} (P : V ̇) → isProp P → (X → P) → P) → ∥ X ∥ 
 gdn-pt {U} {X} φ = φ ∥ X ∥ ptisp ∣_∣

 pt-dn : ∀ {U} {X : U ̇} → ∥ X ∥ → ¬¬ X
 pt-dn s = pt-gdn s 𝟘 𝟘-isProp

 binary-choice : ∀ {U V} {X : U ̇} {Y : V ̇} → ∥ X ∥ → ∥ Y ∥ → ∥ X × Y ∥
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
propositional-truncations-exist U V = (X : U ̇) → Σ \(X' : U ̇) → isProp X' × (X → X')
                                        × ((P : V ̇) → isProp P → (X → P) → X' → P)

propositional-truncations-exist' : ∀ U → U ′ ̇
propositional-truncations-exist' U = propositional-truncations-exist U U

module PropositionalTruncation' (pt : ∀ U → propositional-truncations-exist' U) where

 ∥_∥ : ∀ {U} → U ̇ → U ̇
 ∥ X ∥ = pr₁ (pt (universeOf X) X)

 ptisp : ∀ {U} {X : U ̇} → isProp(∥ X ∥)
 ptisp {U} {X} = pr₁(pr₂(pt (universeOf X) X))

 ∣_∣ : ∀ {U} {X : U ̇} → X → ∥ X ∥
 ∣ x ∣ = pr₁(pr₂(pr₂(pt (universeOf(typeOf x)) (typeOf x)))) x

 ptrec : ∀ {U} {X Y : U ̇} → isProp Y → (X → Y) → ∥ X ∥ → Y
 ptrec {U} {X} {Y} isp f = pr₂(pr₂(pr₂(pt (universeOf X) X))) Y isp f

 ptfunct : ∀ {U} {X Y : U ̇} → (X → Y) → ∥ X ∥ → ∥ Y ∥
 ptfunct f = ptrec ptisp (λ x → ∣ f x ∣)

 ∃ : ∀ {U V} {X : U ̇} → (Y : X → V ̇) → U ⊔ V ̇
 ∃ Y = ∥ Σ Y ∥

 _∨_ : ∀ {U} {V} → U ̇ → V ̇ → U ⊔ V ̇
 P ∨ Q = ∥ P + Q ∥

 infixr 0 _∨_
 infix 0 ∥_∥

\end{code}


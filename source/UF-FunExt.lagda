Formulation of function extensionality

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-FunExt where

open import UF-Base
open import UF-Equiv
open import UF-LeftCancellable

FunExt : ∀ U V → U ′ ⊔ V ′ ̇
FunExt U V = {X : U ̇} {A : X → V ̇} (f g : Π A) → isEquiv (happly' f g)

≃-funext : ∀ U V → FunExt U V → {X : U ̇} {A : X → V ̇} (f g : Π A)
         → (f ≡ g) ≃ ((x : X) → f x ≡ g x)
≃-funext U V fe f g = happly' f g , fe f g

funext : ∀ {U V} (fe : FunExt U V) {X : U ̇} {A : X → V ̇} {f g : Π A} 
       → ((x : X) → f x ≡ g x) → f ≡ g
funext fe {X} {A} {f} {g} = pr₁(pr₁(fe f g))

happly-funext : ∀ {U V} {X : U ̇} {A : X → V ̇}
                (fe : FunExt U V) (f g : Π A) (h : f ∼ g)
              → happly (funext fe h) ≡ h
happly-funext fe f g = pr₂(pr₁(fe f g))

funext-lc : ∀ {U V} {X : U ̇} {A : X → V ̇} (fe : FunExt U V) 
         → (f g : Π A) → left-cancellable (funext fe {X} {A} {f} {g})
funext-lc fe f g = section-lc (funext fe) (happly , happly-funext fe f g)

happly-lc : ∀ {U V} {X : U ̇} {A : X → V ̇} (fe : FunExt U V) (f g : Π A) 
         → left-cancellable(happly' f g)
happly-lc fe f g = section-lc happly ((pr₂ (fe f g)))

\end{code}

Formulation of function extensionality

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-LeftCancellable

\end{code}

The appropriate notion of function extensionality in univalent
mathematics is funext, define below. It is implied, by an argument due
to Voevodky, by naive, non-dependent function extensionality, written
naive-funext here.

\begin{code}

naive-funext : ∀ U V → U ′ ⊔ V ′ ̇
naive-funext U V = {X : U ̇} {Y : V ̇} {f g : X → Y} → f ∼ g → f ≡ g

DN-funext : ∀ U V → U ′ ⊔ V ′ ̇
DN-funext U V = {X : U ̇} {A : X → V ̇} {f g : Π A} → f ∼ g → f ≡ g

funext : ∀ U V → U ′ ⊔ V ′ ̇
funext U V = {X : U ̇} {A : X → V ̇} (f g : Π A) → is-equiv (happly' f g)

≃-funext : ∀ U V → funext U V → {X : U ̇} {A : X → V ̇} (f g : Π A)
         → (f ≡ g) ≃ ((x : X) → f x ≡ g x)
≃-funext U V fe f g = happly' f g , fe f g

dfunext : ∀ {U V} → funext U V → DN-funext U V
dfunext fe {X} {A} {f} {g} = pr₁(pr₁(fe f g))

nfunext : ∀ {U V} → funext U V → naive-funext U V
nfunext fe = dfunext fe 

happly-funext : ∀ {U V} {X : U ̇} {A : X → V ̇}
                (fe : funext U V) (f g : Π A) (h : f ∼ g)
              → happly (dfunext fe h) ≡ h
happly-funext fe f g = pr₂(pr₁(fe f g))

funext-lc : ∀ {U V} {X : U ̇} {A : X → V ̇} (fe : funext U V) 
         → (f g : Π A) → left-cancellable (dfunext fe {X} {A} {f} {g})
funext-lc fe f g = section-lc (dfunext fe) (happly , happly-funext fe f g)

happly-lc : ∀ {U V} {X : U ̇} {A : X → V ̇} (fe : funext U V) (f g : Π A) 
         → left-cancellable(happly' f g)
happly-lc fe f g = section-lc happly ((pr₂ (fe f g)))

\end{code}

The following is taken from this thread:
https://groups.google.com/forum/#!msg/homotopytypetheory/VaLJM7S4d18/Lezr_ZhJl6UJ

\begin{code}

transport-funext : ∀ {U V W} {X : U ̇} (A : X → V ̇) (P : (x : X) → A x → W ̇) (fe : funext U V)
                   (f g : Π A)
                   (φ : (x : X) → P x (f x))
                   (h : f ∼ g)
                   (x : X)
                 → (transport (λ - → (x : X) → P x (- x)) (dfunext fe h) φ) x
                 ≡  transport (P x) (h x) (φ x)
transport-funext A P fe f g φ h x = q ∙ r
 where
  l : (f g : Π A) (φ : ∀ x → P x (f x)) (p : f ≡ g) 
        → ∀ x → (transport (λ - → ∀ x → P x (- x)) p φ) x
               ≡ transport (P x) (happly p x) (φ x)
  l f .f φ refl x = refl

  q : (transport (λ - → ∀ x → P x (- x)) (dfunext fe h) φ) x
    ≡ transport (P x) (happly (dfunext fe h) x) (φ x)
  q = l f g φ (dfunext fe h) x

  r :  transport (P x) (happly (dfunext fe h) x) (φ x) 
     ≡ transport (P x) (h x) (φ x)
  r = ap (λ - → transport (P x) (- x) (φ x)) (happly-funext fe f g h)

\end{code}

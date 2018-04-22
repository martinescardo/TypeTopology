Left cancellable maps.

The definition is given in UF-Base. Here we prove things about them.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-LeftCancellable where

open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Equiv

left-cancellable-reflects-isProp : ∀ {U V} {X : U ̇} {Y : V ̇} (f : X → Y)
                                 → left-cancellable f → isProp Y → isProp X
left-cancellable-reflects-isProp f lc i x x' = lc (i (f x) (f x'))

section-lc : ∀ {U V} {X : U ̇} {A : V ̇} (s : X → A) → hasRetraction s → left-cancellable s
section-lc {U} {V} {X} {Y} s (r , rs) {x} {y} p = (rs x)⁻¹ ∙ ap r p ∙ rs y

isEquiv-lc : ∀ {U} {X Y : U ̇} (f : X → Y) → isEquiv f → left-cancellable f
isEquiv-lc f (_ , hasr) = section-lc f hasr 

left-cancellable-closed-under-∘ : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇} (f : X → Y) (g : Y → Z)
                                → left-cancellable f → left-cancellable g → left-cancellable (g ∘ f)
left-cancellable-closed-under-∘ f g lcf lcg = lcf ∘ lcg

NatΠ-lc : ∀ {U V W} {X : U ̇} {A : X → V ̇} {B : X → W ̇} (f : Nat A B)
    → ((x : X) → left-cancellable(f x))
    → {g g' : Π A} → NatΠ f g ≡ NatΠ f g' → g ∼ g'
NatΠ-lc f flc {g} {g'} p x = flc x (happly p x)

\end{code}


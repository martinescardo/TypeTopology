Left cancellable maps.

The definition is given in UF-Base. Here we prove things about them.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-LeftCancellable where

open import SpartanMLTT
open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Equiv

left-cancellable-reflects-is-prop : {X : U ̇} {Y : V ̇} (f : X → Y)
                                 → left-cancellable f → is-prop Y → is-prop X
left-cancellable-reflects-is-prop f lc i x x' = lc (i (f x) (f x'))

section-lc : {X : U ̇} {A : V ̇} (s : X → A) → has-retraction s → left-cancellable s
section-lc {U} {V} {X} {Y} s (r , rs) {x} {y} p = (rs x)⁻¹ ∙ ap r p ∙ rs y

is-equiv-lc : {X Y : U ̇} (f : X → Y) → is-equiv f → left-cancellable f
is-equiv-lc f (_ , hasr) = section-lc f hasr

left-cancellable-closed-under-∘ : {X : U ̇} {Y : V ̇} {Z : W ̇} (f : X → Y) (g : Y → Z)
                                → left-cancellable f → left-cancellable g → left-cancellable (g ∘ f)
left-cancellable-closed-under-∘ f g lcf lcg = lcf ∘ lcg

NatΣ-lc : {X : U ̇} {A : X → V ̇} {B : X → W ̇} (f : Nat A B)
        → ((x : X) → left-cancellable(f x))
        → left-cancellable (NatΣ f)
NatΣ-lc {U} {V} {W} {X} {A} {B} f flc {x , a} {x' , a'} p = to-Σ-≡ (ap pr₁ p , γ)
 where
  γ : transport A (ap pr₁ p) a ≡ a'
  γ = flc x' (f x' (transport A (ap pr₁ p) a) ≡⟨ nat-transport f (ap pr₁ p) ⟩
              transport B (ap pr₁ p) (f x a)  ≡⟨ from-Σ-≡' p ⟩
              f x' a'                         ∎)

NatΠ-lc : {X : U ̇} {A : X → V ̇} {B : X → W ̇} (f : Nat A B)
        → ((x : X) → left-cancellable(f x))
        → {g g' : Π A} → NatΠ f g ≡ NatΠ f g' → g ∼ g'
NatΠ-lc f flc {g} {g'} p x = flc x (happly p x)

\end{code}

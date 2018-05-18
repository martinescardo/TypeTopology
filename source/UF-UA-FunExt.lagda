Martin Escardo, 9th April 2018

We give Voevodsky's original proof that univalence implies
non-dependent function extensionality, as presented by Gambino,
Kapulkin and Lumsdaine in
http://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-UA-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Univalence
open import UF-LeftCancellable

Δ : ∀ {U} → U ̇ → U ̇
Δ X = Σ \(x : X) → Σ \(y : X) → x ≡ y

δ : ∀ {U} {X : U ̇} → X → Δ X
δ x = (x , x , refl)

π₁ π₂ : ∀ {U} {X : U ̇} → Δ X → X
π₁ (x , _ , _) = x
π₂ (_ , y , _) = y

δ-isEquiv : ∀ {U} {X : U ̇} → isEquiv (δ {U} {X})
δ-isEquiv {U} {X} = (π₁ , η) , (π₁ , ε)
 where
  η : (d : Δ X) → δ (π₁ d) ≡ d
  η (x , _ , refl) = refl
  ε : (x : X) → π₁ (δ x) ≡ x
  ε x = refl

πδ : ∀ {U} (X : U ̇) → π₁ ∘ δ ≡ π₂ ∘ δ
πδ {U} X = refl {U} {X → X}

π₁-equals-π₂ : ∀ {U} → isUnivalent U → {X : U ̇} → π₁ ≡ π₂
π₁-equals-π₂ ua {X} = isEquiv-lc (λ(g : Δ X → X) → g ∘ δ) (preComp-isEquiv ua δ  δ-isEquiv) (πδ X)

fe : ∀ {U} → isUnivalent U → ∀ {V} {X : V ̇} {Y : U ̇} (f₁ f₂ : X → Y) → f₁ ∼ f₂ → f₁ ≡ f₂
fe ua f₁ f₂ h = f₁                              ≡⟨ refl ⟩
               (λ x → f₁ x)                    ≡⟨ refl ⟩ 
               (λ x → π₁ (f₁ x , f₂ x , h x))  ≡⟨ ap (λ π x → π (f₁ x , f₂ x , h x)) (π₁-equals-π₂ ua) ⟩
               (λ x → π₂ (f₁ x , f₂ x , h x))  ≡⟨ refl ⟩
               (λ x → f₂ x)                    ≡⟨ refl ⟩ 
               f₂                               ∎
\end{code}

We prove that Pi of a family of contractible types is contractible;
this is well-known to imply full dependent funext.

1. If each P(x) is contractible, then the projection pr1 : Sigma{x:X}
P(x) --> X is an equivalence.  This requires no funext.
2. If (f : A -> B) is an equivalence, then so is postcomposition with
it (X -> A) -> (X -> B).  This requires only non-dependent funext.
3. Thus, postcomposition with pr1 is an equivalence (X -> Sigma{x:X}
P(x)) --> (X -> X).
4. Therefore, the fiber of "postcomposition with pr1" over idmap : X
-> X is contractible.  (This is VV's *definition* of equivalence, but
all notions of equivalence are *logically* equivalent without any
funext, so it doesn't matter which we use.)
5. The latter fiber is "the type of sections of pr1", so it is
equivalent to Pi(x:X) P(x).  Proving this requires full funext, but
without any funext we can prove that Pi(x:X) P(x) is a *retract* of
this fiber, and hence inherits contractibility from it.


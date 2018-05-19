Martin Escardo, 9th April 2018

We first give Voevodsky's original proof that univalence implies
non-dependent, naive function extensionality, as presented by Gambino,
Kapulkin and Lumsdaine in
http://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf.

We then deduce dependent function extensionality applying a second
argument by Voevodsky, developed in another module, which doesn't
depend on univalence.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-UA-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Univalence
open import UF-LeftCancellable
open import UF-FunExt
open import UF-FunExt-from-Naive-FunExt

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

NFunExt-from-Univalence : ∀ {U} → isUnivalent U → ∀ {V} → NFunExt V U
NFunExt-from-Univalence ua {V} {X} {Y} {f₁} {f₂} h =
  f₁                               ≡⟨ refl ⟩
  (λ x → f₁ x)                    ≡⟨ refl ⟩ 
  (λ x → π₁ (f₁ x , f₂ x , h x))  ≡⟨ ap (λ π x → π (f₁ x , f₂ x , h x)) (π₁-equals-π₂ ua) ⟩
  (λ x → π₂ (f₁ x , f₂ x , h x))  ≡⟨ refl ⟩
  (λ x → f₂ x)                    ≡⟨ refl ⟩ 
  f₂                               ∎

\end{code}

Added 19th May 2018:

\begin{code}

FunExt-from-Univalence : ∀ {U} → isUnivalent U → FunExt U U
FunExt-from-Univalence ua = NFunExt-gives-FunExt' (NFunExt-from-Univalence ua)

\end{code}

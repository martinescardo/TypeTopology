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

naive-funext-from-univalence : ∀ {U} → is-univalent U → ∀ {V} → naive-funext V U
naive-funext-from-univalence {U} ua {V} {X} {Y} {f₁} {f₂} h = γ
 where
  Δ : U ̇ → U ̇
  Δ X = Σ \(x : X) → Σ \(y : X) → x ≡ y

  δ : {X : U ̇} → X → Δ X
  δ x = (x , x , refl)

  π₁ π₂ : {X : U ̇} → Δ X → X
  π₁ (x , _ , _) = x
  π₂ (_ , y , _) = y

  δ-is-equiv : {X : U ̇} → is-equiv δ
  δ-is-equiv {X} = (π₁ , η) , (π₁ , ε)
   where
    η : (d : Δ X) → δ (π₁ d) ≡ d
    η (x , _ , refl) = refl
    ε : (x : X) → π₁ (δ x) ≡ x
    ε x = refl

  πδ : (X : U ̇) → π₁ ∘ δ ≡ π₂ ∘ δ
  πδ X = refl

  π₁-equals-π₂ : {X : U ̇} → π₁ ≡ π₂
  π₁-equals-π₂ {X} = is-equiv-lc (λ(g : Δ X → X) → g ∘ δ)
                                 (preComp-is-equiv ua δ δ-is-equiv) (πδ X)

  γ : f₁ ≡ f₂
  γ = f₁                              ≡⟨ refl ⟩
      (λ x → f₁ x)                    ≡⟨ refl ⟩
      (λ x → π₁ (f₁ x , f₂ x , h x))  ≡⟨ ap (λ π x → π (f₁ x , f₂ x , h x)) π₁-equals-π₂ ⟩
      (λ x → π₂ (f₁ x , f₂ x , h x))  ≡⟨ refl ⟩
      (λ x → f₂ x)                    ≡⟨ refl ⟩
      f₂                              ∎

\end{code}

Added 19th May 2018:

\begin{code}

funext-from-univalence : ∀ {U} → is-univalent U → funext U U
funext-from-univalence ua = naive-funext-gives-funext (naive-funext-from-univalence ua)

\end{code}

Added 27 Jun 2018:

\begin{code}

funext-from-univalence' : ∀ U V → is-univalent U → is-univalent (U ⊔ V) → funext U V
funext-from-univalence' U V ua ua' = naive-funext-gives-funext'
                                       (naive-funext-from-univalence ua')
                                       (naive-funext-from-univalence ua)

global-funext-from-univalence : (∀ U → is-univalent U) → ∀ U V → funext U V
global-funext-from-univalence ua U V = funext-from-univalence' U V (ua U) (ua (U ⊔ V))

funext-from-successive-univalence : ∀ U → is-univalent U → is-univalent (U ′) → funext U (U ′)
funext-from-successive-univalence U = funext-from-univalence' U (U ′)

\end{code}

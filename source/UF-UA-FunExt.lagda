Martin Escardo, 9th April 2018

We first give Voevodsky's original proof that univalence implies
non-dependent, naive function extensionality, as presented by Gambino,
Kapulkin and Lumsdaine in
http://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf.

We then deduce dependent function extensionality applying a second
argument by Voevodsky, developed in another module, which doesn't
depend on univalence.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-UA-FunExt where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Univalence
open import UF-LeftCancellable
open import UF-FunExt
open import UF-FunExt-from-Naive-FunExt

naive-funext-from-univalence : is-univalent 𝓤 → ∀ {𝓥} → naive-funext 𝓥 𝓤
naive-funext-from-univalence {𝓤} ua {𝓥} {X} {Y} {f₁} {f₂} h = γ
 where
  Δ : 𝓤 ̇ → 𝓤 ̇
  Δ X = Σ \(x : X) → Σ \(y : X) → x ≡ y

  δ : {X : 𝓤 ̇} → X → Δ X
  δ x = (x , x , refl)

  π₁ π₂ : {X : 𝓤 ̇} → Δ X → X
  π₁ (x , _ , _) = x
  π₂ (_ , y , _) = y

  δ-is-equiv : {X : 𝓤 ̇} → is-equiv δ
  δ-is-equiv {X} = (π₁ , η) , (π₁ , ε)
   where
    η : (d : Δ X) → δ (π₁ d) ≡ d
    η (x , _ , refl) = refl
    ε : (x : X) → π₁ (δ x) ≡ x
    ε x = refl

  πδ : (X : 𝓤 ̇) → π₁ ∘ δ ≡ π₂ ∘ δ
  πδ X = refl

  π₁-equals-π₂ : {X : 𝓤 ̇} → π₁ ≡ π₂
  π₁-equals-π₂ {X} = is-equiv-lc (λ(g : Δ X → X) → g ∘ δ)
                                 (pre-comp-is-equiv ua δ δ-is-equiv) (πδ X)

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

funext-from-univalence : is-univalent 𝓤 → funext 𝓤 𝓤
funext-from-univalence ua = naive-funext-gives-funext (naive-funext-from-univalence ua)

\end{code}

Added 27 Jun 2018:

\begin{code}

funext-from-univalence' : ∀ 𝓤 𝓥 → is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → funext 𝓤 𝓥
funext-from-univalence' 𝓤 𝓥 ua ua' = naive-funext-gives-funext'
                                       (naive-funext-from-univalence ua')
                                       (naive-funext-from-univalence ua)

global-funext-from-univalence : (∀ 𝓤 → is-univalent 𝓤) → global-funext
global-funext-from-univalence ua 𝓤 𝓥 = funext-from-univalence' 𝓤 𝓥 (ua 𝓤) (ua (𝓤 ⊔ 𝓥))

funext-from-successive-univalence : ∀ 𝓤 → is-univalent 𝓤 → is-univalent (𝓤 ⁺) → funext 𝓤 (𝓤 ⁺)
funext-from-successive-univalence 𝓤 = funext-from-univalence' 𝓤 (𝓤 ⁺)

open import UF-Subsingletons
open import UF-Subsingletons-FunExt

PropExt-from-univalence : is-univalent 𝓤
                        → {p q : Ω 𝓤} → (p holds → q holds) → (q holds → p holds) → p ≡ q
PropExt-from-univalence {𝓤} ua {p} {q} = PropExt (funext-from-univalence ua) (propext-from-univalence ua)

\end{code}

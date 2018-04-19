Martin Escardo, 9th April 2018

We first give Voevodsky's original proof that univalence implies
non-dependent function extensionality, as presented by Gambino,
Kapulkin and Lumsdaine in
http://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf.

Then we give his proof that, without using univalence, non-dependent
function extensionality implies function extensionality. Thanks to
Mike Shulman (13th April 2018) for unraveling the Coq proof given at
https://github.com/vladimirias/Foundations/blob/master/Generalities/uu0.v
(search for "Deduction of functional extnsionality for dependent
functions (sections) from functional extensionality of usual
functions") to an informal proof, which we translated to Agda.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UAFE where

open import UF hiding (𝟘;𝟙)

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

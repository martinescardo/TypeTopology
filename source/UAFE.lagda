Martin Escardo, 9th April 2018

Voevodsky's original proof that univalence implies function
extensionality as presented by Gambino, Kapulkin and Lumsdaine in
http://www.math.uwo.ca/faculty/kapulkin/notes/ua_implies_fe.pdf.

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UAFE where

open import UF

Δ : ∀ {U} → U ̇ → U ̇
Δ X = Σ \(x : X) → Σ \(y : X) → x ≡ y

δ : ∀ {U} {X : U ̇} → X → Δ X
δ x = (x , x , refl)

π₁ : ∀ {U} {X : U ̇} → Δ X → X
π₁ (x , _ , _) = x

π₂ : ∀ {U} {X : U ̇} → Δ X → X
π₂ (_ , y , _) = y

δ-isEquiv : ∀ {U} {X : U ̇} → isEquiv (δ {U} {X})
δ-isEquiv {U} {X} = (π₁ , η) , (π₁ , ε)
 where
  η : (d : Δ X) → δ (π₁ d) ≡ d
  η (x , x , refl) = refl
  ε : (x : X) → π₁ (δ x) ≡ x
  ε x = refl

πδ : ∀ {U} (X : U ̇) → π₁ ∘ δ ≡ π₂ ∘ δ
πδ {U} X = refl {U} {X → X}

π₁-equals-π₂ : ∀ {U} → isUnivalent U → {X : U ̇} → π₁ ≡ π₂
π₁-equals-π₂ ua {X} = isEquiv-lc (λ(g : Δ X → X) → g ∘ δ) (preComp-isEquiv ua δ  δ-isEquiv) (πδ X)

fe : ∀ {U} → isUnivalent U → ∀ {V} {X : V ̇} {Y : U ̇} (f₁ f₂ : X → Y) → f₁ ∼ f₂ → f₁ ≡ f₂
fe {U} ua {V} {X} {Y} f₁ f₂ h = 
      f₁                              ≡⟨ refl ⟩
     (λ x → f₁ x)                    ≡⟨ refl ⟩ 
     (λ x → π₁ (f₁ x , f₂ x , h x))  ≡⟨ ap (λ π x → π (f₁ x , f₂ x , h x)) (π₁-equals-π₂ ua) ⟩
     (λ x → π₂ (f₁ x , f₂ x , h x))  ≡⟨ refl ⟩
     (λ x → f₂ x)                    ≡⟨ refl ⟩ 
      f₂                              ∎

\end{code}

\begin{code}

{-# OPTIONS --without-K --exact-split #-}

module UF-Retracts where

open import UF-Base

_isSectionOf_ : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → (Y → X) → U ̇
s isSectionOf r = r ∘ s ∼ id

has-section : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
has-section r = Σ \s → s isSectionOf r

has-retraction : ∀ {U V} {X : U ̇} {Y : V ̇} → (X → Y) → U ⊔ V ̇
has-retraction s = Σ \r → s isSectionOf r

retract_of_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
retract Y of X = Σ \(r : X → Y) → has-section r

identity-retraction : ∀ {U} {X : U ̇} → retract X of X
identity-retraction = id , (id , λ x → refl)

has-section-closed-under-∼ : ∀ {U V} {X : U ̇} {Y : V ̇} (f g : X → Y) → has-section f →  g ∼ f  → has-section g
has-section-closed-under-∼ {U} {V} {X} {Y} f g (s , fs) h = (s , λ y → g (s y) ≡⟨ h (s y) ⟩ f (s y) ≡⟨ fs y ⟩ y ∎)

has-section-closed-under-∼' : ∀ {U V} {X : U ̇} {Y : V ̇} {f g : X → Y} → has-section f → f ∼ g → has-section g
has-section-closed-under-∼' ise h = has-section-closed-under-∼ _ _ ise (λ x → (h x)⁻¹)

has-retraction-closed-under-∼ : ∀ {U V} {X : U ̇} {Y : V ̇} (f g : X → Y) → has-retraction f →  g ∼ f  → has-retraction g
has-retraction-closed-under-∼ {U} {V} {X} {Y} f g (r , rf) h = (r , λ x → r (g x) ≡⟨ ap r (h x) ⟩ r (f x) ≡⟨ rf x ⟩ x ∎)

has-retraction-closed-under-∼' : ∀ {U V} {X : U ̇} {Y : V ̇} {f g : X → Y} → has-retraction f → f ∼ g → has-retraction g
has-retraction-closed-under-∼' ise h = has-retraction-closed-under-∼ _ _ ise (λ x → (h x)⁻¹)

\end{code}

Surjection expressed in Curry-Howard logic amounts to retraction.

\begin{code}

retraction : ∀ {U V} {X : U ̇} {Y : V ̇} → (f : X → Y) → U ⊔ V ̇
retraction f = ∀ y → Σ \x → f x ≡ y

retract_Of_ : ∀ {U V} → U ̇ → V ̇ → U ⊔ V ̇
retract Y Of X = Σ \(f : X → Y) → retraction f

retract-of-retract-Of : ∀ {U V} {X : U ̇} {Y : V ̇} → retract Y of X → retract Y Of X
retract-of-retract-Of {U} {V} {X} {Y} (f , φ)= (f , hass)
 where
  hass : (y : Y) → Σ \(x : X) → f x ≡ y
  hass y = pr₁ φ y , pr₂ φ y

retract-Of-retract-of : ∀ {U V} {X : U ̇} {Y : V ̇} → retract Y Of X → retract Y of X
retract-Of-retract-of {U} {V} {X} {Y} (f , hass) = (f , φ)
 where
  φ : Σ \(s : Y → X) → f ∘ s ∼ id
  φ = (λ y → pr₁ (hass y)) , λ y → pr₂ (hass y)

retracts-compose : ∀ {U V W} {X : U ̇} {Y : V ̇} {Z : W ̇}
                 → retract Y of X → retract Z of Y → retract Z of X
retracts-compose (r , (s , rs)) (r' , (s' , rs')) = r' ∘ r ,
                                                    (s ∘ s' , λ z → ap r' (rs (s' z)) ∙ rs' z)

\end{code}

\begin{code}

Σ-retract : ∀ {U V W} {X : U ̇} {Y : V ̇} {A : X → W ̇} (g : Y → X)
          → has-section g → retract (Σ A) of (Σ \(y : Y) → A (g y))
Σ-retract {U} {V} {W} {X} {Y} {A} g (f , gf) = γ , φ , γφ
 where
  γ : (Σ \(y : Y) → A (g y)) → Σ A
  γ (y , a) = (g y , a)
  φ : Σ A → Σ \(y : Y) → A (g y)
  φ (x , a) = (f x , back-transport A (gf x) a) 
  γφ : (σ : Σ A) → γ (φ σ) ≡ σ
  γφ (x , a) = to-Σ-≡'' (gf x , p)
   where
    p : transport A (gf x) (back-transport A (gf x) a) ≡ a
    p = back-and-forth-transport (gf x)

\end{code}

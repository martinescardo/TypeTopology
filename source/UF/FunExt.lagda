Martin Escardo.

Formulation of function extensionality. Notice that this file doesn't
postulate function extensionality. It only defines the concept, which
is used explicitly as a hypothesis each time it is needed.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.FunExt where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.LeftCancellable

\end{code}

The appropriate notion of function extensionality in univalent
mathematics is funext, define below. It is implied, by an argument due
to Voevodky, by naive, non-dependent function extensionality, written
naive-funext here.

\begin{code}

naive-funext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
naive-funext 𝓤 𝓥 = {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f g : X → Y} → f ∼ g → f ＝ g

DN-funext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
DN-funext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {f g : Π A} → f ∼ g → f ＝ g

funext : ∀ 𝓤 𝓥 → 𝓤 ⁺ ⊔ 𝓥 ⁺ ̇
funext 𝓤 𝓥 = {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A) → is-equiv (happly' f g)

funext₀ : 𝓤₁ ̇
funext₀ = funext 𝓤₀ 𝓤₀

FunExt : 𝓤ω
FunExt = (𝓤 𝓥 : Universe) → funext 𝓤 𝓥

Fun-Ext : 𝓤ω
Fun-Ext = {𝓤 𝓥 : Universe} → funext 𝓤 𝓥

≃-funext : funext 𝓤 𝓥 → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (f g : Π A)
         → (f ＝ g) ≃ (f ∼ g)
≃-funext fe f g = happly' f g , fe f g

abstract
 dfunext : funext 𝓤 𝓥 → DN-funext 𝓤 𝓥
 dfunext fe {X} {A} {f} {g} = inverse (happly' f g) (fe f g)

 happly-funext : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                 (fe : funext 𝓤 𝓥) (f g : Π A) (h : f ∼ g)
              → happly (dfunext fe h) ＝ h
 happly-funext fe f g = inverses-are-sections happly (fe f g)

 funext-happly : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (fe : funext 𝓤 𝓥)
               → (f g : Π A) (h : f ＝ g)
               → dfunext fe (happly h) ＝ h
 funext-happly fe f g refl = inverses-are-retractions happly (fe f f) refl

happly-≃ : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } (fe : funext 𝓤 𝓥) {f g : (x : X) → A x} → (f ＝ g) ≃ f ∼ g
happly-≃ fe = happly , fe _ _

funext-lc : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
            (fe : funext 𝓤 𝓥)
            (f g : Π A)
          → left-cancellable (dfunext fe {X} {A} {f} {g})
funext-lc fe f g = section-lc (dfunext fe) (happly , happly-funext fe f g)

happly-lc : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
            (fe : funext 𝓤 𝓥)
            (f g : Π A)
          → left-cancellable (happly' f g)
happly-lc fe f g = section-lc happly (equivs-are-sections happly (fe f g))

inverse-happly-is-dfunext : {𝓤 𝓥 : Universe}
                            {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                            (fe₀ : funext 𝓤 𝓥)
                            (fe₁ : funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥))
                            (f g : A → B)
                          → inverse (happly' f g) (fe₀ f g) ＝ dfunext fe₀
inverse-happly-is-dfunext fe₀ fe₁ f g =
 dfunext fe₁ λ h →
 happly-lc fe₀ f g
  (happly' f g (inverse (happly' f g) (fe₀ f g) h)
     ＝⟨ inverses-are-sections _ (fe₀ f g) h ⟩
   h ＝⟨ happly-funext fe₀ f g h ⁻¹ ⟩
   happly' f g (dfunext fe₀ h) ∎)

dfunext-refl : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
               (fe : funext 𝓤 𝓥)
               (f : Π A)
             → dfunext fe (λ (x : X) → 𝓻𝓮𝒻𝓵 (f x)) ＝ refl
dfunext-refl fe f = happly-lc fe f f (happly-funext fe f f (λ x → refl))

ap-funext : {X : 𝓥 ̇ } {Y : 𝓦 ̇ }
            (f g : X → Y)
            {A : 𝓦' ̇ } (k : Y → A)
            (h : f ∼ g)
            (fe : funext 𝓥 𝓦) (x : X)
          → ap (λ (- : X → Y) → k (- x)) (dfunext fe h) ＝ ap k (h x)
ap-funext f g k h fe x = ap (λ - → k (- x)) (dfunext fe h)    ＝⟨ refl ⟩
                         ap (k ∘ (λ - → - x)) (dfunext fe h)  ＝⟨ I ⟩
                         ap k (ap (λ - → - x) (dfunext fe h)) ＝⟨ refl ⟩
                         ap k (happly (dfunext fe h) x)       ＝⟨ II ⟩
                         ap k (h x)                           ∎
                          where
                           I  = (ap-ap (λ - → - x) k (dfunext fe h))⁻¹
                           II = ap (λ - → ap k (- x)) (happly-funext fe f g h)

ap-precomp-funext : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {A : 𝓦 ̇ }
                    (f g : X → Y)
                    (k : A → X) (h : f ∼ g)
                    (fe₀ : funext 𝓤 𝓥)
                    (fe₁ : funext 𝓦 𝓥)
                  → ap (_∘ k) (dfunext fe₀ h) ＝ dfunext fe₁ (h ∘ k)
ap-precomp-funext f g k h fe₀ fe₁ =
  ap (_∘ k) (dfunext fe₀ h)                        ＝⟨ I ⟩
  dfunext fe₁ (happly (ap (_∘ k) (dfunext fe₀ h))) ＝⟨ II ⟩
  dfunext fe₁ (h ∘ k)                              ∎
   where
    I  = funext-happly fe₁ (f ∘ k) (g ∘ k) _ ⁻¹

    III = λ x →
     ap (λ - → - x) (ap (_∘ k) (dfunext fe₀ h)) ＝⟨ ap-ap _ _ (dfunext fe₀ h) ⟩
     ap (λ - → - (k x)) (dfunext fe₀ h)         ＝⟨ ap-funext f g id h fe₀ (k x) ⟩
     ap (λ v → v) (h (k x))                     ＝⟨ ap-id-is-id (h (k x)) ⟩
     h (k x)                                    ∎

    II = ap (dfunext fe₁) (dfunext fe₁ III)

\end{code}

The following is taken from this thread:
https://groups.google.com/forum/#!msg/homotopytypetheory/VaLJM7S4d18/Lezr_ZhJl6UJ

\begin{code}

transport-funext : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                   (P : (x : X) → A x → 𝓦 ̇ )
                   (fe : funext 𝓤 𝓥)
                   (f g : Π A)
                   (φ : (x : X) → P x (f x))
                   (h : f ∼ g)
                   (x : X)
                 → transport (λ - → (x : X) → P x (- x)) (dfunext fe h) φ x
                 ＝ transport (P x) (h x) (φ x)
transport-funext A P fe f g φ h x = q ∙ r
 where
  l : (f g : Π A) (φ : ∀ x → P x (f x)) (p : f ＝ g)
        → ∀ x → transport (λ - → ∀ x → P x (- x)) p φ x
              ＝ transport (P x) (happly p x) (φ x)
  l f .f φ refl x = refl

  q : transport (λ - → ∀ x → P x (- x)) (dfunext fe h) φ x
    ＝ transport (P x) (happly (dfunext fe h) x) (φ x)
  q = l f g φ (dfunext fe h) x

  r : transport (P x) (happly (dfunext fe h) x) (φ x)
    ＝ transport (P x) (h x) (φ x)
  r = ap (λ - → transport (P x) (- x) (φ x)) (happly-funext fe f g h)

transport-funext' : {X : 𝓤 ̇ } (A : 𝓥 ̇ )
                    (P : X → A → 𝓦 ̇ )
                    (fe : funext 𝓤 𝓥)
                    (f g : X → A)
                    (φ : (x : X) → P x (f x))
                    (h : f ∼ g)
                    (x : X)
                 → transport (λ - → (x : X) → P x (- x)) (dfunext fe h) φ x
                 ＝ transport (P x) (h x) (φ x)
transport-funext' A P = transport-funext (λ _ → A) P

\end{code}

Martin Escardo 2011.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module NotionsOfDecidability.Decidable where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import UF.Equiv
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.Logic

¬¬-elim : {A : 𝓤 ̇ } → is-decidable A → ¬¬ A → A
¬¬-elim (inl a) f = a
¬¬-elim (inr g) f = 𝟘-elim(f g)

map-decidable : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
              → (A → B)
              → (B → A)
              → is-decidable A
              → is-decidable B
map-decidable f g (inl x) = inl (f x)
map-decidable f g (inr h) = inr (λ y → h (g y))

map-decidable-↔ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                → (A ↔ B)
                → (is-decidable A ↔ is-decidable B)
map-decidable-↔ (f , g) = map-decidable f g ,
                          map-decidable g f

decidability-is-closed-under-≃ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                               → (A ≃ B)
                               → is-decidable A
                               → is-decidable B
decidability-is-closed-under-≃ (f , e) = map-decidable f (inverse f e)

map-decidable' : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
               → (A → ¬ B)
               → (¬ A → B)
               → is-decidable A
               → is-decidable B
map-decidable' f g (inl x) = inr (f x)
map-decidable' f g (inr h) = inl (g h)

empty-is-decidable : {X : 𝓤 ̇ } → is-empty X → is-decidable X
empty-is-decidable = inr

𝟘-is-decidable : is-decidable (𝟘 {𝓤})
𝟘-is-decidable = empty-is-decidable 𝟘-elim

pointed-is-decidable : {X : 𝓤 ̇ } → X → is-decidable X
pointed-is-decidable = inl

𝟙-is-decidable : is-decidable (𝟙 {𝓤})
𝟙-is-decidable = pointed-is-decidable ⋆

equivs-are-decidable : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (𝕗 : X ≃ Y)
                     → each-fiber-of ⌜ 𝕗 ⌝ is-decidable
equivs-are-decidable 𝕗 y = inl (⌜ 𝕗 ⌝⁻¹ y , inverses-are-sections' 𝕗 y)

id-is-decidable : {X : 𝓤 ̇ } → each-fiber-of (id {𝓤} {X}) is-decidable
id-is-decidable x = inl (x , refl)

decidable-closed-under-Σ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                         → is-prop X
                         → is-decidable X
                         → ((x : X) → is-decidable (Y x))
                         → is-decidable (Σ Y)
decidable-closed-under-Σ {𝓤} {𝓥} {X} {Y} isp d e = g d
 where
  g : is-decidable X → is-decidable (Σ Y)
  g (inl x) = h (e x)
   where
    φ : Σ Y → Y x
    φ (x' , y) = transport Y (isp x' x) y

    h : is-decidable(Y x) → is-decidable (Σ Y)
    h (inl y) = inl (x , y)
    h (inr v) = inr (contrapositive φ v)

  g (inr u) = inr (contrapositive pr₁ u)

×-preserves-decidability : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                         → is-decidable A
                         → is-decidable B
                         → is-decidable (A × B)
×-preserves-decidability (inl a) (inl b) = inl (a , b)
×-preserves-decidability (inl a) (inr v) = inr (λ c → v (pr₂ c))
×-preserves-decidability (inr u) _       = inr (λ c → u (pr₁ c))


+-preserves-decidability : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                         → is-decidable A
                         → is-decidable B
                         → is-decidable (A + B)
+-preserves-decidability (inl a) _       = inl (inl a)
+-preserves-decidability (inr u) (inl b) = inl (inr b)
+-preserves-decidability (inr u) (inr v) = inr (cases u v)

\end{code}

The following was added by Ayberk Tosun on 2024-05-28.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open Disjunction pt
 open PropositionalTruncation pt using (∣_∣; ∥∥-rec)

 ∨-preserves-decidability : (P : Ω 𝓤) (Q : Ω 𝓥)
                          → is-decidable (P holds)
                          → is-decidable (Q holds)
                          → is-decidable ((P ∨ Q) holds)
 ∨-preserves-decidability P Q φ ψ =
  cases case₁ case₂ (+-preserves-decidability φ ψ)
   where
    case₁ : P holds + Q holds → is-decidable ((P ∨ Q) holds)
    case₁ (inl p) = inl ∣ inl p ∣
    case₁ (inr q) = inl ∣ inr q ∣

    case₂ : ¬ (P holds + Q holds) → is-decidable ((P ∨ Q) holds)
    case₂ = inr ∘ ∥∥-rec 𝟘-is-prop

\end{code}

End of addition.

\begin{code}

→-preserves-decidability : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                         → is-decidable A
                         → is-decidable B
                         → is-decidable (A → B)
→-preserves-decidability d       (inl b) = inl (λ _ → b)
→-preserves-decidability (inl a) (inr v) = inr (λ f → v (f a))
→-preserves-decidability (inr u) (inr v) = inl (λ a → 𝟘-elim (u a))

→-preserves-decidability' : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                          → (¬ B →  is-decidable A)
                          → is-decidable B
                          → is-decidable (A → B)
→-preserves-decidability' φ (inl b) = inl (λ _ → b)
→-preserves-decidability' {𝓤} {𝓥} {A} {B} φ (inr v) = γ (φ v)
 where
  γ : is-decidable A → is-decidable (A → B)
  γ (inl a) = inr (λ f → v (f a))
  γ (inr u) = inl (λ a → 𝟘-elim (u a))

→-preserves-decidability'' : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                           → is-decidable A
                           → (A → is-decidable B)
                           → is-decidable (A → B)
→-preserves-decidability'' {𝓤} {𝓥} {A} {B} (inl a) φ = γ (φ a)
 where
  γ : is-decidable B → is-decidable (A → B)
  γ (inl b) = inl (λ _ → b)
  γ (inr v) = inr (λ f → v (f a))

→-preserves-decidability'' (inr u) φ = inl (λ a → 𝟘-elim (u a))

¬-preserves-decidability : {A : 𝓤 ̇ }
                         → is-decidable A
                         → is-decidable(¬ A)
¬-preserves-decidability d = →-preserves-decidability d 𝟘-is-decidable

which-of : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
         → A + B
         → Σ b ꞉ 𝟚 , (b ＝ ₀ → A)
                   × (b ＝ ₁ → B)
which-of (inl a) = ₀ ,
                   (λ (r : ₀ ＝ ₀) → a) ,
                   (λ (p : ₀ ＝ ₁) → 𝟘-elim (zero-is-not-one p))
which-of (inr b) = ₁ ,
                   (λ (p : ₁ ＝ ₀) → 𝟘-elim (zero-is-not-one (p ⁻¹))) ,
                   (λ (r : ₁ ＝ ₁) → b)

\end{code}

The following is a special case we are interested in:

\begin{code}

boolean-value : {A : 𝓤 ̇ }
              → is-decidable A
              → Σ b ꞉ 𝟚 , (b ＝ ₀ →   A)
                        × (b ＝ ₁ → ¬ A)
boolean-value = which-of

module _ {X : 𝓤 ̇ } {A₀ : X → 𝓥 ̇ } {A₁ : X → 𝓦 ̇ }
         (h : (x : X) → A₀ x + A₁ x)
       where

 indicator : Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ → A₀ x)
                                      × (p x ＝ ₁ → A₁ x))
 indicator = (λ x → pr₁(lemma₁ x)) , (λ x → pr₂(lemma₁ x))
  where
   lemma₀ : (x : X) → (A₀ x + A₁ x) → Σ b ꞉ 𝟚 , (b ＝ ₀ → A₀ x)
                                              × (b ＝ ₁ → A₁ x)
   lemma₀ x = which-of

   lemma₁ : (x : X) → Σ b ꞉ 𝟚 , (b ＝ ₀ → A₀ x) × (b ＝ ₁ → A₁ x)
   lemma₁ x = lemma₀ x (h x)

 indicator-map : X → 𝟚
 indicator-map = pr₁ indicator

 indicator-property : (x : X) → (indicator-map x ＝ ₀ → A₀ x)
                              × (indicator-map x ＝ ₁ → A₁ x)
 indicator-property = pr₂ indicator

 indicator-property₀ : (x : X) → indicator-map x ＝ ₀ → A₀ x
 indicator-property₀ x = pr₁ (indicator-property x)

 indicator-property₁ : (x : X) → indicator-map x ＝ ₁ → A₁ x
 indicator-property₁ x = pr₂ (indicator-property x)

module _ {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
         (δ : (x : X) → A x + ¬ A x)
       where

 private
  f : (x : X) → is-decidable (A x) → 𝟚
  f x (inl a) = ₀
  f x (inr ν) = ₁

  f₀ : (x : X) (d : is-decidable (A x)) → f x d ＝ ₀ → A x
  f₀ x (inl a) e = a
  f₀ x (inr ν) e = 𝟘-elim (one-is-not-zero e)

  f₁ : (x : X) (d : is-decidable (A x)) → f x d ＝ ₁ → ¬ A x
  f₁ x (inl a) e = 𝟘-elim (zero-is-not-one e)
  f₁ x (inr ν) e = ν

  f₀-back : (x : X) (d : is-decidable (A x)) → A x → f x d ＝ ₀
  f₀-back x (inl a) a' = refl
  f₀-back x (inr ν) a' = 𝟘-elim (ν a')

  f₁-back : (x : X) (d : is-decidable (A x)) → ¬ A x → f x d ＝ ₁
  f₁-back x (inl a) ν' = 𝟘-elim (ν' a)
  f₁-back x (inr ν) ν' = refl

  χ : X → 𝟚
  χ x = f x (δ x)

 characteristic-map : X → 𝟚
 characteristic-map = χ

 characteristic-map-property₀ : (x : X) → χ x ＝ ₀ → A x
 characteristic-map-property₀ x = f₀ x (δ x)

 characteristic-map-property₁ : (x : X) → χ x ＝ ₁ → ¬ A x
 characteristic-map-property₁ x = f₁ x (δ x)

 characteristic-map-property₀-back : (x : X) → A x → χ x ＝ ₀
 characteristic-map-property₀-back x = f₀-back x (δ x)

 characteristic-map-property₁-back : (x : X) → ¬ A x → χ x ＝ ₁
 characteristic-map-property₁-back x = f₁-back x (δ x)

\end{code}

Added by Tom de Jong, November 2021.

\begin{code}

decidable-↔ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → X ↔ Y
            → is-decidable X
            → is-decidable Y
decidable-↔ {𝓤} {𝓥} {X} {Y} (f , g) (inl  x) = inl (f x)
decidable-↔ {𝓤} {𝓥} {X} {Y} (f , g) (inr nx) = inr (nx ∘ g)

decidable-cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → X ≃ Y
               → is-decidable X
               → is-decidable Y
decidable-cong e = decidable-↔ (⌜ e ⌝ , ⌜ e ⌝⁻¹)

\end{code}

Added by Tom de Jong in January 2022.

\begin{code}

all-types-are-¬¬-decidable : (X : 𝓤 ̇ ) → ¬¬ (is-decidable X)
all-types-are-¬¬-decidable X h = claim₂ claim₁
 where
  claim₁ : ¬ X
  claim₁ x = h (inl x)
  claim₂ : ¬¬ X
  claim₂ nx = h (inr nx)

¬¬-stable-if-decidable : (X : 𝓤 ̇ ) → is-decidable X → ¬¬-stable X
¬¬-stable-if-decidable X = ¬¬-elim

\end{code}

Added 21th August 2024 by Alice Laroche.

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 decidable-inhabited-types-are-pointed : {X : 𝓤 ̇ } → ∥ X ∥ → is-decidable X → X
 decidable-inhabited-types-are-pointed ∣x∣ (inl x)  = x
 decidable-inhabited-types-are-pointed ∣x∣ (inr ¬x) =
  𝟘-elim (∥∥-rec 𝟘-is-prop ¬x ∣x∣)

\end{code}

End of addition.

Added by Martin Escardo 17th September 2024. The propositional
truncation of a decidable type can be constructed with no assumptions
and it has split support.

\begin{code}

∥_∥⟨_⟩ : (X : 𝓤 ̇ ) → is-decidable X → 𝓤₀ ̇
∥ X ∥⟨ inl x ⟩ = 𝟙
∥ X ∥⟨ inr ν ⟩ = 𝟘

∥∥⟨_⟩-is-prop : {X : 𝓤 ̇ } (δ : is-decidable X) → is-prop ∥ X ∥⟨ δ ⟩
∥∥⟨ inl x ⟩-is-prop = 𝟙-is-prop
∥∥⟨ inr ν ⟩-is-prop = 𝟘-is-prop

∥∥⟨_⟩-is-decidable : {X : 𝓤 ̇ } (δ : is-decidable X) → is-decidable ∥ X ∥⟨ δ ⟩
∥∥⟨ inl x ⟩-is-decidable = 𝟙-is-decidable
∥∥⟨ inr ν ⟩-is-decidable = 𝟘-is-decidable

∣_∣⟨_⟩ : {X : 𝓤 ̇ } → X → (δ : is-decidable X) → ∥ X ∥⟨ δ ⟩
∣ x ∣⟨ inl _ ⟩ = ⋆
∣ x ∣⟨ inr ν ⟩ = ν x

\end{code}

Notice that the induction principle doesn't require the family A to be
prop-valued.

\begin{code}

∥∥⟨_⟩-induction : {X : 𝓤 ̇ } (δ : is-decidable X)
                 (A : ∥ X ∥⟨ δ ⟩ → 𝓥 ̇ )
               → ((x : X) → A ∣ x ∣⟨ δ ⟩)
               → (s : ∥ X ∥⟨ δ ⟩) → A s
∥∥⟨ inl x ⟩-induction A f ⋆ = f x
∥∥⟨ inr ν ⟩-induction A f s = 𝟘-elim s

\end{code}

But the induction equation does.

\begin{code}

∥∥⟨_⟩-induction-equation : {X : 𝓤 ̇ }
                          (δ : is-decidable X)
                          (A : ∥ X ∥⟨ δ ⟩ → 𝓥 ̇ )
                        → ((s : ∥ X ∥⟨ δ ⟩) → is-prop (A s))
                        → (f : (x : X) → A ∣ x ∣⟨ δ ⟩)
                          (x : X)
                        → ∥∥⟨ δ ⟩-induction A f ∣ x ∣⟨ δ ⟩ ＝ f x
∥∥⟨ inl x ⟩-induction-equation A A-is-prop f x' = A-is-prop ⋆ (f x) (f x')
∥∥⟨ inr ν ⟩-induction-equation A A-is-prop f x  = 𝟘-elim (ν x)

∥∥⟨_⟩-rec : {X : 𝓤 ̇ } (δ : is-decidable X) {A : 𝓥 ̇ }
          → (X → A) → ∥ X ∥⟨ δ ⟩ → A
∥∥⟨ δ ⟩-rec {A} = ∥∥⟨ δ ⟩-induction (λ _ → A)

∣∣⟨_⟩-exit : {X : 𝓤 ̇ } (δ : is-decidable X) → ∥ X ∥⟨ δ ⟩ → X
∣∣⟨ δ ⟩-exit = ∥∥⟨ δ ⟩-rec id

∣∣⟨_⟩-exit-is-section : {X : 𝓤 ̇ } (δ : is-decidable X) (s : ∥ X ∥⟨ δ ⟩)
                     → ∣ ∣∣⟨ δ ⟩-exit s ∣⟨ δ ⟩ ＝ s
∣∣⟨ inl x ⟩-exit-is-section ⋆ = refl
∣∣⟨ inr ν ⟩-exit-is-section s = 𝟘-elim s

module propositional-truncation-of-decidable-type
        (pt : propositional-truncations-exist)
       where

 open propositional-truncations-exist pt public

 module _ {X : 𝓤 ̇ } (δ : is-decidable X) where

  ∥∥⟨_⟩-to-∥∥ : ∥ X ∥⟨ δ ⟩ → ∥ X ∥
  ∥∥⟨_⟩-to-∥∥ = ∥∥⟨ δ ⟩-rec ∣_∣

  ∥∥-to-∥∥⟨_⟩ : ∥ X ∥ → ∥ X ∥⟨ δ ⟩
  ∥∥-to-∥∥⟨_⟩ = ∥∥-rec (∥∥⟨ δ ⟩-is-prop) ∣_∣⟨ δ ⟩

  decidable-types-have-split-support : ∥ X ∥ → X
  decidable-types-have-split-support s = ∣∣⟨ δ ⟩-exit (∥∥-to-∥∥⟨_⟩ s)

\end{code}

Added by Fredrik Bakke 22nd August 2025. Negations of decidable types are
decidable.

\begin{code}

decidable-types-are-closed-under-negations : {X : 𝓤 ̇ }
                                           → is-decidable X
                                           → is-decidable (¬ X)
decidable-types-are-closed-under-negations (inl x) = inr (λ nx → nx x)
decidable-types-are-closed-under-negations (inr nx) = inl nx

\end{code}

Martin Escardo 2011.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module NotionsOfDecidability.Decidable where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import UF.Equiv
open import UF.Subsingletons

¬¬-elim : {A : 𝓤 ̇ } → is-decidable A → ¬¬ A → A
¬¬-elim (inl a) f = a
¬¬-elim (inr g) f = 𝟘-elim(f g)

map-is-decidable : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (B → A) → is-decidable A → is-decidable B
map-is-decidable f g (inl x) = inl (f x)
map-is-decidable f g (inr h) = inr (λ y → h (g y))

map-is-decidable-↔ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A ↔ B) → (is-decidable A ↔ is-decidable B)
map-is-decidable-↔ (f , g) = map-is-decidable f g , map-is-decidable g f

decidability-is-closed-under-≃ : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                               → (A ≃ B)
                               → is-decidable A
                               → is-decidable B
decidability-is-closed-under-≃ (f , e) = map-is-decidable f (inverse f e)

map-is-decidable' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → ¬ B) → (¬ A → B) → is-decidable A → is-decidable B
map-is-decidable' f g (inl x) = inr (f x)
map-is-decidable' f g (inr h) = inl (g h)

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
which-of (inl a) = ₀ , (λ (r : ₀ ＝ ₀) → a) , λ (p : ₀ ＝ ₁) → 𝟘-elim (zero-is-not-one p)
which-of (inr b) = ₁ , (λ (p : ₁ ＝ ₀) → 𝟘-elim (zero-is-not-one (p ⁻¹))) , (λ (r : ₁ ＝ ₁) → b)

\end{code}

The following is a special case we are interested in:

\begin{code}

boolean-value : {A : 𝓤 ̇ }
              → is-decidable A
              → Σ b ꞉ 𝟚 , (b ＝ ₀ →   A)
                        × (b ＝ ₁ → ¬ A)
boolean-value = which-of

\end{code}

Notice that this b is unique (Agda exercise) and that the converse
also holds. In classical mathematics it is posited that all
propositions have binary truth values, irrespective of whether they
have BHK-style witnesses. And this is precisely the role of the
principle of excluded middle in classical mathematics.  The following
requires choice, which holds in BHK-style constructive mathematics:
s
\begin{code}

indicator : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
          → ((x : X) → A x + B x)
          → Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ → A x)
                                     × (p x ＝ ₁ → B x))
indicator {𝓤} {𝓥} {𝓦} {X} {A} {B} h = (λ x → pr₁(lemma₁ x)) , (λ x → pr₂(lemma₁ x))
 where
  lemma₀ : (x : X) → (A x + B x) → Σ b ꞉ 𝟚 , (b ＝ ₀ → A x) × (b ＝ ₁ → B x)
  lemma₀ x = which-of

  lemma₁ : (x : X) → Σ b ꞉ 𝟚 , (b ＝ ₀ → A x) × (b ＝ ₁ → B x)
  lemma₁ = λ x → lemma₀ x (h x)

\end{code}

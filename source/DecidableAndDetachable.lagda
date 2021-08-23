Martin Escardo 2011.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module DecidableAndDetachable where

open import SpartanMLTT

open import Plus-Properties
open import Two-Properties
open import UF-Subsingletons
open import UF-PropTrunc

\end{code}

We look at decidable propositions and subsets (using the terminogy
"detachable" for the latter").

\begin{code}

¬¬-elim : {A : 𝓤 ̇ } → decidable A → ¬¬ A → A
¬¬-elim (inl a) f = a
¬¬-elim (inr g) f = 𝟘-elim(f g)

empty-decidable : {X : 𝓤 ̇ } → is-empty X → decidable X
empty-decidable = inr

𝟘-decidable : decidable (𝟘 {𝓤})
𝟘-decidable = empty-decidable 𝟘-elim

pointed-decidable : {X : 𝓤 ̇ } → X → decidable X
pointed-decidable = inl

\end{code}

Digression: https://twitter.com/EgbertRijke/status/1429443868450295810

"decidable" is almost a monad, except that it is not even functorial:

\begin{code}

module EgbertRijkeTwitterDiscussion-22-August-2021-not-a-monad where

  T : 𝓤 ̇ → 𝓤 ̇
  T = decidable

  η : (X : 𝓤 ̇ ) → X → T X
  η X = pointed-decidable

  μ : (X : 𝓤 ̇ ) → T (T X) → T X
  μ X (inl δ) = δ
  μ X (inr u) = inr (λ x → u (inl x))

\end{code}

Answer to Andrej Bauer's trick question:

\begin{code}

  open import UF-Equiv

  raw-T-algebras-are-non-empty : {X : 𝓤 ̇ } (α : T X → X) → is-nonempty X
  raw-T-algebras-are-non-empty α u = u (α (inr u))

  retraction-of-η-is-section : {A : 𝓤 ̇ } (α : T A → A)
                             → α ∘ η A ∼ id
                             → η A ∘ α ∼ id
  retraction-of-η-is-section α h (inl a) = ap inl (h a)
  retraction-of-η-is-section α h (inr u) = 𝟘-elim (raw-T-algebras-are-non-empty α u)

  section-of-η-is-retraction : {A : 𝓤 ̇ } (α : T A → A)
                             → η A ∘ α ∼ id
                             → α ∘ η A ∼ id
  section-of-η-is-retraction α k a = inl-lc (k (inl a))

  is-proto-structure-map : {A : 𝓤 ̇ } (α : T A → A) → 𝓤 ̇
  is-proto-structure-map {𝓤} {A} α = α ∘ η A ∼ id

  proto-structure-maps-have-nonempty-carrier : {A : 𝓤 ̇ } (α : T A → A)
                                             → is-proto-structure-map α
                                             → is-nonempty A
  proto-structure-maps-have-nonempty-carrier α _ = raw-T-algebras-are-non-empty α

  proto-structure-maps-are-invertible : {A : 𝓤 ̇ } (α : T A → A)
                                      → is-proto-structure-map α
                                      → invertible α
  proto-structure-maps-are-invertible {𝓤} {A} α h = η A , retraction-of-η-is-section α h , h

  canonical-psm : {A : 𝓤 ̇ } → is-nonempty A → (T A → A)
  canonical-psm ϕ (inl a) = a
  canonical-psm ϕ (inr u) = 𝟘-elim (ϕ u)

  psm-is-proto-structure-map : {A : 𝓤 ̇ } (ϕ : is-nonempty A) → is-proto-structure-map (canonical-psm ϕ)
  psm-is-proto-structure-map ϕ a = refl

  proto-structure-map-uniqueness : {A : 𝓤 ̇ } (α : T A → A)
                                 → is-proto-structure-map α
                                 → (ϕ : is-nonempty A) → α ∼ canonical-psm ϕ
  proto-structure-map-uniqueness α h ϕ (inl a) = h a
  proto-structure-map-uniqueness α h ϕ (inr u) = 𝟘-elim (ϕ u)

  is-proto-algebra : 𝓤 ̇ → 𝓤 ̇
  is-proto-algebra A = Σ α ꞉ (T A → A) , is-proto-structure-map α

  proto-algebras-are-non-empty : {A : 𝓤 ̇ } → is-proto-algebra A → is-nonempty A
  proto-algebras-are-non-empty (α , _) = raw-T-algebras-are-non-empty α

  nonempty-types-are-proto-algebras : {A : 𝓤 ̇ } → is-nonempty A → is-proto-algebra A
  nonempty-types-are-proto-algebras ϕ = canonical-psm ϕ , psm-is-proto-structure-map ϕ

  ηcpsm : {A : 𝓤 ̇ } (ϕ : is-nonempty A) → η A ∘ canonical-psm ϕ ∼ id
  ηcpsm ϕ (inl a) = refl
  ηcpsm ϕ (inr u) = 𝟘-elim (ϕ u)

  η-invertible-gives-non-empty : {X : 𝓤 ̇ } → invertible (η X) → is-nonempty X
  η-invertible-gives-non-empty (α , _ , _) = raw-T-algebras-are-non-empty α

  non-empty-gives-η-invertible : {X : 𝓤 ̇ } → is-nonempty X → invertible (η X)
  non-empty-gives-η-invertible {𝓤} {X} ϕ = canonical-psm ϕ , psm-is-proto-structure-map ϕ , ηcpsm ϕ

\end{code}

End of digression.

\begin{code}

𝟙-decidable : decidable (𝟙 {𝓤})
𝟙-decidable = pointed-decidable *

×-preserves-decidability : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                         → decidable A
                         → decidable B
                         → decidable (A × B)
×-preserves-decidability (inl a) (inl b) = inl (a , b)
×-preserves-decidability (inl a) (inr v) = inr (λ c → v (pr₂ c))
×-preserves-decidability (inr u) _       = inr (λ c → u (pr₁ c))


+-preserves-decidability : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                         → decidable A
                         → decidable B
                         → decidable (A + B)
+-preserves-decidability (inl a) _       = inl (inl a)
+-preserves-decidability (inr u) (inl b) = inl (inr b)
+-preserves-decidability (inr u) (inr v) = inr (cases u v)

→-preserves-decidability : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                         → decidable A
                         → decidable B
                         → decidable (A → B)
→-preserves-decidability d       (inl b) = inl (λ _ → b)
→-preserves-decidability (inl a) (inr v) = inr (λ f → v (f a))
→-preserves-decidability (inr u) (inr v) = inl (λ a → 𝟘-elim (u a))

→-preserves-decidability' : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                          → (¬ B →  decidable A)
                          → decidable B
                          → decidable (A → B)
→-preserves-decidability' φ (inl b) = inl (λ _ → b)
→-preserves-decidability' {𝓤} {𝓥} {A} {B} φ (inr v) = γ (φ v)
 where
  γ : decidable A → decidable (A → B)
  γ (inl a) = inr (λ f → v (f a))
  γ (inr u) = inl (λ a → 𝟘-elim (u a))

→-preserves-decidability'' : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
                           → decidable A
                           → (A → decidable B)
                           → decidable (A → B)
→-preserves-decidability'' {𝓤} {𝓥} {A} {B} (inl a) φ = γ (φ a)
 where
  γ : decidable B → decidable (A → B)
  γ (inl b) = inl (λ _ → b)
  γ (inr v) = inr (λ f → v (f a))

→-preserves-decidability'' (inr u) φ = inl (λ a → 𝟘-elim (u a))

¬-preserves-decidability : {A : 𝓤 ̇ }
                         → decidable A
                         → decidable(¬ A)
¬-preserves-decidability d = →-preserves-decidability d 𝟘-decidable

which-of : {A : 𝓤 ̇ } {B : 𝓥 ̇ }
         → A + B
         → Σ b ꞉ 𝟚 , (b ≡ ₀ → A)
                   × (b ≡ ₁ → B)
which-of (inl a) = ₀ , (λ (r : ₀ ≡ ₀) → a) , λ (p : ₀ ≡ ₁) → 𝟘-elim (zero-is-not-one p)
which-of (inr b) = ₁ , (λ (p : ₁ ≡ ₀) → 𝟘-elim (zero-is-not-one (p ⁻¹))) , (λ (r : ₁ ≡ ₁) → b)

\end{code}

The following is a special case we are interested in:

\begin{code}

boolean-value : {A : 𝓤 ̇ }
            → decidable A
            → Σ b ꞉ 𝟚 , (b ≡ ₀ →   A)
                      × (b ≡ ₁ → ¬ A)
boolean-value = which-of

\end{code}

Notice that this b is unique (Agda exercise) and that the converse
also holds. In classical mathematics it is posited that all
propositions have binary truth values, irrespective of whether they
have BHK-style witnesses. And this is precisely the role of the
principle of excluded middle in classical mathematics.  The following
requires choice, which holds in BHK-style constructive mathematics:

\begin{code}

indicator : {X : 𝓤 ̇ } → {A B : X → 𝓥 ̇ }
          → ((x : X) → A x + B x)
          → Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ≡ ₀ → A x)
                                     × (p x ≡ ₁ → B x))
indicator {𝓤} {𝓥} {X} {A} {B} h = (λ x → pr₁(lemma₁ x)) , (λ x → pr₂(lemma₁ x))
 where
  lemma₀ : (x : X) → (A x + B x) → Σ b ꞉ 𝟚 , (b ≡ ₀ → A x) × (b ≡ ₁ → B x)
  lemma₀ x = which-of

  lemma₁ : (x : X) → Σ b ꞉ 𝟚 , (b ≡ ₀ → A x) × (b ≡ ₁ → B x)
  lemma₁ = λ x → lemma₀ x (h x)

\end{code}

We again have a particular case of interest.  Detachable subsets,
defined below, are often known as decidable subsets. Agda doesn't
allow overloading of terminology, and hence we gladly accept the
slighly non-universal terminology.

\begin{code}

detachable : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
detachable A = ∀ x → decidable(A x)

characteristic-function : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                        → detachable A
                        → Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ≡ ₀ →   A x)
                                                   × (p x ≡ ₁ → ¬ (A x)))
characteristic-function = indicator

co-characteristic-function : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                           → detachable A
                           → Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ≡ ₀ → ¬ (A x))
                                                      × (p x ≡ ₁ →   A x))
co-characteristic-function d = indicator(λ x → +-commutative(d x))

decidable-closed-under-Σ : {X : 𝓤 ̇ } {Y : X → 𝓥 ̇ }
                         → is-prop X
                         → decidable X
                         → ((x : X) → decidable (Y x))
                         → decidable (Σ Y)
decidable-closed-under-Σ {𝓤} {𝓥} {X} {Y} isp d e = g d
 where
  g : decidable X → decidable (Σ Y)
  g (inl x) = h (e x)
   where
    φ : Σ Y → Y x
    φ (x' , y) = transport Y (isp x' x) y

    h : decidable(Y x) → decidable (Σ Y)
    h (inl y) = inl (x , y)
    h (inr v) = inr (contrapositive φ v)

  g (inr u) = inr (contrapositive pr₁ u)

\end{code}

Notice that p is unique (Agda exercise - you will need function
extensionality).

Don't really have a good place to put this:

\begin{code}

module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 not-exists₀-implies-forall₁ : {X : 𝓤 ̇ } (p : X → 𝟚)
                            → ¬ (∃ x ꞉ X , p x ≡ ₀)
                            → ∀ (x : X) → p x ≡ ₁
 not-exists₀-implies-forall₁ p u x = different-from-₀-equal-₁ (not-Σ-implies-Π-not (u ∘ ∣_∣) x)

 forall₁-implies-not-exists₀ : {X : 𝓤 ̇ } (p : X → 𝟚)
                            → (∀ (x : X) → p x ≡ ₁)
                            → ¬ (∃ x ꞉ X , p x ≡ ₀)
 forall₁-implies-not-exists₀ {𝓤} {X} p α = ∥∥-rec 𝟘-is-prop h
  where
   h : (Σ x ꞉ X , p x ≡ ₀) → 𝟘
   h (x , r) = zero-is-not-one (r ⁻¹ ∙ α x)

\end{code}

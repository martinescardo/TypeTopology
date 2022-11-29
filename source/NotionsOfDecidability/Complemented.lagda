Martin Escardo 2011. With additions by Tom de Jong 2021.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module NotionsOfDecidability.Complemented where

open import MLTT.Spartan

open import MLTT.Plus-Properties
open import MLTT.Two-Properties
open import UF.Subsingletons
open import UF.PropTrunc
open import NotionsOfDecidability.Decidable

\end{code}

We again have a particular case of interest.  Complemented subsets,
defined below, are often known as decidable subsets. Agda doesn't
allow overloading of terminology, and hence we gladly accept the
slighly non-universal terminology.

\begin{code}

complemented : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ ) → 𝓤 ⊔ 𝓥 ̇
complemented A = ∀ x → decidable(A x)

characteristic-function : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                        → complemented A
                        → Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ →   A x)
                                                   × (p x ＝ ₁ → ¬ (A x)))
characteristic-function = indicator

co-characteristic-function : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
                           → complemented A
                           → Σ p ꞉ (X → 𝟚) , ((x : X) → (p x ＝ ₀ → ¬ (A x))
                                                      × (p x ＝ ₁ →   A x))
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
                            → ¬ (∃ x ꞉ X , p x ＝ ₀)
                            → ∀ (x : X) → p x ＝ ₁
 not-exists₀-implies-forall₁ p u x = different-from-₀-equal-₁ (not-Σ-implies-Π-not (u ∘ ∣_∣) x)

 forall₁-implies-not-exists₀ : {X : 𝓤 ̇ } (p : X → 𝟚)
                            → (∀ (x : X) → p x ＝ ₁)
                            → ¬ (∃ x ꞉ X , p x ＝ ₀)
 forall₁-implies-not-exists₀ {𝓤} {X} p α = ∥∥-rec 𝟘-is-prop h
  where
   h : (Σ x ꞉ X , p x ＝ ₀) → 𝟘
   h (x , r) = zero-is-not-one (r ⁻¹ ∙ α x)

 forall₀-implies-not-exists₁ : {X : 𝓤 ̇ } (p : X → 𝟚)
                            → (∀ (x : X) → p x ＝ ₀)
                            → ¬ (∃ x ꞉ X , p x ＝ ₁)
 forall₀-implies-not-exists₁ {𝓤} {X} p α = ∥∥-rec 𝟘-is-prop h
  where
   h : (Σ x ꞉ X , p x ＝ ₁) → 𝟘
   h (x , r) = one-is-not-zero (r ⁻¹ ∙ α x)

\end{code}

Tom de Jong, 1 November 2021.

We show that 𝟚 classifies decidable subsets.

We start by defining the type Ωᵈ 𝓤 of decidable propositions in a type
universe 𝓤 and we show that 𝟚 ≃ Ωᵈ 𝓤 (for any universe 𝓤).

\begin{code}

boolean-value' : {A : 𝓤 ̇ }
               → decidable A
               → Σ b ꞉ 𝟚 , (b ＝ ₀ ⇔ ¬ A)
                         × (b ＝ ₁ ⇔   A)
boolean-value' {𝓤} {A} (inl a ) = (₁ , ϕ , ψ)
 where
  ϕ : ₁ ＝ ₀ ⇔ ¬ A
  ϕ = (λ p → 𝟘-elim (one-is-not-zero p))
    , (λ na → 𝟘-elim (na a))
  ψ : ₁ ＝ ₁ ⇔ A
  ψ = (λ _ → a) , (λ _ → refl)
boolean-value' {𝓤} {A} (inr na) = ₀ , ϕ , ψ
 where
  ϕ : ₀ ＝ ₀ ⇔ ¬ A
  ϕ = (λ _ → na) , (λ _ → refl)
  ψ : ₀ ＝ ₁ ⇔ A
  ψ = (λ p → 𝟘-elim (zero-is-not-one p))
    , (λ a → 𝟘-elim (na a))

private
 Ωᵈ : (𝓤 : Universe) → 𝓤 ⁺ ̇
 Ωᵈ 𝓤 = Σ P ꞉ Ω 𝓤 , decidable (P holds)

 ⟨_⟩ : Ωᵈ 𝓤 → 𝓤 ̇
 ⟨ (P , i) , δ ⟩ = P

open import UF.Equiv
open import UF.Subsingletons-FunExt
open import UF.FunExt
open import UF.Lower-FunExt

module _
        {𝓤 : Universe}
        (fe : funext 𝓤 𝓤)
        (pe : propext 𝓤)
       where

 to-Ωᵈ-equality : (P Q : Ωᵈ 𝓤)
                → (⟨ P ⟩ → ⟨ Q ⟩)
                → (⟨ Q ⟩ → ⟨ P ⟩)
                → P ＝ Q
 to-Ωᵈ-equality ((P , i) , δ) ((Q , j) , ε) α β =
  to-subtype-＝ σ (to-subtype-＝ τ (pe i j α β))
  where
   σ : (P : Ω 𝓤) → is-prop (decidable (P holds))
   σ P = decidability-of-prop-is-prop (lower-funext 𝓤 𝓤 fe) (holds-is-prop P)
   τ : (X : 𝓤 ̇) → is-prop (is-prop X)
   τ _ = being-prop-is-prop fe

 𝟚-is-the-type-of-decidable-propositions : 𝟚 ≃ Ωᵈ 𝓤
 𝟚-is-the-type-of-decidable-propositions = qinveq f (g , η , ε)
  where
   f : 𝟚 → Ωᵈ 𝓤
   f ₀ = ((𝟘 , 𝟘-is-prop) , inr 𝟘-elim)
   f ₁ = ((𝟙 , 𝟙-is-prop) , inl ⋆)
   g : Ωᵈ 𝓤 → 𝟚
   g (P , δ) = pr₁ (boolean-value' δ)
   η : g ∘ f ∼ id
   η ₀ = refl
   η ₁ = refl
   ε : f ∘ g ∼ id
   ε P = 𝟚-equality-cases ε₀ ε₁
    where
     lemma : (g P ＝ ₀ ⇔ ¬ ⟨ P ⟩)
           × (g P ＝ ₁ ⇔   ⟨ P ⟩)
     lemma = pr₂ (boolean-value' (pr₂ P))
     ε₀ : g P ＝ ₀
        → (f ∘ g) P ＝ P
     ε₀ e = to-Ωᵈ-equality (f (g P)) P
             (λ (q : ⟨ f (g P) ⟩) → 𝟘-elim (transport (λ b → ⟨ f b ⟩) e q))
             (λ (p : ⟨ P ⟩) → 𝟘-elim (lr-implication (pr₁ lemma) e p))
     ε₁ : g P ＝ ₁
        → (f ∘ g) P ＝ P
     ε₁ e = to-Ωᵈ-equality (f (g P)) P
             (λ _ → lr-implication (pr₂ lemma) e)
             (λ _ → transport⁻¹ (λ (b : 𝟚) → ⟨ f b ⟩) e ⋆)

\end{code}

The promised result now follows promptly using two general lemmas on
equivalences.

(Note that one direction of the equivalence ΠΣ-distr-≃ is sometimes known as
"type-theoretic axiom of choice".)

\begin{code}

open import UF.Powerset
open import UF.EquivalenceExamples

is-complemented-subset : {X : 𝓤 ̇  } → (X → Ω 𝓣) → 𝓤 ⊔ 𝓣 ̇
is-complemented-subset {𝓤} {𝓣} {X} A = (x : X) → decidable (x ∈ A)

module _
        (fe  : funext 𝓤 (𝓣 ⁺))
        (fe' : funext 𝓣 𝓣)
        (pe : propext 𝓣)
       where

 𝟚-classifies-decidable-subsets : {X : 𝓤 ̇  }
                                → (X → 𝟚)
                                ≃ (Σ A ꞉ (X → Ω 𝓣) , is-complemented-subset A)
 𝟚-classifies-decidable-subsets {X} =
  (X → 𝟚)                                      ≃⟨ γ          ⟩
  (X → Ωᵈ 𝓣)                                   ≃⟨ ΠΣ-distr-≃ ⟩
  (Σ A ꞉ (X → Ω 𝓣) , is-complemented-subset A) ■
   where
    γ = →cong' fe (lower-funext 𝓤 (𝓣 ⁺) fe)
         (𝟚-is-the-type-of-decidable-propositions fe' pe)

 𝟚-classifies-decidable-subsets-values :
   {X : 𝓤 ̇  }
   (A : X → Ω 𝓣)
   (δ : is-complemented-subset A)
   (x : X)
   → ((⌜ 𝟚-classifies-decidable-subsets ⌝⁻¹ (A , δ) x ＝ ₀) ⇔ ¬ (x ∈ A))
   × ((⌜ 𝟚-classifies-decidable-subsets ⌝⁻¹ (A , δ) x ＝ ₁) ⇔   (x ∈ A))
 𝟚-classifies-decidable-subsets-values {X} A δ x = γ
  where
   χ : (Σ A ꞉ (X → Ω 𝓣) , is-complemented-subset A) → (X → 𝟚)
   χ = ⌜ 𝟚-classifies-decidable-subsets ⌝⁻¹
   γ : (χ (A , δ) x ＝ ₀ ⇔ ¬ (x ∈ A))
     × (χ (A , δ) x ＝ ₁ ⇔   (x ∈ A))
   γ = pr₂ (boolean-value' (δ x))

\end{code}

Added by Tom de Jong, November 2021.

\begin{code}

decidable-⇔ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
            → X ⇔ Y
            → decidable X
            → decidable Y
decidable-⇔ {𝓤} {𝓥} {X} {Y} (f , g) (inl  x) = inl (f x)
decidable-⇔ {𝓤} {𝓥} {X} {Y} (f , g) (inr nx) = inr (nx ∘ g)

decidable-cong : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
               → X ≃ Y
               → decidable X
               → decidable Y
decidable-cong e = decidable-⇔ (⌜ e ⌝ , ⌜ e ⌝⁻¹)

\end{code}

Added by Tom de Jong in January 2022.

\begin{code}

all-types-are-¬¬-decidable : (X : 𝓤 ̇  ) → ¬¬ (decidable X)
all-types-are-¬¬-decidable X h = claim₂ claim₁
 where
  claim₁ : ¬ X
  claim₁ x = h (inl x)
  claim₂ : ¬¬ X
  claim₂ nx = h (inr nx)

¬¬-stable-if-decidable : (X : 𝓤 ̇  ) → decidable X → ¬¬-stable X
¬¬-stable-if-decidable X (inl  x) = λ _ → x
¬¬-stable-if-decidable X (inr nx) = λ h → 𝟘-elim (h nx)

\end{code}

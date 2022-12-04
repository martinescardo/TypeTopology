Martin Escardo 2011. With additions by Tom de Jong 2021.

We look at decidable propositions, detachable families, and complemented subsets.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module NotionsOfDecidability.Decidable where

open import MLTT.Spartan

open import MLTT.Plus-Properties
open import MLTT.Two-Properties
open import UF.Subsingletons

¬¬-elim : {A : 𝓤 ̇ } → decidable A → ¬¬ A → A
¬¬-elim (inl a) f = a
¬¬-elim (inr g) f = 𝟘-elim(f g)

map-decidable : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → (B → A) → decidable A → decidable B
map-decidable f g (inl x) = inl (f x)
map-decidable f g (inr h) = inr (λ y → h (g y))

map-decidable-corollary : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A ⇔ B) → (decidable A ⇔ decidable B)
map-decidable-corollary (f , g) = map-decidable f g , map-decidable g f

map-decidable' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → ¬ B) → (¬ A → B) → decidable A → decidable B
map-decidable' f g (inl x) = inr (f x)
map-decidable' f g (inr h) = inl (g h)

empty-decidable : {X : 𝓤 ̇ } → is-empty X → decidable X
empty-decidable = inr

𝟘-decidable : decidable (𝟘 {𝓤})
𝟘-decidable = empty-decidable 𝟘-elim

pointed-decidable : {X : 𝓤 ̇ } → X → decidable X
pointed-decidable = inl

𝟙-decidable : decidable (𝟙 {𝓤})
𝟙-decidable = pointed-decidable ⋆

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
         → Σ b ꞉ 𝟚 , (b ＝ ₀ → A)
                   × (b ＝ ₁ → B)
which-of (inl a) = ₀ , (λ (r : ₀ ＝ ₀) → a) , λ (p : ₀ ＝ ₁) → 𝟘-elim (zero-is-not-one p)
which-of (inr b) = ₁ , (λ (p : ₁ ＝ ₀) → 𝟘-elim (zero-is-not-one (p ⁻¹))) , (λ (r : ₁ ＝ ₁) → b)

\end{code}

The following is a special case we are interested in:

\begin{code}

boolean-value : {A : 𝓤 ̇ }
              → decidable A
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

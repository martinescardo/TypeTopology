Tom de Jong, 1 November 2021.

We show that 𝟚 classifies decidable subsets.

We start by defining the type Ωᵈ 𝓤 of decidable propositions in a type
universe 𝓤 and we show that 𝟚 ≃ Ωᵈ 𝓤 (for any universe 𝓤).

Added 22 June 2024: 𝟚 ≃ Ω 𝓤 if and only if excluded middle (EM) holds in 𝓤.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module NotionsOfDecidability.DecidableClassifier where

open import MLTT.Spartan

open import MLTT.Two-Properties

open import UF.DiscreteAndSeparated
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Lower-FunExt
open import UF.Powerset
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

open import NotionsOfDecidability.Decidable

boolean-value' : {A : 𝓤 ̇ }
               → is-decidable A
               → Σ b ꞉ 𝟚 , (b ＝ ₀ ↔ ¬ A)
                         × (b ＝ ₁ ↔   A)
boolean-value' {𝓤} {A} (inl a ) = (₁ , ϕ , ψ)
 where
  ϕ : ₁ ＝ ₀ ↔ ¬ A
  ϕ = one-is-zero-elim , (λ na → 𝟘-elim (na a))
  ψ : ₁ ＝ ₁ ↔ A
  ψ = (λ _ → a) , (λ _ → refl)
boolean-value' {𝓤} {A} (inr na) = ₀ , ϕ , ψ
 where
  ϕ : ₀ ＝ ₀ ↔ ¬ A
  ϕ = (λ _ → na) , (λ _ → refl)
  ψ : ₀ ＝ ₁ ↔ A
  ψ = zero-is-one-elim , (λ a → 𝟘-elim (na a))

inclusion-of-booleans : 𝟚 → Ω 𝓤
inclusion-of-booleans ₀ = 𝟘 , 𝟘-is-prop
inclusion-of-booleans ₁ = 𝟙 , 𝟙-is-prop

private
 Ωᵈ : (𝓤 : Universe) → 𝓤 ⁺ ̇
 Ωᵈ 𝓤 = Σ P ꞉ Ω 𝓤 , is-decidable (P holds)

 inclusion-of-decidable-props : Ωᵈ 𝓤 → Ω 𝓤
 inclusion-of-decidable-props = pr₁

 ⟨_⟩ : Ωᵈ 𝓤 → 𝓤 ̇
 ⟨ (P , i) , δ ⟩ = P

inclusion-of-booleans-into-decidable-props : 𝟚 → Ωᵈ 𝓤
inclusion-of-booleans-into-decidable-props ₀ = (𝟘 , 𝟘-is-prop) , 𝟘-is-decidable
inclusion-of-booleans-into-decidable-props ₁ = (𝟙 , 𝟙-is-prop) , 𝟙-is-decidable

inclusion-of-booleans-∼ :
 inclusion-of-booleans {𝓤} ∼
 inclusion-of-decidable-props ∘ inclusion-of-booleans-into-decidable-props
inclusion-of-booleans-∼ ₀ = refl
inclusion-of-booleans-∼ ₁ = refl

module _
        {𝓤 : Universe}
        (fe : funext 𝓤 𝓤)
        (pe : propext 𝓤)
       where

 to-Ωᵈ-＝ : (P Q : Ωᵈ 𝓤)
          → (⟨ P ⟩ → ⟨ Q ⟩)
          → (⟨ Q ⟩ → ⟨ P ⟩)
          → P ＝ Q
 to-Ωᵈ-＝ ((P , i) , δ) ((Q , j) , ε) α β =
  to-subtype-＝ σ (to-subtype-＝ τ (pe i j α β))
  where
   σ : (P : Ω 𝓤) → is-prop (is-decidable (P holds))
   σ P = decidability-of-prop-is-prop (lower-funext 𝓤 𝓤 fe) (holds-is-prop P)
   τ : (X : 𝓤 ̇ )→ is-prop (is-prop X)
   τ _ = being-prop-is-prop fe

 𝟚-is-the-type-of-decidable-propositions : 𝟚 ≃ Ωᵈ 𝓤
 𝟚-is-the-type-of-decidable-propositions = qinveq f (g , η , ε)
  where
   f : 𝟚 → Ωᵈ 𝓤
   f = inclusion-of-booleans-into-decidable-props
   g : Ωᵈ 𝓤 → 𝟚
   g (P , δ) = pr₁ (boolean-value' δ)
   η : g ∘ f ∼ id
   η ₀ = refl
   η ₁ = refl
   ε : f ∘ g ∼ id
   ε P = 𝟚-equality-cases ε₀ ε₁
    where
     lemma : (g P ＝ ₀ ↔ ¬ ⟨ P ⟩)
           × (g P ＝ ₁ ↔   ⟨ P ⟩)
     lemma = pr₂ (boolean-value' (pr₂ P))
     ε₀ : g P ＝ ₀
        → (f ∘ g) P ＝ P
     ε₀ e = to-Ωᵈ-＝ (f (g P)) P
             (λ (q : ⟨ f (g P) ⟩) → 𝟘-elim (transport (λ b → ⟨ f b ⟩) e q))
             (λ (p : ⟨ P ⟩) → 𝟘-elim (lr-implication (pr₁ lemma) e p))
     ε₁ : g P ＝ ₁
        → (f ∘ g) P ＝ P
     ε₁ e = to-Ωᵈ-＝ (f (g P)) P
             (λ _ → lr-implication (pr₂ lemma) e)
             (λ _ → transport⁻¹ (λ (b : 𝟚) → ⟨ f b ⟩) e ⋆)

\end{code}

The promised result now follows promptly using two general lemmas on
equivalences.

(Note that one direction of the equivalence ΠΣ-distr-≃ is sometimes known as
"type-theoretic axiom of choice".)

\begin{code}

is-complemented-subset : {X : 𝓤 ̇ } → (X → Ω 𝓣) → 𝓤 ⊔ 𝓣 ̇
is-complemented-subset {𝓤} {𝓣} {X} A = (x : X) → is-decidable (x ∈ A)

module _
        (fe  : funext 𝓤 (𝓣 ⁺))
        (fe' : funext 𝓣 𝓣)
        (pe : propext 𝓣)
       where

 𝟚-classifies-decidable-subsets : {X : 𝓤 ̇ }
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
   {X : 𝓤 ̇ }
   (A : X → Ω 𝓣)
   (δ : is-complemented-subset A)
   (x : X)
   → ((⌜ 𝟚-classifies-decidable-subsets ⌝⁻¹ (A , δ) x ＝ ₀) ↔ ¬ (x ∈ A))
   × ((⌜ 𝟚-classifies-decidable-subsets ⌝⁻¹ (A , δ) x ＝ ₁) ↔   (x ∈ A))
 𝟚-classifies-decidable-subsets-values {X} A δ x = γ
  where
   χ : (Σ A ꞉ (X → Ω 𝓣) , is-complemented-subset A) → (X → 𝟚)
   χ = ⌜ 𝟚-classifies-decidable-subsets ⌝⁻¹
   γ : (χ (A , δ) x ＝ ₀ ↔ ¬ (x ∈ A))
     × (χ (A , δ) x ＝ ₁ ↔   (x ∈ A))
   γ = pr₂ (boolean-value' (δ x))

\end{code}

Added 22 June 2024.

We record that Ω is equivalent to 𝟚 precisely when EM holds.

\begin{code}

open import UF.ClassicalLogic

module _
        {𝓤 : Universe}
        (fe : funext 𝓤 𝓤)
        (pe : propext 𝓤)
       where

\end{code}

Firstly, EM holds if and only if the inclusion Ωᵈ ↪ Ω of decidable propositions
into all propositions is an equivalence.

\begin{code}
 EM-gives-inclusion-of-decidable-props-is-equiv :
  EM 𝓤 → is-equiv (inclusion-of-decidable-props)
 EM-gives-inclusion-of-decidable-props-is-equiv em =
  qinvs-are-equivs
   inclusion-of-decidable-props
   ((λ 𝕡@(P , i) → 𝕡 , em P i) ,
    (λ P → to-Ωᵈ-＝ fe pe _ P id id) ,
    λ _ → refl)

 inclusion-of-decidable-props-is-equiv-gives-EM :
  is-equiv (inclusion-of-decidable-props) → EM 𝓤
 inclusion-of-decidable-props-is-equiv-gives-EM e P i = ℙ-is-decidable
  where
   f : Ω 𝓤 → Ωᵈ 𝓤
   f = inverse inclusion-of-decidable-props e
   ℙ : Ω 𝓤
   ℙ = (P , i)
   ℙ' : Ω 𝓤
   ℙ' = inclusion-of-decidable-props (f ℙ)
   ℙ'-is-decidable : is-decidable (ℙ' holds)
   ℙ'-is-decidable = pr₂ (f ℙ)
   ℙ-is-decidable : is-decidable (ℙ holds)
   ℙ-is-decidable =
    transport (λ - → is-decidable (- holds))
              (inverses-are-sections inclusion-of-decidable-props e ℙ)
              ℙ'-is-decidable

\end{code}

Since 𝟚 is equivalent to Ωᵈ, we get that EM holds if and only if the inclusion
𝟚 ↪ Ω of the booleans into all propositions is an equivalence.

\begin{code}

 EM-gives-inclusion-of-booleans-is-equiv :
  EM 𝓤 → is-equiv (inclusion-of-booleans)
 EM-gives-inclusion-of-booleans-is-equiv em =
  equiv-closed-under-∼
   (inclusion-of-decidable-props ∘ inclusion-of-booleans-into-decidable-props)
   inclusion-of-booleans
   (∘-is-equiv
    (⌜⌝-is-equiv (𝟚-is-the-type-of-decidable-propositions fe pe))
    (EM-gives-inclusion-of-decidable-props-is-equiv em))
   inclusion-of-booleans-∼

 inclusion-of-booleans-is-equiv-gives-EM :
  is-equiv (inclusion-of-booleans) → EM 𝓤
 inclusion-of-booleans-is-equiv-gives-EM e =
  inclusion-of-decidable-props-is-equiv-gives-EM
   (≃-2-out-of-3-right
    (⌜⌝-is-equiv (𝟚-is-the-type-of-decidable-propositions fe pe))
    (equiv-closed-under-∼ _ _ e (∼-sym inclusion-of-booleans-∼)))

\end{code}

In fact, EM holds if and only if we have any equivalence between 𝟚 and Ω,
because any such equivalence would prove that Ω is discrete which is equivalent
to EM.

\begin{code}

 EM-gives-𝟚-is-the-type-of-propositions : EM 𝓤 → 𝟚 ≃ Ω 𝓤
 EM-gives-𝟚-is-the-type-of-propositions em =
  inclusion-of-booleans , EM-gives-inclusion-of-booleans-is-equiv em

 𝟚-is-the-type-of-propositions-gives-EM : 𝟚 ≃ Ω 𝓤 → EM 𝓤
 𝟚-is-the-type-of-propositions-gives-EM e =
  Ω-discrete-gives-EM fe pe (equiv-to-discrete e 𝟚-is-discrete)

\end{code}

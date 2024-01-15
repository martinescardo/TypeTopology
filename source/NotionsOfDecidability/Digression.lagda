Martin Escardo. 22 August 2021

Based on this discussion: https://twitter.com/EgbertRijke/status/1429443868450295810

\begin{code}

{-# OPTIONS --safe --without-K #-}

module NotionsOfDecidability.Digression where

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import UF.Equiv

T : 𝓤 ̇ → 𝓤 ̇
T = is-decidable

η : (X : 𝓤 ̇ ) → X → T X
η X = inl

μ : (X : 𝓤 ̇ ) → T (T X) → T X
μ X (inl d) = d
μ X (inr u) = inr (λ x → u (inl x))

T-is-nonempty : (X : 𝓤 ̇ ) → is-nonempty (T X)
T-is-nonempty X u = u (inr (λ x → u (inl x)))

μη : (X : 𝓤 ̇ ) → μ X ∘ η (T X) ∼ id
μη X (inl x) = refl
μη X (inr u) = refl

ημ : (X : 𝓤 ̇ ) → η (T X) ∘ μ X ∼ id
ημ X (inl (inl x)) = refl
ημ X (inl (inr u)) = refl
ημ X (inr u) = 𝟘-elim (u (inr (λ x → u (inl x))))

μ-is-invertible : (X : 𝓤 ̇ ) → invertible (μ X)
μ-is-invertible X = η (T X) , ημ X , μη X

μ-≃ : (X : 𝓤 ̇ ) → T (T X) ≃ T X
μ-≃ X = qinveq (μ X) (μ-is-invertible X)

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

η⁻¹ : {A : 𝓤 ̇ } → is-nonempty A → (T A → A)
η⁻¹ ϕ (inl a) = a
η⁻¹ ϕ (inr u) = 𝟘-elim (ϕ u)

η⁻¹-is-retraction : {A : 𝓤 ̇ } (ϕ : is-nonempty A) → η⁻¹ ϕ ∘ η A ∼ id
η⁻¹-is-retraction ϕ a = refl

η⁻¹-is-section : {A : 𝓤 ̇ } (ϕ : is-nonempty A) → η A ∘ η⁻¹ ϕ ∼ id
η⁻¹-is-section ϕ = retraction-of-η-is-section (η⁻¹ ϕ) (η⁻¹-is-retraction ϕ)

η-invertible-gives-non-empty : {X : 𝓤 ̇ } → invertible (η X) → is-nonempty X
η-invertible-gives-non-empty (α , _ , _) = raw-T-algebras-are-non-empty α

nonempty-gives-η-invertible : {X : 𝓤 ̇ } → is-nonempty X → invertible (η X)
nonempty-gives-η-invertible {𝓤} {X} ϕ = η⁻¹ ϕ , η⁻¹-is-retraction ϕ , η⁻¹-is-section ϕ

η-≃ : (X : 𝓤 ̇ ) → is-nonempty X → X ≃ T X
η-≃ X ϕ = qinveq (η X) (nonempty-gives-η-invertible ϕ)

retractions-of-η-are-invertible : {A : 𝓤 ̇ } (α : T A → A)
                                → α ∘ η A ∼ id
                                → invertible α
retractions-of-η-are-invertible {𝓤} {A} α h = η A , retraction-of-η-is-section α h , h

retractions-of-η-are-unique : {A : 𝓤 ̇ } (α : T A → A)
                            → α ∘ η A ∼ id
                            → (ϕ : is-nonempty A) → α ∼ η⁻¹ ϕ
retractions-of-η-are-unique α h ϕ (inl a) = h a
retractions-of-η-are-unique α h ϕ (inr u) = 𝟘-elim (ϕ u)

is-proto-algebra : 𝓤 ̇ → 𝓤 ̇
is-proto-algebra A = Σ α ꞉ (T A → A) , α ∘ η A ∼ id

proto-algebras-are-non-empty : {A : 𝓤 ̇ } → is-proto-algebra A → is-nonempty A
proto-algebras-are-non-empty (α , _) = raw-T-algebras-are-non-empty α

nonempty-types-are-proto-algebras : {A : 𝓤 ̇ } → is-nonempty A → is-proto-algebra A
nonempty-types-are-proto-algebras ϕ = η⁻¹ ϕ , η⁻¹-is-retraction ϕ

\end{code}

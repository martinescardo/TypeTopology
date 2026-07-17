Martin Escardo, 31st March 2023

In collaboration with Marc Bezem, Thierry Coquand, Peter Dybjer.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.SmallnessProperties where

open import MLTT.List
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import MLTT.Two-Properties
open import NotionsOfDecidability.Decidable
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size

smallness-closed-under-≃ : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                         → X is 𝓦 small
                         → X ≃ Y
                         → Y is 𝓦 small
smallness-closed-under-≃ (X' , 𝕗) 𝕘 = X' , (𝕗 ● 𝕘)

smallness-closed-under-≃' : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                          → X is 𝓦 small
                          → Y ≃ X
                          → Y is 𝓦 small
smallness-closed-under-≃' s 𝕘 = smallness-closed-under-≃ s (≃-sym 𝕘)

Σ-is-small : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
           → X is 𝓤' small
           → ((x : X) → A x is 𝓥' small)
           → Σ A is 𝓤' ⊔ 𝓥' small
Σ-is-small {𝓤} {𝓥} {𝓤'} {𝓥'} {X} {A} (X' , 𝕗) σ = γ
 where
  A' : X → 𝓥' ̇
  A' x = resized (A x) (σ x)

  𝕘 : (x : X) → A' x ≃ A x
  𝕘 x = resizing-condition (σ x)

  γ : (Σ A) is 𝓤' ⊔ 𝓥' small
  γ = (Σ (A' ∘ ⌜ 𝕗 ⌝)) , Σ-bicong (A' ∘ ⌜ 𝕗 ⌝) A 𝕗 (λ x → 𝕘 (⌜ 𝕗 ⌝ x))

Π-is-small : FunExt
           → {X : 𝓤 ̇ } {A : X → 𝓥 ̇ }
           → X is 𝓤' small
           → ((x : X) → A x is 𝓥' small)
           → Π A is 𝓤' ⊔ 𝓥' small
Π-is-small {𝓤} {𝓥} {𝓤'} {𝓥'} fe {X} {A} (X' , 𝕗) σ = γ
 where
  A' : X → 𝓥' ̇
  A' x = resized (A x) (σ x)

  𝕘 : (x : X) → A' x ≃ A x
  𝕘 x = resizing-condition (σ x)

  γ : (Π A) is 𝓤' ⊔ 𝓥' small
  γ = (Π (A' ∘ ⌜ 𝕗 ⌝)) ,
      Π-bicong fe (A' ∘ ⌜ 𝕗 ⌝) A 𝕗 (λ x → 𝕘 (⌜ 𝕗 ⌝ x))

decidable-embeddings-have-any-size : (𝓦 : Universe)
                                     {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y}
                                   → is-embedding f
                                   → each-fiber-of f is-decidable
                                   → f is 𝓦 small-map
decidable-embeddings-have-any-size 𝓦 {X} {Y} {f} e δ y =
 decidable-propositions-have-any-size (fiber f y) (e y) (δ y)

id-has-any-size : (𝓦 : Universe) {X : 𝓤 ̇ } → id {𝓤} {X} is 𝓦 small-map
id-has-any-size 𝓦 {𝓤} = equivs-have-any-size id (id-is-equiv 𝓤)

∘-decidable-embeddings : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
                         {f : X → Y} {g : Y → Z}
                       → is-embedding g
                       → each-fiber-of f is-decidable
                       → each-fiber-of g is-decidable
                       → each-fiber-of (g ∘ f) is-decidable
∘-decidable-embeddings {𝓤} {𝓥} {𝓦} {X} {Y} {Z} {f} {g} ge σ τ z = γ
 where
  δ : is-decidable (Σ (y , _) ꞉ fiber g z , fiber f y)
  δ = decidable-closed-under-Σ (ge z) (τ z) (λ (y , _) → σ y)

  γ : is-decidable (fiber (g ∘ f) z)
  γ = decidability-is-closed-under-≃ (≃-sym (fiber-of-composite f g z)) δ

∘-small-maps : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ }
               {f : X → Y} {g : Y → Z}
             → f is 𝓣 small-map
             → g is 𝓣' small-map
             → (g ∘ f) is 𝓣 ⊔ 𝓣' small-map
∘-small-maps {𝓤} {𝓥} {𝓦} {𝓣} {𝓣'} {X} {Y} {Z} {f} {g} σ τ z = γ
 where
  A : Y → 𝓣 ̇
  A y = resized (fiber f y) (σ y)

  φ : (y : Y) → A y ≃ fiber f y
  φ y = resizing-condition (σ y)

  B : 𝓣' ̇
  B = resized (fiber g z) (τ z)

  ψ : B ≃ fiber g z
  ψ = resizing-condition (τ z)

  δ = (Σ b ꞉ B , A (pr₁ (⌜ ψ ⌝ b)))       ≃⟨ I ⟩
      (Σ (y , _) ꞉ fiber g z , A y)       ≃⟨ II ⟩
      (Σ (y , _) ꞉ fiber g z , fiber f y) ≃⟨ III ⟩
      fiber (g ∘ f) z                     ■
      where
       I   = Σ-change-of-variable-≃ (A ∘ pr₁) ψ
       II  = Σ-cong (φ ∘ pr₁)
       III = ≃-sym (fiber-of-composite f g z)

  γ : fiber (g ∘ f) z is 𝓣 ⊔ 𝓣' small
  γ = domain ⌜ δ ⌝ , δ

maps-between-small-types-are-small-maps
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y)
 → X is 𝓦 small
 → Y is 𝓦 small
 → f is 𝓦 small-map
maps-between-small-types-are-small-maps f X-small Y-small y =
 Σ-is-small
  X-small
  (λ x → identity-types-of-small-types-are-small Y-small (f x) y)

NatΣ-is-small : {X : 𝓤 ̇ } {A : X → 𝓥 ̇ } {B : X → 𝓦 ̇ }
                (τ : Nat A B)
              → ((x : X) → τ x is 𝓣 small-map)
              → NatΣ τ is 𝓣 small-map
NatΣ-is-small {𝓤} {𝓥} {𝓦} {𝓣} {X} {A} {B} τ τ-small = γ
 where
  F : (x : X) → B x → 𝓣 ̇
  F x b = resized (fiber (τ x) b) (τ-small x b)

  γ : NatΣ τ is 𝓣 small-map
  γ (x , b) = F x b ,
             (F x b                  ≃⟨ resizing-condition (τ-small x b) ⟩
              fiber (τ x) b          ≃⟨ NatΣ-fiber-equiv A B τ x b ⟩
              fiber (NatΣ τ) (x , b) ■)

inl-has-any-size : (𝓦 : Universe) {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → inl {𝓤} {𝓥} {X} {Y} is 𝓦 small-map
inl-has-any-size 𝓦 =
 decidable-embeddings-have-any-size 𝓦 (inl-is-embedding _ _) γ
 where
  γ : each-fiber-of inl is-decidable
  γ (inl x) = inl (x , refl)
  γ (inr y) = inr (λ ((x , p) : fiber inl (inr y)) → +disjoint p)

inr-has-any-size : (𝓦 : Universe) {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → inr {𝓤} {𝓥} {X} {Y} is 𝓦 small-map
inr-has-any-size 𝓦 =
 decidable-embeddings-have-any-size 𝓦 (inr-is-embedding _ _) γ
 where
  γ : each-fiber-of inr is-decidable
  γ (inl x) = inr (λ ((y , p) : fiber inr (inl x)) → +disjoint' p)
  γ (inr y) = inl (y , refl)

pair₀ : {X : 𝓤 ̇ } → X → 𝟚 × X
pair₀ x = (₀ , x)

pair₀-is-embedding : {X : 𝓤 ̇ } → is-embedding (pair₀ {𝓤} {X})
pair₀-is-embedding (₀ , x) (x , refl) (x , refl) = refl

pair₀-is-decidable : {X : 𝓤 ̇ } → each-fiber-of (pair₀ {𝓤} {X}) is-decidable
pair₀-is-decidable (₀ , x) = inl (x , refl)
pair₀-is-decidable (₁ , x) = inr (λ (y , p) → zero-is-not-one (ap pr₁ p))

pair₀-has-any-size : (𝓦 : Universe) {X : 𝓤 ̇ } → (pair₀ {𝓤} {X}) is 𝓦 small-map
pair₀-has-any-size 𝓦 = decidable-embeddings-have-any-size 𝓦
                         pair₀-is-embedding
                         pair₀-is-decidable

[]-is-embedding : {X : 𝓤 ̇ } → is-embedding (λ (x : X) → [ x ])
[]-is-embedding (x ∷ []) (x , refl) (x , refl) = refl

[]-is-decidable : {X : 𝓤 ̇ } → each-fiber-of (λ (x : X) → [ x ]) is-decidable
[]-is-decidable {𝓤} {X} [] =
  inr (λ (x , p) → []-is-not-cons x [] (p ⁻¹))
[]-is-decidable {𝓤} {X} (x ∷ []) =
  inl (x , refl)
[]-is-decidable {𝓤} {X} (x₀ ∷ x₁ ∷ xs) =
  inr λ (x , p) → []-is-not-cons x₁ xs (equal-tails p)

[]-has-any-size : (𝓦 : Universe) {X : 𝓤 ̇ } → (λ (x : X) → [ x ]) is 𝓦 small-map
[]-has-any-size 𝓦 = decidable-embeddings-have-any-size 𝓦
                      []-is-embedding
                      []-is-decidable


module _ (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 ∥∥-is-small : {X : 𝓤 ̇ }
             → X is 𝓦 small
             → ∥ X ∥ is 𝓦 small
 ∥∥-is-small (X' , 𝕗) = ∥ X' ∥ ,
                       qinveq (∥∥-functor ⌜ 𝕗 ⌝)
                        (∥∥-functor ⌜ 𝕗 ⌝⁻¹ ,
                         (λ _ → ∥∥-is-prop _ _) ,
                         (λ _ → ∥∥-is-prop _ _))

\end{code}

Added by Martin Escardo and Tom de Jong 14th November 2024.

\begin{code}

open import UF.UA-FunExt
open import UF.Univalence

Id-is-small : is-univalent 𝓤
            → funext 𝓤 (𝓤 ⁺)
            → (X : 𝓤 ̇ )
            → (Id {𝓤} {X}) is 𝓤 small-map
Id-is-small {𝓤} ua fe⁺ X A =
 (Σ x ꞉ X , (Π y ꞉ X , (x ＝ y) ≃ A y)) ,
 ((Σ x ꞉ X , (Π y ꞉ X , (x ＝ y) ≃ A y))  ≃⟨ I ⟩
  (Σ x ꞉ X , (Π y ꞉ X , (x ＝ y) ＝ A y)) ≃⟨ II ⟩
  fiber Id A                              ■)
   where
    fe : funext 𝓤 𝓤
    fe = univalence-gives-funext ua

    I  = Σ-cong (λ x → Π-cong fe fe⁺ (λ y → ≃-sym (univalence-≃ ua _ _)))
    II = Σ-cong (λ x → ≃-sym (≃-funext fe⁺ _ _))

\end{code}

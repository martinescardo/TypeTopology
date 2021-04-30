Martin Escardo, 5th September 2018.

Univalence gives the usual mathematical notion of equality for the
subsets of a type: two subsets of a type are equal precisely when they
have the same elements, like in ZF (C). And *not* when they are
isomorphic, for any reasonable notion of isomorphism between subsets
of a given type.

A subset of a type X in a universe 𝓤 is an embedding of some given
type into X, or, equivalently, a map of X into the subtype classifier
Ω 𝓤 of the universe 𝓤 (see the module UF-Classifiers).

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

module UF-Powerset where

open import SpartanMLTT
open import UF-Subsingletons
open import UF-Equiv
open import UF-Univalence
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-UA-FunExt
open import UF-Subsingletons-FunExt
open import UF-Equiv-FunExt

𝓟 : 𝓤 ̇ → 𝓤 ⁺ ̇
𝓟 {𝓤} X = X → Ω 𝓤

powersets-are-sets' : Univalence → {X : 𝓤 ̇ } → is-set (𝓟 X)

powersets-are-sets' {𝓤} ua = powersets-are-sets
                               (univalence-gives-funext' 𝓤 (𝓤 ⁺) (ua 𝓤) (ua (𝓤 ⁺)))
                               (univalence-gives-propext (ua 𝓤))

_∈_ : {X : 𝓤 ̇ } → X → (X → Ω 𝓥) → 𝓥 ̇
x ∈ A = A x holds

_⊆_ : {X : 𝓤 ̇ } → (X → Ω 𝓥) → (X → Ω 𝓦) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
A ⊆ B = ∀ x → x ∈ A → x ∈ B

∈-is-prop : {X : 𝓤 ̇ } (A : X → Ω 𝓥) (x : X) → is-prop (x ∈ A)
∈-is-prop A x = holds-is-prop (A x)

⊆-is-prop' : funext 𝓤 𝓥
           → funext 𝓥 𝓥
           → {X : 𝓤 ̇ } (A B : X → Ω 𝓥) → is-prop (A ⊆ B)
⊆-is-prop' fe fe' A B = Π-is-prop fe
                         (λ x → Π-is-prop fe'
                         (λ _ → ∈-is-prop B x))

⊆-is-prop : funext 𝓤 𝓤
          → {X : 𝓤 ̇ } (A B : 𝓟 X) → is-prop (A ⊆ B)
⊆-is-prop fe = ⊆-is-prop' fe fe

⊆-refl : {X : 𝓤 ̇ } (A : 𝓟 X) → A ⊆ A
⊆-refl A x = id

⊆-trans : {X : 𝓤 ̇ } (A B C : 𝓟 X) → A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans A B C s t x a = t x (s x a)

⊆-refl-consequence : {X : 𝓤 ̇ } (A B : 𝓟 X)
                   → A ≡ B → (A ⊆ B) × (B ⊆ A)

⊆-refl-consequence {X} A A (refl) = ⊆-refl A , ⊆-refl A

subset-extensionality : propext 𝓤
                      → funext 𝓤 (𝓤 ⁺)
                      → {X : 𝓤 ̇ } {A B : 𝓟 X}
                      → A ⊆ B → B ⊆ A → A ≡ B

subset-extensionality {𝓤} pe fe {X} {A} {B} h k = dfunext fe φ
 where
  φ : (x : X) → A x ≡ B x
  φ x = to-subtype-≡
           (λ _ → being-prop-is-prop (lower-funext 𝓤 (𝓤 ⁺) fe))
           (pe (holds-is-prop (A x)) (holds-is-prop (B x))
               (h x) (k x))

subset-extensionality' : Univalence
                       → {X : 𝓤 ̇ } {A B : 𝓟 X}
                       → A ⊆ B → B ⊆ A → A ≡ B

subset-extensionality' {𝓤} ua = subset-extensionality
                                 (univalence-gives-propext (ua 𝓤))
                                 (univalence-gives-funext' 𝓤 (𝓤 ⁺) (ua 𝓤) (ua (𝓤 ⁺)))

infix  40 _∈_

\end{code}

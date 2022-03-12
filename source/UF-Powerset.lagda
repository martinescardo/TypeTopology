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

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

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

∅ : {X : 𝓤 ̇ } →  X → Ω 𝓥
∅ _ = 𝟘 , 𝟘-is-prop

full : {X : 𝓤 ̇ } →  X → Ω 𝓥
full _ = 𝟙 , 𝟙-is-prop

_∈_ : {X : 𝓤 ̇ } → X → (X → Ω 𝓥) → 𝓥 ̇
x ∈ A = A x holds

_∉_ : {X : 𝓤 ̇ } → X → (X → Ω 𝓥) → 𝓥 ̇
x ∉ A = ¬ (x ∈ A)

are-disjoint : {X : 𝓤 ̇ } → (X → Ω 𝓥) → (X → Ω 𝓦) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
are-disjoint {𝓤} {𝓥} {𝓦} {X} A B = (x : X) → ¬((x ∈ A) × (x ∈ B))

being-disjoint-is-prop : Fun-Ext
                       → {X : 𝓤 ̇ } (A : X → Ω 𝓥) (B : X → Ω 𝓦)
                       → is-prop (are-disjoint A B)
being-disjoint-is-prop fe A B = Π-is-prop fe (λ _ → negations-are-props fe)

_⊆_ _⊇_ : {X : 𝓤 ̇ } → (X → Ω 𝓥) → (X → Ω 𝓦) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
A ⊆ B = ∀ x → x ∈ A → x ∈ B
A ⊇ B = B ⊆ A

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

∅-is-least : {X : 𝓤 ̇ } (A : 𝓟 X) → ∅ {𝓤} {𝓤} ⊆ A
∅-is-least x _ = 𝟘-induction

⊆-refl' : {X : 𝓤 ̇ } (A : X → Ω 𝓥) → A ⊆ A
⊆-refl' A x = id

⊆-refl : {X : 𝓤 ̇ } (A : 𝓟 X) → A ⊆ A
⊆-refl = ⊆-refl'

⊆-trans : {X : 𝓤 ̇ } (A B C : 𝓟 X) → A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans A B C s t x a = t x (s x a)

⊆-refl-consequence : {X : 𝓤 ̇ } (A B : 𝓟 X)
                   → A ≡ B → (A ⊆ B) × (B ⊆ A)

⊆-refl-consequence {X} A A (refl) = ⊆-refl A , ⊆-refl A

subset-extensionality'' : propext 𝓥
                        → funext 𝓤 (𝓥 ⁺)
                        → funext 𝓥 𝓥
                        → {X : 𝓤 ̇ } {A B : X → Ω 𝓥}
                        → A ⊆ B → B ⊆ A → A ≡ B

subset-extensionality'' {𝓥} {𝓤} pe fe fe' {X} {A} {B} h k = dfunext fe φ
 where
  φ : (x : X) → A x ≡ B x
  φ x = to-subtype-≡
           (λ _ → being-prop-is-prop fe')
           (pe (holds-is-prop (A x)) (holds-is-prop (B x))
               (h x) (k x))

subset-extensionality : propext 𝓤
                      → funext 𝓤 (𝓤 ⁺)
                      → {X : 𝓤 ̇ } {A B : 𝓟 X}
                      → A ⊆ B → B ⊆ A → A ≡ B

subset-extensionality {𝓤} pe fe = subset-extensionality'' pe fe (lower-funext 𝓤 (𝓤 ⁺) fe)

subset-extensionality' : Univalence
                       → {X : 𝓤 ̇ } {A B : 𝓟 X}
                       → A ⊆ B → B ⊆ A → A ≡ B

subset-extensionality' {𝓤} ua = subset-extensionality
                                 (univalence-gives-propext (ua 𝓤))
                                 (univalence-gives-funext' 𝓤 (𝓤 ⁺) (ua 𝓤) (ua (𝓤 ⁺)))

infix  40 _∈_
infix  40 _∉_

\end{code}

Tom de Jong, 24 January 2022
(Based on code from FreeJoinSemiLattice.lagda written 18-24 December 2020.)

Notation for the "total space" of a subset.

\begin{code}

module _
        {X : 𝓤 ̇ }
       where

 𝕋 : 𝓟 X → 𝓤 ̇
 𝕋 A = Σ x ꞉ X , x ∈ A

 𝕋-to-carrier : (A : 𝓟 X) → 𝕋 A → X
 𝕋-to-carrier A = pr₁

 𝕋-to-membership : (A : 𝓟 X) → (t : 𝕋 A) → (𝕋-to-carrier A t) ∈ A
 𝕋-to-membership A = pr₂

\end{code}

We use a named module when defining singleton subsets, so that we can write
❴ x ❵ without having to keep supplying the proof that the ambient type is a set.

\begin{code}

module singleton-subsets
        {X : 𝓤 ̇  }
        (X-is-set : is-set X)
       where

 ❴_❵ : X → 𝓟 X
 ❴ x ❵ = λ y → ((x ≡ y) , X-is-set)

 ❴❵-is-singleton : {x : X} → is-singleton (𝕋 ❴ x ❵)
 ❴❵-is-singleton {x} = singleton-types-are-singletons x

\end{code}

Next, we consider binary intersections and unions in the powerset. For the
latter, we need propositional truncations.

\begin{code}

module _
        {X : 𝓤 ̇ }
       where

 _∩_ : 𝓟 X → 𝓟 X → 𝓟 X
 (A ∩ B) x = (x ∈ A × x ∈ B) , ×-is-prop (∈-is-prop A x) (∈-is-prop B x)

 ∩-is-lowerbound₁ : (A B : 𝓟 X) → (A ∩ B) ⊆ A
 ∩-is-lowerbound₁ A B x = pr₁

 ∩-is-lowerbound₂ : (A B : 𝓟 X) → (A ∩ B) ⊆ B
 ∩-is-lowerbound₂ A B x = pr₂

 ∩-is-upperbound-of-lowerbounds : (A B C : 𝓟 X)
                                → C ⊆ A → C ⊆ B → C ⊆ (A ∩ B)
 ∩-is-upperbound-of-lowerbounds A B C s t x c = (s x c , t x c)

open import UF-PropTrunc

module binary-union-of-subsets
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt

 module _
         {X : 𝓤 ̇ }
        where

  _∪_ : 𝓟 X → 𝓟 X → 𝓟 X
  (A ∪ B) x = ∥ x ∈ A + x ∈ B ∥ , ∥∥-is-prop

  ∪-is-upperbound₁ : (A B : 𝓟 X) → A ⊆ (A ∪ B)
  ∪-is-upperbound₁ A B x a = ∣ inl a ∣

  ∪-is-upperbound₂ : (A B : 𝓟 X) → B ⊆ (A ∪ B)
  ∪-is-upperbound₂ A B x b = ∣ inr b ∣

  ∪-is-lowerbound-of-upperbounds : (A B C : 𝓟 X)
                                 → A ⊆ C → B ⊆ C → (A ∪ B) ⊆ C
  ∪-is-lowerbound-of-upperbounds A B C s t x = ∥∥-rec (∈-is-prop C x) γ
    where
     γ : (x ∈ A + x ∈ B) → x ∈ C
     γ (inl a) = s x a
     γ (inr b) = t x b

  ∅-left-neutral-for-∪ : propext 𝓤
                       → funext 𝓤 (𝓤 ⁺)
                       → (A : 𝓟 X) → ∅ ∪ A ≡ A
  ∅-left-neutral-for-∪ pe fe A = subset-extensionality pe fe
                                  s (∪-is-upperbound₂ ∅ A)
   where
    s : (∅ ∪ A) ⊆ A
    s x = ∥∥-rec (∈-is-prop A x) γ
     where
      γ : x ∈ ∅ + x ∈ A → x ∈ A
      γ (inl p) = 𝟘-elim p
      γ (inr a) = a

  ∅-right-neutral-for-∪ : propext 𝓤
                        → funext 𝓤 (𝓤 ⁺)
                        → (A : 𝓟 X) → A ≡ A ∪ ∅
  ∅-right-neutral-for-∪ pe fe A = subset-extensionality pe fe
                                   (∪-is-upperbound₁ A ∅) s
   where
    s : (A ∪ ∅) ⊆ A
    s x = ∥∥-rec (∈-is-prop A x) γ
     where
      γ : x ∈ A + x ∈ ∅ → x ∈ A
      γ (inl a) = a
      γ (inr p) = 𝟘-elim p

  ∪-assoc : propext 𝓤
          → funext 𝓤 (𝓤 ⁺)
          → associative (_∪_)
  ∪-assoc pe fe A B C = subset-extensionality pe fe s t
   where
    s : ((A ∪ B) ∪ C) ⊆ (A ∪ (B ∪ C))
    s x = ∥∥-rec i s₁
     where
      i : is-prop (x ∈ (A ∪ (B ∪ C)))
      i = ∈-is-prop (A ∪ (B ∪ C)) x
      s₁ : x ∈ (A ∪ B) + x ∈ C
         → x ∈ (A ∪ (B ∪ C))
      s₁ (inl u) = ∥∥-rec i s₂ u
       where
        s₂ : x ∈ A + x ∈ B
           → x ∈ (A ∪ (B ∪ C))
        s₂ (inl a) = ∪-is-upperbound₁ A (B ∪ C) x a
        s₂ (inr b) = ∪-is-upperbound₂ A (B ∪ C) x (∪-is-upperbound₁ B C x b)
      s₁ (inr c) = ∪-is-upperbound₂ A (B ∪ C) x (∪-is-upperbound₂ B C x c)
    t : (A ∪ (B ∪ C)) ⊆ ((A ∪ B) ∪ C)
    t x = ∥∥-rec i t₁
     where
      i : is-prop (x ∈ ((A ∪ B) ∪ C))
      i = ∈-is-prop ((A ∪ B) ∪ C) x
      t₁ : x ∈ A + x ∈ (B ∪ C)
         → x ∈ ((A ∪ B) ∪ C)
      t₁ (inl a) = ∪-is-upperbound₁ (A ∪ B) C x (∪-is-upperbound₁ A B x a)
      t₁ (inr u) = ∥∥-rec i t₂ u
       where
        t₂ : x ∈ B + x ∈ C
           → x ∈ ((A ∪ B) ∪ C)
        t₂ (inl b) = ∪-is-upperbound₁ (A ∪ B) C x (∪-is-upperbound₂ A B x b)
        t₂ (inr c) = ∪-is-upperbound₂ (A ∪ B) C x c

\end{code}

Again assuming propositional truncations, we can construct arbitrary suprema in
𝓟 (X : 𝓤) of families indexed by types in 𝓤.

\begin{code}

module unions-of-small-families
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt

 ⋃  : {X I : 𝓤 ̇ } (α : I → 𝓟 X) → 𝓟 X
 ⋃ {𝓤} {X} {I} α x = (∃ i ꞉ I , x ∈ α i) , ∃-is-prop

 ⋃-is-upperbound : {X I : 𝓤 ̇ } (α : I → 𝓟 X) (i : I)
                 → α i ⊆ ⋃ α
 ⋃-is-upperbound α i x a = ∣ i , a ∣

 ⋃-is-lowerbound-of-upperbounds : {X I : 𝓤 ̇ } (α : I → 𝓟 X) (A : 𝓟 X)
                                → ((i : I) → α i ⊆ A)
                                → ⋃ α ⊆ A
 ⋃-is-lowerbound-of-upperbounds {𝓤} {X} {I} α A ub x u =
  ∥∥-rec (∈-is-prop A x) γ u
   where
    γ : (Σ i ꞉ I , x ∈ α i) → x ∈ A
    γ (i , a) = ub i x a

\end{code}

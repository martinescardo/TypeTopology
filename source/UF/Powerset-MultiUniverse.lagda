Martin Escardo, 5th September 2018. Modified 27 September 2023 to
support the object of truth values to live in a different universe
than that of which the powerset is taken.


Univalence gives the usual mathematical notion of equality for the
subsets of a type: two subsets of a type are equal precisely when they
have the same elements, like in ZF (C). And *not* when they are
isomorphic, for any reasonable notion of isomorphism between subsets
of a given type.

A subset of a type X in a universe 𝓤 is an embedding of some given
type into X, or, equivalently, a map of X into the subtype classifier
Ω 𝓤 of the universe 𝓤 (see the module UF.Classifiers).

We generalize this to allow the powerset to have values in Ω 𝓥. The
module UF.Powerset specializes this module to the case 𝓤=𝓥.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module UF.Powerset-MultiUniverse where

open import MLTT.Spartan
open import UF.FunExt
open import UF.Lower-FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties
open import UF.UA-FunExt
open import UF.Univalence

𝓟 : {𝓥 𝓤 : Universe} → 𝓤 ̇ → 𝓤 ⊔ (𝓥 ⁺) ̇
𝓟 {𝓥} {𝓤} X = X → Ω 𝓥

powersets-are-sets'' : funext 𝓤 (𝓥 ⁺)
                     → funext 𝓥 𝓥
                     → propext 𝓥
                     → {X : 𝓤 ̇ } → is-set (𝓟 {𝓥} X)
powersets-are-sets'' fe fe' pe = Π-is-set fe (λ x → Ω-is-set fe' pe)

powersets-are-sets : funext 𝓥 (𝓥 ⁺)
                   → propext 𝓥
                   → {X : 𝓥 ̇ } → is-set (X → Ω 𝓥)
powersets-are-sets {𝓥} fe = powersets-are-sets'' fe (lower-funext 𝓥 (𝓥 ⁺) fe)

𝓟-is-set' : funext 𝓤 (𝓤 ⁺)
          → propext 𝓤
          → {X : 𝓤 ̇ }
          → is-set (𝓟 {𝓤} X)
𝓟-is-set' = powersets-are-sets

𝓟-is-set : Univalence
         → {X : 𝓤 ̇ }
         → is-set (𝓟 X)
𝓟-is-set {𝓤} ua = 𝓟-is-set'
                    (univalence-gives-funext' 𝓤 (𝓤 ⁺) (ua 𝓤) (ua (𝓤 ⁺)))
                    (univalence-gives-propext (ua 𝓤))

comprehension : (X : 𝓤 ̇ ) → 𝓟 {𝓥} X → 𝓟 {𝓥} X
comprehension X A = A

syntax comprehension X (λ x → A) = ⁅ x ꞉ X ∣ A ⁆

∅ : {X : 𝓤 ̇ } →  𝓟 {𝓥} X
∅ _ = 𝟘 , 𝟘-is-prop

full : {X : 𝓤 ̇ } →  𝓟 {𝓥} X
full _ = 𝟙 , 𝟙-is-prop

_∈ₚ_ : {X : 𝓤 ̇ } → X → (X → Ω 𝓥) → Ω 𝓥
x ∈ₚ A = A x

_∈_ : {X : 𝓤 ̇ } → X → 𝓟 {𝓥} X → 𝓥 ̇
x ∈ A =  x ∈ₚ A holds

_∉_ : {X : 𝓤 ̇ } → X → 𝓟 {𝓥} X → 𝓥 ̇
x ∉ A = ¬ (x ∈ A)

is-empty-subset : {X : 𝓤 ̇ } → 𝓟 {𝓥} X → 𝓤 ⊔ 𝓥 ̇
is-empty-subset {𝓤} {𝓥} {X} A = (x : X) → x ∉ A

being-empty-subset-is-prop : Fun-Ext
                           → {X : 𝓤 ̇ } (A : 𝓟 {𝓥} X)
                           → is-prop (is-empty-subset A)
being-empty-subset-is-prop fe {X} A = Π-is-prop fe (λ x → negations-are-props fe)

are-disjoint : {X : 𝓤 ̇ } → 𝓟 {𝓥} X → 𝓟 {𝓦} X → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
are-disjoint {𝓤} {𝓥} {𝓦} {X} A B = (x : X) → ¬((x ∈ A) × (x ∈ B))

being-disjoint-is-prop : Fun-Ext
                       → {X : 𝓤 ̇ } (A : 𝓟 {𝓥} X) (B : 𝓟 {𝓦} X)
                       → is-prop (are-disjoint A B)
being-disjoint-is-prop fe A B = Π-is-prop fe (λ _ → negations-are-props fe)

_⊆_ _⊇_ : {X : 𝓤 ̇ } → 𝓟 {𝓥} X → 𝓟 {𝓦} X → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
A ⊆ B = ∀ x → x ∈ A → x ∈ B
A ⊇ B = B ⊆ A

∈-is-prop : {X : 𝓤 ̇ } (A : 𝓟 {𝓥} X) (x : X) → is-prop (x ∈ A)
∈-is-prop A x = holds-is-prop (A x)

∉-is-prop : funext 𝓥 𝓤₀ → {X : 𝓤 ̇ } (A : 𝓟 {𝓥} X) (x : X) → is-prop (x ∉ A)
∉-is-prop fe A x = negations-are-props fe

module subset-complement (fe : Fun-Ext) where

 _∖_ :  {X : 𝓤 ̇ } → 𝓟 {𝓥} X → 𝓟 {𝓦} X → 𝓟 {𝓥 ⊔ 𝓦} X
 A ∖ B = λ x → (x ∈ A × x ∉ B) , ×-is-prop (∈-is-prop A x) (∉-is-prop fe B x)

 infix  45 _∖_

 ∖-elim₀ : {X : 𝓤 ̇ } (A : 𝓟 {𝓥} X) (B : 𝓟 {𝓦} X) {x : X} → x ∈ A ∖ B → x ∈ A
 ∖-elim₀ A B = pr₁

 ∖-elim₁ : {X : 𝓤 ̇ } (A : 𝓟 {𝓥} X) (B : 𝓟 {𝓦} X) {x : X} → x ∈ A ∖ B → x ∉ B
 ∖-elim₁ A B = pr₂

𝓟-inverse-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                → (X → Y)
                → 𝓟 {𝓦} Y → 𝓟 {𝓦} X
𝓟-inverse-image {𝓤} {𝓥} {𝓦} {X} {Y} f B x = f x ∈ B , ∈-is-prop B (f x)

module 𝓟-image (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 𝓟-image : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
         → (X → Y)
         → 𝓟 {𝓦} X → 𝓟 {𝓤 ⊔ 𝓥 ⊔ 𝓦} Y
 𝓟-image {𝓤} {𝓥} {𝓦} {X} {Y} f A y = (∃ x ꞉ X , x ∈ A × (f x ＝ y)) , ∃-is-prop

module inhabited-subsets (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 is-inhabited : {X : 𝓤 ̇ } → 𝓟 {𝓥} X → 𝓤 ⊔ 𝓥 ̇
 is-inhabited {𝓤} {𝓥} {X} A = ∃ x ꞉ X , x ∈ A

 being-inhabited-is-prop : {X : 𝓤 ̇ } (A : 𝓟 {𝓥} X)
                         → is-prop (is-inhabited A)
 being-inhabited-is-prop {𝓤} {𝓥} {X} A = ∃-is-prop

 𝓟⁺ : 𝓤 ̇ → 𝓤 ⁺ ̇
 𝓟⁺ {𝓤} X = Σ A ꞉ 𝓟 X , is-inhabited A

 𝓟⁺-is-set' : funext 𝓤 (𝓤 ⁺) → propext 𝓤 → {X : 𝓤 ̇ } → is-set (𝓟⁺ X)
 𝓟⁺-is-set' fe pe {X} = subsets-of-sets-are-sets (𝓟 X)
                         is-inhabited
                         (𝓟-is-set' fe pe)
                         (λ {A} → being-inhabited-is-prop A)

 𝓟⁺-is-set : Univalence → {X : 𝓤 ̇ } → is-set (𝓟⁺ X)
 𝓟⁺-is-set {𝓤} ua = 𝓟⁺-is-set'
                      (univalence-gives-funext' 𝓤 (𝓤 ⁺) (ua 𝓤) (ua (𝓤 ⁺)))
                      (univalence-gives-propext (ua 𝓤))

 _∈⁺_ : {X : 𝓤 ̇ } → X → 𝓟⁺ X → 𝓤 ̇
 x ∈⁺ (A , _) = x ∈ A

 _∉⁺_ : {X : 𝓤 ̇ } → X → 𝓟⁺ X → 𝓤 ̇
 x ∉⁺ A = ¬ (x ∈⁺ A)

 infix  40 _∈⁺_
 infix  40 _∉⁺_

 open import UF.ClassicalLogic

 non-empty-subsets-are-inhabited : Excluded-Middle
                                 → {X : 𝓤 ̇ } (B : 𝓟 {𝓥} X)
                                 → ¬ is-empty-subset B
                                 → is-inhabited B
 non-empty-subsets-are-inhabited em B = not-Π-not-implies-∃ pt em

 uninhabited-subsets-are-empty : {X : 𝓤 ̇ } (B : 𝓟 {𝓥} X)
                               → ¬ is-inhabited B
                               → is-empty-subset B
 uninhabited-subsets-are-empty B ν x m = ν ∣ x , m ∣

complement :  {X : 𝓤 ̇ } → funext 𝓤 𝓤₀ → 𝓟 X → 𝓟 X
complement fe A = λ x → (x ∉ A) , (∉-is-prop fe A x)

⊆-is-prop' : funext 𝓤 𝓥
           → funext 𝓥 𝓥
           → {X : 𝓤 ̇ } (A B : 𝓟 {𝓥} X) → is-prop (A ⊆ B)
⊆-is-prop' fe fe' A B = Π-is-prop fe
                         (λ x → Π-is-prop fe'
                         (λ _ → ∈-is-prop B x))

⊆-is-prop : funext 𝓤 𝓤
          → {X : 𝓤 ̇ } (A B : 𝓟 X) → is-prop (A ⊆ B)
⊆-is-prop fe = ⊆-is-prop' fe fe

module PropositionalSubsetInclusionNotation (fe : Fun-Ext) where

 _⊆ₚ_ _⊇ₚ_ : {X : 𝓤 ̇ } → 𝓟 {𝓤} X → 𝓟 {𝓤} X → Ω 𝓤
 A ⊆ₚ B = (A ⊆ B) , ⊆-is-prop fe A B
 A ⊇ₚ B = (A ⊇ B) , ⊆-is-prop fe B A

∅-is-least' : {X : 𝓤 ̇ } (A : 𝓟 {𝓥} X) → ∅ {𝓤} {𝓥} ⊆ A
∅-is-least' _ x = 𝟘-induction

∅-is-least : {X : 𝓤 ̇ } (A : 𝓟 X) → ∅ {𝓤} {𝓤} ⊆ A
∅-is-least = ∅-is-least'

⊆-refl' : {X : 𝓤 ̇ } (A : 𝓟 {𝓥} X) → A ⊆ A
⊆-refl' A x = id

⊆-refl : {X : 𝓤 ̇ } (A : 𝓟 {𝓥} X) → A ⊆ A
⊆-refl = ⊆-refl'

⊆-trans' : {X : 𝓤 ̇ } (A B C : 𝓟 {𝓥} X) → A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans' A B C s t x a = t x (s x a)

⊆-trans : {X : 𝓤 ̇ } (A B C : 𝓟 {𝓥} X) → A ⊆ B → B ⊆ C → A ⊆ C
⊆-trans = ⊆-trans'

⊆-refl-consequence : {X : 𝓤 ̇ } (A B : 𝓟 {𝓥} X)
                   → A ＝ B → (A ⊆ B) × (B ⊆ A)

⊆-refl-consequence A A (refl) = ⊆-refl A , ⊆-refl A

subset-extensionality'' : propext 𝓥
                        → funext 𝓤 (𝓥 ⁺)
                        → funext 𝓥 𝓥
                        → {X : 𝓤 ̇ } {A B : 𝓟 {𝓥} X}
                        → A ⊆ B → B ⊆ A → A ＝ B

subset-extensionality'' {𝓥} {𝓤} pe fe fe' {X} {A} {B} h k = dfunext fe φ
 where
  φ : (x : X) → A x ＝ B x
  φ x = to-subtype-＝
           (λ _ → being-prop-is-prop fe')
           (pe (holds-is-prop (A x)) (holds-is-prop (B x))
               (h x) (k x))

subset-extensionality : propext 𝓤
                      → funext 𝓤 (𝓤 ⁺)
                      → {X : 𝓤 ̇ } {A B : 𝓟 X}
                      → A ⊆ B → B ⊆ A → A ＝ B

subset-extensionality {𝓤} pe fe = subset-extensionality'' pe fe (lower-funext 𝓤 (𝓤 ⁺) fe)

subset-extensionality' : Univalence
                       → {X : 𝓤 ̇ } {A B : 𝓟 X}
                       → A ⊆ B → B ⊆ A → A ＝ B

subset-extensionality' {𝓤} ua = subset-extensionality
                                 (univalence-gives-propext (ua 𝓤))
                                 (univalence-gives-funext' 𝓤 (𝓤 ⁺) (ua 𝓤) (ua (𝓤 ⁺)))
\end{code}

Tom de Jong, 24 January 2022
(Based on code from FreeJoinSemiLattice.lagda written 18-24 December 2020.)

Notation for the "total space" of a subset.

\begin{code}

module _
        {X : 𝓤 ̇ }
       where

 𝕋 : 𝓟 {𝓥} X → 𝓤 ⊔ 𝓥 ̇
 𝕋 A = Σ x ꞉ X , x ∈ A

 𝕋-to-carrier : (A : 𝓟 {𝓥} X) → 𝕋 A → X
 𝕋-to-carrier A = pr₁

 𝕋-to-membership : (A : 𝓟 {𝓥} X) → (t : 𝕋 A) → 𝕋-to-carrier A t ∈ A
 𝕋-to-membership A = pr₂

\end{code}

Added by Martin Escardo 23rd June 2025.

\begin{code}

 open import UF.Embeddings
 open import UF.Equiv

 module _ (K : 𝓟 {𝓥} X) where

  𝕋-to-carrier-is-embedding : is-embedding (𝕋-to-carrier K)
  𝕋-to-carrier-is-embedding = pr₁-is-embedding (∈-is-prop K)

  from-𝕋-fiber : (x : X) → fiber (𝕋-to-carrier K) x → x ∈ K
  from-𝕋-fiber x ((x , m) , refl) = m

  to-𝕋-fiber : (x : X) → x ∈ K → fiber (𝕋-to-carrier K) x
  to-𝕋-fiber x m = ((x , m) , refl)

  𝕋-fiber : (x : X) → fiber (𝕋-to-carrier K) x ≃ (x ∈ K)
  𝕋-fiber x = qinveq (from-𝕋-fiber x)
               (to-𝕋-fiber x , (λ {((x , m) , refl) → refl}) , (λ m → refl))

\end{code}

End of 23rd June addition and continuing with Tom de Jong older
additions.

We use a named module when defining singleton subsets, so that we can write
❴ x ❵ without having to keep supplying the proof that the ambient type is a set.

\begin{code}

module singleton-subsets
        {X : 𝓤 ̇ }
        (X-is-set : is-set X)
       where

 ❴_❵ : X → 𝓟 X
 ❴ x ❵ = λ y → ((x ＝ y) , X-is-set)

 ∈-❴❵ : {x : X} → x ∈ ❴ x ❵
 ∈-❴❵ {x} = refl

 ❴❵-subset-characterization : {x : X} (A : 𝓟 {𝓥} X) → x ∈ A ↔ ❴ x ❵ ⊆ A
 ❴❵-subset-characterization {𝓥} {x} A = ⦅⇒⦆ , ⦅⇐⦆
  where
   ⦅⇒⦆ : x ∈ A → ❴ x ❵ ⊆ A
   ⦅⇒⦆ a _ refl = a
   ⦅⇐⦆ : ❴ x ❵ ⊆ A → x ∈ A
   ⦅⇐⦆ s = s x ∈-❴❵

 ❴❵-is-singleton : {x : X} → is-singleton (𝕋 ❴ x ❵)
 ❴❵-is-singleton {x} = singleton-types-are-singletons x

\end{code}

Next, we consider binary intersections and unions in the powerset. For the
latter, we need propositional truncations.

\begin{code}

module _
        {X : 𝓤 ̇ }
       where

 _∩_ : 𝓟 {𝓥} X → 𝓟 {𝓥} X → 𝓟 {𝓥} X
 (A ∩ B) x = (x ∈ A × x ∈ B) , ×-is-prop (∈-is-prop A x) (∈-is-prop B x)

 ∩-is-lowerbound₁ : (A B : 𝓟 {𝓥} X) → (A ∩ B) ⊆ A
 ∩-is-lowerbound₁ A B x = pr₁

 ∩-is-lowerbound₂ : (A B : 𝓟 {𝓥} X) → (A ∩ B) ⊆ B
 ∩-is-lowerbound₂ A B x = pr₂

 ∩-is-upperbound-of-lowerbounds : (A B C : 𝓟 {𝓥} X)
                                → C ⊆ A → C ⊆ B → C ⊆ (A ∩ B)
 ∩-is-upperbound-of-lowerbounds A B C s t x c = (s x c , t x c)

module binary-unions-of-subsets
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt

 module _
         {X : 𝓤 ̇ }
        where

  _∪_ : 𝓟 {𝓥} X → 𝓟 {𝓥} X → 𝓟 {𝓥} X
  (A ∪ B) x = ∥ x ∈ A + x ∈ B ∥ , ∥∥-is-prop

  ∪-is-upperbound₁ : (A B : 𝓟 {𝓥} X) → A ⊆ (A ∪ B)
  ∪-is-upperbound₁ A B x a = ∣ inl a ∣

  ∪-is-upperbound₂ : (A B : 𝓟 {𝓥} X) → B ⊆ (A ∪ B)
  ∪-is-upperbound₂ A B x b = ∣ inr b ∣

  ∪-is-lowerbound-of-upperbounds : (A B C : 𝓟 {𝓥} X)
                                 → A ⊆ C → B ⊆ C → (A ∪ B) ⊆ C
  ∪-is-lowerbound-of-upperbounds A B C s t x = ∥∥-rec (∈-is-prop C x) γ
    where
     γ : (x ∈ A + x ∈ B) → x ∈ C
     γ (inl a) = s x a
     γ (inr b) = t x b

  ∅-left-neutral-for-∪' : propext 𝓥
                        → funext 𝓤 (𝓥 ⁺)
                        → funext 𝓥 𝓥
                        → (A : 𝓟 {𝓥} X) → ∅ ∪ A ＝ A
  ∅-left-neutral-for-∪' pe fe fe' A =
   subset-extensionality'' pe fe fe' s (∪-is-upperbound₂ ∅ A)
    where
     s : (∅ ∪ A) ⊆ A
     s x = ∥∥-rec (∈-is-prop A x) γ
      where
       γ : x ∈ ∅ + x ∈ A → x ∈ A
       γ (inl p) = 𝟘-elim p
       γ (inr a) = a

  ∅-left-neutral-for-∪ : propext 𝓤
                       → funext 𝓤 (𝓤 ⁺)
                       → (A : 𝓟 X) → ∅ ∪ A ＝ A
  ∅-left-neutral-for-∪ pe fe =
   ∅-left-neutral-for-∪' pe fe (lower-funext 𝓤 (𝓤 ⁺) fe)

  ∅-right-neutral-for-∪' : propext 𝓥
                         → funext 𝓤 (𝓥 ⁺)
                         → funext 𝓥 𝓥
                         → (A : 𝓟 {𝓥} X) → A ＝ A ∪ ∅
  ∅-right-neutral-for-∪' pe fe fe' A =
   subset-extensionality'' pe fe fe' (∪-is-upperbound₁ A ∅) s
    where
     s : (A ∪ ∅) ⊆ A
     s x = ∥∥-rec (∈-is-prop A x) γ
      where
       γ : x ∈ A + x ∈ ∅ → x ∈ A
       γ (inl a) = a
       γ (inr p) = 𝟘-elim p

  ∅-right-neutral-for-∪ : propext 𝓤
                        → funext 𝓤 (𝓤 ⁺)
                        → (A : 𝓟 X) → A ＝ A ∪ ∅
  ∅-right-neutral-for-∪ pe fe =
   ∅-right-neutral-for-∪' pe fe (lower-funext 𝓤 (𝓤 ⁺) fe)

  ∪-assoc' : propext 𝓥
           → funext 𝓤 (𝓥 ⁺)
           → funext 𝓥 𝓥
           → associative {𝓥 ⁺ ⊔ 𝓤} {𝓟 {𝓥} X} (_∪_)
  ∪-assoc' pe fe fe' A B C = subset-extensionality'' pe fe fe' s t
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

  ∪-assoc : propext 𝓤
          → funext 𝓤 (𝓤 ⁺)
          → associative {𝓤 ⁺} {𝓟 X} (_∪_)
  ∪-assoc pe fe = ∪-assoc' pe fe (lower-funext 𝓤 (𝓤 ⁺) fe)

\end{code}

Again assuming propositional truncations, we can construct arbitrary suprema in
𝓟 (X : 𝓤) of families indexed by types in 𝓤.

\begin{code}

module unions-of-small-families
        (pt : propositional-truncations-exist)
        (𝓥 : Universe)
        (𝓣 : Universe)
        (X : 𝓤 ̇ )
        {I : 𝓥 ̇ }
       where

 open PropositionalTruncation pt

 ⋃  : (α : I → 𝓟 {𝓥 ⊔ 𝓣} X) → 𝓟 {𝓥 ⊔ 𝓣} X
 ⋃ α x = (∃ i ꞉ I , x ∈ α i) , ∃-is-prop

 ⋃-is-upperbound : (α : I → 𝓟 {𝓥 ⊔ 𝓣} X) (i : I)
                 → α i ⊆ ⋃ α
 ⋃-is-upperbound α i x a = ∣ i , a ∣

 ⋃-is-lowerbound-of-upperbounds : (α : I → 𝓟 {𝓥 ⊔ 𝓣} X) (A : 𝓟 {𝓥 ⊔ 𝓣} X)
                                → ((i : I) → α i ⊆ A)
                                → ⋃ α ⊆ A
 ⋃-is-lowerbound-of-upperbounds α A ub x u =
  ∥∥-rec (∈-is-prop A x) γ u
   where
    γ : (Σ i ꞉ I , x ∈ α i) → x ∈ A
    γ (i , a) = ub i x a

\end{code}

Fixities.

\begin{code}

infix  40 _∈ₚ_
infix  40 _∈_
infix  40 _∉_

\end{code}

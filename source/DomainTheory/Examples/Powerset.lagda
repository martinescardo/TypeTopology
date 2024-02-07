Tom de Jong, 25 January 2022

We consider the powerset of a set as a pointed dcpo. Given a set X : 𝓤, the
𝓥-valued subsets X → Ω 𝓥 are a pointed 𝓥-dcpo.

Taking 𝓥 to be equal to 𝓤 is more interesting as in this case we get a pointed
dcpo with a small compact basis (given by lists on X). In particular, the
powerset is algebraic and we characterize its compact elements as the Kuratowski
finite subsets.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan

open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Sets

module DomainTheory.Examples.Powerset
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        {X : 𝓤 ̇ }
        (X-is-set : is-set X)
       where

open import MLTT.List

open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Powerset
open import UF.Powerset-Fin pt
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.SubtypeClassifier-Properties

open import OrderedTypes.Poset fe

open binary-unions-of-subsets pt
open canonical-map-from-lists-to-subsets X-is-set
open PropositionalTruncation pt
open singleton-subsets X-is-set

module _
        (𝓥 : Universe)
       where

 open import DomainTheory.Basics.Dcpo pt fe 𝓥
 open import DomainTheory.Basics.Pointed pt fe 𝓥

 open unions-of-small-families pt 𝓥 𝓥 X

 generalized-𝓟-DCPO : DCPO {𝓥 ⁺ ⊔ 𝓤} {𝓤 ⊔ 𝓥}
 generalized-𝓟-DCPO = (X → Ω 𝓥) , _⊆_ ,
                      ( powersets-are-sets'' fe fe pe
                      , ⊆-is-prop' fe fe
                      , ⊆-refl'
                      , ⊆-trans'
                      , λ A B → subset-extensionality'' pe fe fe)
                      , dir-compl
  where
   dir-compl : is-directed-complete _⊆_
   dir-compl I α δ = ⋃ α , ⋃-is-upperbound α , ⋃-is-lowerbound-of-upperbounds α

 generalized-𝓟-DCPO⊥ : DCPO⊥ {𝓥 ⁺ ⊔ 𝓤} {𝓤 ⊔ 𝓥}
 generalized-𝓟-DCPO⊥ = (generalized-𝓟-DCPO , ∅ , ∅-is-least')

\end{code}

We now specialize to taking 𝓥 to be equal to 𝓤, the universe where X lives and
we prove that lists on X give a small compact basis for the powerset.

\begin{code}

open import DomainTheory.Basics.Dcpo pt fe 𝓤
open import DomainTheory.Basics.Miscelanea pt fe 𝓤
open import DomainTheory.Basics.Pointed pt fe 𝓤
open import DomainTheory.Basics.WayBelow pt fe 𝓤

open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓤
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓤

open unions-of-small-families pt 𝓤 𝓤 X

𝓟-DCPO : DCPO {𝓤 ⁺} {𝓤}
𝓟-DCPO = generalized-𝓟-DCPO 𝓤

𝓟-DCPO⊥ : DCPO⊥ {𝓤 ⁺} {𝓤}
𝓟-DCPO⊥ = generalized-𝓟-DCPO⊥ 𝓤

κ⁺ : (A : 𝓟 X) → (Σ l ꞉ List X , κ l ⊆ A) → 𝓟 X
κ⁺ A = κ ∘ pr₁

κ⁺-is-directed : (A : 𝓟 X) → is-Directed 𝓟-DCPO (κ⁺ A)
κ⁺-is-directed A = inh , semidir
 where
  inh : ∃ l ꞉ List X , κ l ⊆ A
  inh = ∣ [] , (∅-is-least A) ∣
  semidir : is-semidirected _⊆_ (κ⁺ A)
  semidir (l₁ , s₁) (l₂ , s₂) = ∣ ((l₁ ++ l₂) , s) , u₁ , u₂ ∣
   where
    e : κ (l₁ ++ l₂) ＝ κ l₁ ∪ κ l₂
    e = κ-of-concatenated-lists-is-union pe fe l₁ l₂
    u : (κ l₁ ∪ κ l₂) ⊆ κ (l₁ ++ l₂)
    u = ＝-to-⊒ 𝓟-DCPO e
    -- Unfortunately, using the ⊑⟨ 𝓟-DCPO ⟩-syntax here gives
    -- implicit arguments problems, so we use ⊆-trans instead.
    u₁ : κ l₁ ⊆ κ (l₁ ++ l₂)
    u₁ = ⊆-trans (κ l₁) (κ l₁ ∪ κ l₂) (κ (l₁ ++ l₂))
          (∪-is-upperbound₁ (κ l₁) (κ l₂)) u
    u₂ = ⊆-trans (κ l₂) (κ l₁ ∪ κ l₂) (κ (l₁ ++ l₂))
          (∪-is-upperbound₂ (κ l₁) (κ l₂)) u
    s : κ (l₁ ++ l₂) ⊆ A
    s = ⊆-trans (κ (l₁ ++ l₂)) (κ l₁ ∪ κ l₂) A ⦅1⦆ ⦅2⦆
     where
      ⦅1⦆ : κ (l₁ ++ l₂) ⊆ (κ l₁ ∪ κ l₂)
      ⦅1⦆ = ＝-to-⊑ 𝓟-DCPO e
      ⦅2⦆ : (κ l₁ ∪ κ l₂) ⊆ A
      ⦅2⦆ = ∪-is-lowerbound-of-upperbounds (κ l₁) (κ l₂) A s₁ s₂

κ⁺-sup : (A : 𝓟 X) → is-sup _⊆_ A (κ⁺ A)
κ⁺-sup A = ub , lb-of-ubs
 where
  ub : is-upperbound _⊆_ A (κ⁺ A)
  ub (l , l-subset-A) x x-in-l = l-subset-A x x-in-l
  lb-of-ubs : is-lowerbound-of-upperbounds _⊆_ A (κ⁺ A)
  lb-of-ubs B B-is-ub x x-in-A = B-is-ub ([ x ] , s) x (∪-is-upperbound₁ ❴ x ❵ ∅ x ∈-❴❵)
   where
    s : (❴ x ❵ ∪ ∅) ⊆ A
    s = ∪-is-lowerbound-of-upperbounds ❴ x ❵ ∅ A
         (lr-implication (❴❵-subset-characterization A) x-in-A)
         (∅-is-least A)

κ⁺-⋃-⊆ : (A : 𝓟 X) → ⋃ (κ⁺ A) ⊆ A
κ⁺-⋃-⊆ A = ⋃-is-lowerbound-of-upperbounds (κ⁺ A) A
        (sup-is-upperbound _⊆_ {_} {_} {A} {κ⁺ A} (κ⁺-sup A))

κ⁺-⋃-⊇ : (A : 𝓟 X) → ⋃ (κ⁺ A) ⊇ A
κ⁺-⋃-⊇ A = sup-is-lowerbound-of-upperbounds _⊆_ {_} {_} {A} {κ⁺ A}
            (κ⁺-sup A) (⋃ (κ⁺ A))
            (⋃-is-upperbound (κ⁺ A))

κ⁺-⋃-＝ : (A : 𝓟 X) → ⋃ (κ⁺ A) ＝ A
κ⁺-⋃-＝ A = subset-extensionality pe fe (κ⁺-⋃-⊆ A) (κ⁺-⋃-⊇ A)

Kuratowski-finite-subset-if-compact : (A : 𝓟 X)
                                    → is-compact 𝓟-DCPO A
                                    → is-Kuratowski-finite-subset A
Kuratowski-finite-subset-if-compact A c =
 Kuratowski-finite-subset-if-in-image-of-κ A γ
  where
   claim : ∃ l⁺ ꞉ (Σ l ꞉ List X , κ l ⊆ A) , A ⊆ κ⁺ A l⁺
   claim = c (domain (κ⁺ A)) (κ⁺ A) (κ⁺-is-directed A) (κ⁺-⋃-⊇ A)
   γ : A ∈image κ
   γ = ∥∥-functor h claim
    where
     h : (Σ l⁺ ꞉ (Σ l ꞉ List X , κ l ⊆ A) , A ⊆ κ⁺ A l⁺)
       → Σ l ꞉ List X , κ l ＝ A
     h ((l , s) , t) = (l , subset-extensionality pe fe s t)

∅-is-compact : is-compact 𝓟-DCPO ∅
∅-is-compact = ⊥-is-compact 𝓟-DCPO⊥

singletons-are-compact : (x : X) → is-compact 𝓟-DCPO ❴ x ❵
singletons-are-compact x I α δ l = ∥∥-functor h (l x ∈-❴❵)
 where
  h : (Σ i ꞉ I , x ∈ α i)
    → (Σ i ꞉ I , ❴ x ❵ ⊆ α i)
  h (i , m) = (i , lr-implication (❴❵-subset-characterization (α i)) m)

∪-is-compact : (A B : 𝓟 X)
             → is-compact 𝓟-DCPO A
             → is-compact 𝓟-DCPO B
             → is-compact 𝓟-DCPO (A ∪ B)
∪-is-compact A B =
 binary-join-is-compact 𝓟-DCPO {A} {B} {A ∪ B}
  (∪-is-upperbound₁ A B) (∪-is-upperbound₂ A B)
  (∪-is-lowerbound-of-upperbounds A B)

compact-if-Kuratowski-finite-subset : (A : 𝓟 X)
                                    → is-Kuratowski-finite-subset A
                                    → is-compact 𝓟-DCPO A
compact-if-Kuratowski-finite-subset A k = lemma (A , k)
 where
  Q : 𝓚 X → 𝓤 ⁺ ̇
  Q A = is-compact 𝓟-DCPO (pr₁ A)
  lemma : (A : 𝓚 X) → Q A
  lemma = Kuratowski-finite-subset-induction pe fe X X-is-set Q
           (λ A → being-compact-is-prop 𝓟-DCPO (pr₁ A))
           ∅-is-compact
           singletons-are-compact
           (λ A B → ∪-is-compact (pr₁ A) (pr₁ B))

κ-is-small-compact-basis : is-small-compact-basis 𝓟-DCPO κ
κ-is-small-compact-basis =
 record
  { basis-is-compact = λ l → compact-if-Kuratowski-finite-subset (κ l)
                            (κ-of-list-is-Kuratowski-finite-subset l)
  ; ⊑ᴮ-is-small      = λ A l → (κ l ⊆ A , ≃-refl (κ l ⊆ A))
  ; ↓ᴮ-is-directed   = κ⁺-is-directed
  ; ↓ᴮ-is-sup        = κ⁺-sup
  }

𝓟-has-specified-small-compact-basis : has-specified-small-compact-basis 𝓟-DCPO
𝓟-has-specified-small-compact-basis = (List X , κ , κ-is-small-compact-basis)

𝓟-structurally-algebraic : structurally-algebraic 𝓟-DCPO
𝓟-structurally-algebraic =
 structurally-algebraic-if-specified-small-compact-basis
  𝓟-DCPO 𝓟-has-specified-small-compact-basis

𝓟-is-algebraic-dcpo : is-algebraic-dcpo 𝓟-DCPO
𝓟-is-algebraic-dcpo = ∣ 𝓟-structurally-algebraic ∣

\end{code}

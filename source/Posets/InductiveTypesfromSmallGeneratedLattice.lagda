Ian Ray 01/09/2023.

We formalize Curi's notion of abstract inductive definition (CZF) within the
context of a sup-lattice L with small basis B (and q : B → L). An abstract
inductive defintion is a subset ϕ : B × L → Prop which can be thought of as a
'inference rule' concluding b from a. An inductive definition induces a
closure condition. More precisely, a subset S is closed under ϕ if for all
b : B and a : L such that (b , a) ∈ ϕ and ↓ᴮa is 'contained' in S then b ∈ S.
Interestingly, there is an intimate connection between the least-closed
subsets of some inductive definition ϕ and the least fixed point of a monotome
map related to ϕ in a precise way. In this file we will develop this
relationship and prove a predicative version of the least fixed point theorem.
This work follows the paper 'On Tarski's Fixed Point Theorem' by Giovanni Curi.
Fortunately, unlike in the realm of set theory, induction rules are first
class citizens in type theory. Using UF + HITs we can construct the least
closed subset, under an inductive definition ϕ, as a special quotient inductive
type (QIT). 

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.PropTrunc
open import UF.Retracts
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Size
open import UF.SmallnessProperties
open import UF.UniverseEmbedding

module Posets.InductiveTypesfromSmallGeneratedLattice
       (pt : propositional-truncations-exist)
       (fe : Fun-Ext)
       (fe' : FunExt)
       (pe : Prop-Ext)
        where

open import Locales.Frame pt fe hiding (⟨_⟩)
open import Slice.Family
open import UF.ImageAndSurjection pt

open AllCombinators pt fe

\end{code}

In the interest of self containment we open this file by defining a sup-lattice
as well as some boiler plater.

\begin{code}

module sup-lattice-def (𝓤 𝓦 𝓥 : Universe) where

 sup-lattice-data : 𝓤  ̇ → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓥 ⁺  ̇
 sup-lattice-data A = (A → A → Ω 𝓦) × (Fam 𝓥 A → A)
 
 is-sup-lattice : {A : 𝓤  ̇} → sup-lattice-data A → 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⁺  ̇  
 is-sup-lattice {A} (_≤_ , ⋁_) = is-partial-order A _≤_ × rest
  where
   open Joins _≤_
   rest : 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⁺  ̇
   rest = (U : Fam 𝓥 A) → ((⋁ U) is-lub-of U) holds

 sup-lattice-structure : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
 sup-lattice-structure A = Σ d ꞉ (sup-lattice-data A) , is-sup-lattice d

Sup-Lattice : (𝓤 𝓦 𝓥 : Universe) → (𝓤 ⊔ 𝓦 ⊔ 𝓥) ⁺  ̇
Sup-Lattice 𝓤 𝓦 𝓥 = Σ A ꞉ 𝓤  ̇ , sup-lattice-structure A
 where
  open sup-lattice-def 𝓤 𝓦 𝓥

⟨_⟩ : Sup-Lattice 𝓤 𝓦 𝓥 → 𝓤  ̇
⟨ (A , rest) ⟩ = A

order-of : (L : Sup-Lattice 𝓤 𝓦 𝓥) → (⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦)
order-of (A , (_≤_ , ⋁_) , rest) = _≤_

join-for : (L : Sup-Lattice 𝓤 𝓦 𝓥) → Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
join-for (A , (_≤_ , ⋁_) , rest) = ⋁_

is-partial-order-for : (L : Sup-Lattice 𝓤 𝓦 𝓥)
                     → is-partial-order ⟨ L ⟩ (order-of L)
is-partial-order-for (A , (_≤_ , ⋁_) , order , is-lub-of) = order

is-reflexive-for : (L : Sup-Lattice 𝓤 𝓦 𝓥) → is-reflexive (order-of L) holds
is-reflexive-for L = pr₁ (pr₁ (is-partial-order-for L))

is-antisymmetric-for : (L : Sup-Lattice 𝓤 𝓦 𝓥) → is-antisymmetric (order-of L) 
is-antisymmetric-for L = pr₂ (is-partial-order-for L)

is-transitive-for : (L : Sup-Lattice 𝓤 𝓦 𝓥) → is-transitive (order-of L) holds
is-transitive-for L = pr₂ (pr₁ (is-partial-order-for L))

is-lub-for : (L : Sup-Lattice 𝓤 𝓦 𝓥)
           → (U : Fam 𝓥 ⟨ L ⟩)
           → ((order-of L) Joins.is-lub-of join-for L U) U holds
is-lub-for (A , (_≤_ , ⋁_) , order , is-lub-of) = is-lub-of

is-an-upper-bound-for_of_ : (L : Sup-Lattice 𝓤 𝓦 𝓥)
                          → (U : Fam 𝓥 ⟨ L ⟩)
                          → ((order-of L) Joins.is-an-upper-bound-of
                                          join-for L U) U holds
is-an-upper-bound-for L of U = pr₁ (is-lub-for L U)

is-least-upper-bound-for_of_ : (L : Sup-Lattice 𝓤 𝓦 𝓥)
                             → (U : Fam 𝓥 ⟨ L ⟩)
                             → ((u' , _) : Joins.upper-bound (order-of L) U)
                             → (order-of L (join-for L U) u') holds
is-least-upper-bound-for L of U = pr₂ (is-lub-for L U)

\end{code}

We now define monotone endomaps on a sup-lattice. This is sufficient for our
work as we are studying fixed points.

\begin{code}

module monotone-endomaps {𝓤 𝓦 𝓥 : Universe} (L : Sup-Lattice 𝓤 𝓦 𝓥) where

 _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦
 _≤_ = order-of L

 _is-monotone : (f : ⟨ L ⟩ → ⟨ L ⟩) → 𝓤 ⊔ 𝓦  ̇
 f is-monotone = (x y : ⟨ L ⟩) → (x ≤ y) holds → (f x ≤ f y) holds

\end{code}

We now show that when one subset contains another the join of their total
spaces are ordered as expected. This result will be quite useful throughout
this file.

\begin{code}

module subsets-order-joins {𝓤 𝓦 𝓥 : Universe}
                           (L : Sup-Lattice 𝓤 𝓦 𝓥)
                           (A : 𝓥  ̇)
                           (m : A → ⟨ L ⟩)
                           where

 _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦
 x ≤ y = order-of L x y

 ⋁_ : Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
 ⋁_ = join-for L

 open Joins _≤_

 joins-preserve-containment : {P : 𝓟 {𝓥} A} {Q : 𝓟 {𝓥} A}
                            → (C : P ⊆ Q)
                            → ((⋁ (𝕋 P , m ∘ 𝕋-to-carrier P))
                             ≤ (⋁ (𝕋 Q , m ∘ 𝕋-to-carrier Q))) holds
 joins-preserve-containment {P} {Q} C =
   (is-least-upper-bound-for L of (𝕋 P , m ∘ 𝕋-to-carrier P))
    (⋁ (𝕋 Q , m ∘ 𝕋-to-carrier Q) ,
    λ (b , b-in-P)
      → (is-an-upper-bound-for L of (𝕋 Q , m ∘ 𝕋-to-carrier Q))
    (b , C b b-in-P))

\end{code}

We now show if a type is small and has a map to the carrier then it has a join.
This seems like strict requirement but as we will see it occurs often when
considering a lattice with a basis. 

\begin{code}

module small-types-have-joins {𝓤 𝓦 𝓥 𝓣 : Universe}
                              (L : Sup-Lattice 𝓤 𝓦 𝓥)
                              (T : 𝓣  ̇)
                              (m : T → ⟨ L ⟩)
                              (t : T is 𝓥 small)
                              where
 
 _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦
 _≤_ = order-of L

 ⋁_ : Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
 ⋁_ = join-for L

 T' : 𝓥  ̇
 T' = (resized T) t

 T'-≃-T : T' ≃ T
 T'-≃-T = resizing-condition t

 T'-to-T : T' → T
 T'-to-T = ⌜ T'-≃-T ⌝

 T'-to-T-is-equiv : is-equiv T'-to-T
 T'-to-T-is-equiv = ⌜ T'-≃-T ⌝-is-equiv

 T-to-T' : T → T'
 T-to-T' =  ⌜ T'-≃-T ⌝⁻¹

 T'-to-T-has-section : has-section T'-to-T
 T'-to-T-has-section = equivs-have-sections T'-to-T T'-to-T-is-equiv

 T'-to-T-is-section : is-section T'-to-T
 T'-to-T-is-section = equivs-are-sections T'-to-T T'-to-T-is-equiv

 section-T'-to-T : T'-to-T ∘ T-to-T' ∼ id
 section-T'-to-T = section-equation T'-to-T T'-to-T-has-section

 retraction-T'-to-T : T-to-T' ∘ T'-to-T ∼ id
 retraction-T'-to-T = inverses-are-retractions' T'-≃-T

 T'-inclusion : T' → ⟨ L ⟩
 T'-inclusion = m ∘ T'-to-T

 s : ⟨ L ⟩
 s = ⋁ (T' , T'-inclusion)

 open Joins _≤_

 sup-of-small-fam-is-lub : (s is-lub-of (T , m)) holds
 sup-of-small-fam-is-lub = (s-upper-bound , s-least-upper-bound)
  where
   s-upper-bound : (s is-an-upper-bound-of (T , m)) holds
   s-upper-bound t = t-≤-s
    where
     t-≤-s : (m t ≤ s) holds 
     t-≤-s = transport (λ z → (m z ≤ s) holds) (section-T'-to-T t)
                       ((is-an-upper-bound-for L of
                        (T' , T'-inclusion)) (T-to-T' t))
   s-least-upper-bound : ((u , _) : upper-bound (T , m)) → (s ≤ u) holds
   s-least-upper-bound (u , is-upbnd-T) = s-≤-u
    where
     s-≤-u : (s ≤ u) holds
     s-≤-u = pr₂ (is-lub-for L (T' , T'-inclusion))
                 ((u , λ i → is-upbnd-T (T'-to-T i)))

\end{code}

We now show that the joins of equivalent types can be identified. This will
prove useful in the coming section.

\begin{code}

module equivalent-families-have-same-join {𝓤 𝓦 𝓥 𝓣 𝓣' : Universe}
                                          (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                          (T : 𝓣  ̇)
                                          (T' : 𝓣'  ̇)
                                          (e : T' ≃ T)
                                          (m : T → ⟨ L ⟩)
                                          where

 _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦
 _≤_ = order-of L

 ⋁_ : Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
 ⋁_ = join-for L

 open Joins _≤_

 reindexing-along-equiv-＝-sup : (s s' : ⟨ L ⟩)
                               → (s is-lub-of (T , m)) holds
                               → (s' is-lub-of (T' , m ∘ ⌜ e ⌝ )) holds
                               → s ＝ s'
 reindexing-along-equiv-＝-sup s s' (is-upbnd , is-least-upbnd)
                        (is-upbnd' , is-least-upbnd') =
   is-antisymmetric-for L s-≤-s' s'-≤-s
  where
   s-≤-s' : (s ≤ s') holds
   s-≤-s' = is-least-upbnd (s' , λ t → transport (λ z → (z ≤ s') holds)
                           (＝₁ t) (is-upbnd' (⌜ e ⌝⁻¹ t)))
    where
     ＝₁ : (t : T) → m (⌜ e ⌝ (⌜ e ⌝⁻¹ t)) ＝ m t
     ＝₁ t = ap m (naive-inverses-are-sections ⌜ e ⌝ (⌜ e ⌝-is-equiv) t)
   s'-≤-s : (s' ≤ s) holds
   s'-≤-s = is-least-upbnd' (s , λ t' → is-upbnd (⌜ e ⌝ t'))

\end{code}

We can weaken the above result and simply require a surjection between families.

\begin{code}

module surjection-implies-equal-joins {𝓤 𝓦 𝓥 𝓣 𝓣' : Universe}
                                      (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                      (T : 𝓣  ̇)
                                      (T' : 𝓣'  ̇)
                                      (e : T' ↠ T)
                                      (m : T → ⟨ L ⟩)
                                      where

 _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦
 _≤_ = order-of L

 ⋁_ : Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
 ⋁_ = join-for L

 open Joins _≤_
 open PropositionalTruncation pt

 reindexing-along-surj-＝-sup : (s s' : ⟨ L ⟩)
                              → (s is-lub-of (T , m)) holds
                              → (s' is-lub-of (T' , m ∘ ⌞ e ⌟)) holds
                              → s ＝ s'
 reindexing-along-surj-＝-sup s s' (is-upbnd , is-least-upbnd)
                        (is-upbnd' , is-least-upbnd') =
   is-antisymmetric-for L s-≤-s' s'-≤-s
  where
   s-≤-s' : (s ≤ s') holds
   s-≤-s' = is-least-upbnd (s' , λ t → map₂ t (⌞⌟-is-surjection e t))
    where
     map₁ : (t : T) → Σ t' ꞉ T' , ⌞ e ⌟ t' ＝ t → (m t ≤ s') holds
     map₁ t (t' , path) = transport (λ z → (m z ≤ s') holds) path (is-upbnd' t')
     map₂ : (t : T) → (Ǝ t' ꞉ T' , ⌞ e ⌟ t' ＝ t) holds → (m t ≤ s') holds
     map₂ t = ∥∥-rec (holds-is-prop (m t ≤ s')) (map₁ t)
   s'-≤-s : (s' ≤ s) holds
   s'-≤-s = is-least-upbnd' (s , λ t' → is-upbnd (⌞ e ⌟ t'))

\end{code}

We now define a small basis for a sup-lattice. This consists of a type B in a
fixed universe and a map q from B to the carrier of the sup-lattice. In a sense
to be made precise the pair B and q generate the sup-lattice. This notion will
be integral in the development of the rest of our theory.

\begin{code}

module small-basis {𝓤 𝓦 𝓥 : Universe}
                   {B : 𝓥  ̇}
                   (L : Sup-Lattice 𝓤 𝓦 𝓥)
                   (q : B → ⟨ L ⟩)
                    where

 _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦
 _≤_ = order-of L

 ⋁_ : Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
 ⋁_ = join-for L

 open Joins _≤_

 ↓ᴮ : ⟨ L ⟩ → 𝓦 ⊔ 𝓥  ̇
 ↓ᴮ x = Σ b ꞉ B , (q b ≤ x) holds

 ↓ᴮ-to-base : (x : ⟨ L ⟩) → ↓ᴮ x → B
 ↓ᴮ-to-base x = pr₁

 ↓ᴮ-inclusion : (x : ⟨ L ⟩) → ↓ᴮ x → ⟨ L ⟩
 ↓ᴮ-inclusion x = q ∘ ↓ᴮ-to-base x

 is-small-basis : 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⁺  ̇
 is-small-basis = (x : ⟨ L ⟩)
                 → ((b : B) → ((q b ≤ x) holds) is 𝓥 small) ×
                   ((x is-lub-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds)

 module small-basis-facts (h : is-small-basis) where

  ≤-is-small : (x : ⟨ L ⟩) (b : B) → ((q b ≤ x) holds) is 𝓥 small
  ≤-is-small x b = pr₁ (h x) b

  is-sup-↓ : (x : ⟨ L ⟩) → (x is-lub-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds
  is-sup-↓ x = pr₂ (h x)

  is-upper-bound-↓ : (x : ⟨ L ⟩)
                   → (x is-an-upper-bound-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds
  is-upper-bound-↓ x = pr₁ (is-sup-↓ x)

  is-least-upper-bound-↓ : (x : ⟨ L ⟩)
                         → ((u' , _) : upper-bound (↓ᴮ x , ↓ᴮ-inclusion x))
                         → (x ≤ u') holds
  is-least-upper-bound-↓ x = pr₂ (is-sup-↓ x)

  _≤ᴮ_ : (b : B) → (x : ⟨ L ⟩) → 𝓥  ̇
  b ≤ᴮ x = (resized ((q b ≤ x) holds)) (≤-is-small x b)

  _≤ᴮ_-≃-_≤_ : {b : B} {x : ⟨ L ⟩} → (b ≤ᴮ x) ≃ ((q b) ≤ x) holds
  _≤ᴮ_-≃-_≤_ {b} {x} = (resizing-condition) (≤-is-small x b)

  _≤ᴮ_-to-_≤_ : {b : B} {x : ⟨ L ⟩} → (b ≤ᴮ x) → ((q b) ≤ x) holds
  _≤ᴮ_-to-_≤_ = ⌜ _≤ᴮ_-≃-_≤_ ⌝

  _≤_-to-_≤ᴮ_ : {b : B} {x : ⟨ L ⟩} → ((q b) ≤ x) holds → (b ≤ᴮ x)
  _≤_-to-_≤ᴮ_ = ⌜ _≤ᴮ_-≃-_≤_ ⌝⁻¹

  _≤ᴮ_-is-prop-valued : {b : B} {x : ⟨ L ⟩} → is-prop (b ≤ᴮ x)
  _≤ᴮ_-is-prop-valued {b} {x} =
   equiv-to-prop _≤ᴮ_-≃-_≤_ (holds-is-prop ((q b) ≤ x))

  small-↓ᴮ : ⟨ L ⟩ → 𝓥  ̇
  small-↓ᴮ x = Σ b ꞉ B , b ≤ᴮ x

  small-↓ᴮ-inclusion : (x : ⟨ L ⟩) → small-↓ᴮ x → ⟨ L ⟩
  small-↓ᴮ-inclusion x = q ∘ pr₁

  small-↓ᴮ-≃-↓ᴮ : {x : ⟨ L ⟩} → small-↓ᴮ x ≃ ↓ᴮ x
  small-↓ᴮ-≃-↓ᴮ {x} = Σ-cong' P Q e
   where
    P : B → 𝓥  ̇
    P b = b ≤ᴮ x
    Q : B → 𝓦  ̇
    Q b = ((q b) ≤ x) holds
    e : (b : B) →  b ≤ᴮ x ≃ ((q b) ≤ x) holds
    e b = _≤ᴮ_-≃-_≤_ {b} {x}

  ↓ᴮ-is-small : {x : ⟨ L ⟩} → ↓ᴮ x is 𝓥 small
  ↓ᴮ-is-small {x} = (small-↓ᴮ x , small-↓ᴮ-≃-↓ᴮ {x})

  is-sup'ᴮ : (x : ⟨ L ⟩) → x ＝ ⋁ (small-↓ᴮ x , small-↓ᴮ-inclusion x)
  is-sup'ᴮ x = reindexing-along-equiv-＝-sup
               x
               (⋁ (small-↓ᴮ x , small-↓ᴮ-inclusion x))
               (is-sup-↓ x)
               (is-lub-for L ((small-↓ᴮ x , small-↓ᴮ-inclusion x)))
   where
    open equivalent-families-have-same-join L (↓ᴮ x)
                                              (small-↓ᴮ x)
                                              small-↓ᴮ-≃-↓ᴮ
                                              (↓ᴮ-inclusion x)
                                              hiding (⋁_)

  is-supᴮ : (x : ⟨ L ⟩)
          → (x is-lub-of (small-↓ᴮ x , small-↓ᴮ-inclusion x)) holds
  is-supᴮ x =
    transport (λ z → (z is-lub-of (small-↓ᴮ x , small-↓ᴮ-inclusion x)) holds)
              (is-sup'ᴮ x ⁻¹)
              (is-lub-for L ((small-↓ᴮ x , small-↓ᴮ-inclusion x)))

  is-upper-boundᴮ : (x : ⟨ L ⟩)
                  → (x is-an-upper-bound-of
                       (small-↓ᴮ x , small-↓ᴮ-inclusion x)) holds
  is-upper-boundᴮ x = pr₁ (is-supᴮ x)

  is-least-upper-boundᴮ : (x : ⟨ L ⟩)
                        → ((u' , _) : upper-bound
                                      (small-↓ᴮ x , small-↓ᴮ-inclusion x))
                        → (x ≤ u') holds
  is-least-upper-boundᴮ x = pr₂ (is-supᴮ x)

\end{code}

Now we construct the least closed subset of an inductive definition as a QIT.
Since HITs are not native in Agda we will instead assume the existence of such
a type as well as its induction principle. Technically speaking we are going
to use record types to package the contents of this HIT. See below:
  record inductively-generated-subset-exists

Notice that the QIT has two constructors which representing the closure
conditions we wish to impose on subsets. The c-cl constructor says:
for any subset contained in the least closed subset, elements in the downset of
its join are in the least closed subset as well. The ϕ-cl constructor says:
if for any a : L and b : B with (b , a) ∈ ϕ and ↓ᴮ a 'contained' in the least
closed subset then b is in the least closed subset.

We also derive the initiality of the least closed subset from the postulated
induction principle. Initiality is closely related to the 'least' part of
our least fixed point theorem.

\begin{code}

module inductive-definitions {𝓤 𝓦 𝓥 : Universe}
                             {B : 𝓥  ̇}
                             (L : Sup-Lattice 𝓤 𝓦 𝓥)
                             (q : B → ⟨ L ⟩)
                              where

 open small-basis L q
 open Joins _≤_

 module ind-from-small-basis-facts (h : is-small-basis) where

  open small-basis-facts h

  record inductively-generated-subset-exists (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)): 𝓤ω
   where
   constructor
    inductively-generated-subset

   field
    Ind : B → 𝓤 ⊔ 𝓥 ⁺  ̇
    Ind-trunc : (b : B) → is-prop (Ind b)
    c-closed : (U : 𝓟 {𝓥} B)
             → ((b : B) → (b ∈ U → Ind b))
             → (b : B) → b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))
             → Ind b
    ϕ-closed : (a : ⟨ L ⟩)
             → (b : B)
             → (b , a) ∈ ϕ
             → ((b' : B) → (b' ≤ᴮ a → Ind b'))
             → Ind b
    Ind-induction : (P : (b : B) → 𝓟 {𝓣} (Ind b))
                  → ((U : 𝓟 {𝓥} B) → (f : (x : B) → (x ∈ U → Ind x))
                   → ((x : B) → (u : x ∈ U) → f x u ∈ P x)
                   → (b : B)
                   → (g : (b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))))
                   → c-closed U f b g ∈ P b)
                  → ((a : ⟨ L ⟩)
                   → (b : B)
                   → (p : (b , a) ∈ ϕ)
                   → (f : (x : B) → (x ≤ᴮ a → Ind x))
                   → ((x : B) → (o : x ≤ᴮ a) → f x o ∈ P x)
                   → ϕ-closed a b p f ∈ P b)
                  → (b : B) → (i : Ind b) → i ∈ P b

  module trunc-ind-def (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                       (ind-e : inductively-generated-subset-exists ϕ)
                        where

   open inductively-generated-subset-exists ind-e

   𝓘nd : 𝓟 {𝓤 ⊔ 𝓥 ⁺} B
   𝓘nd b = (Ind b , Ind-trunc b)

   𝓘nd-is-c-closed : (U : 𝓟 {𝓥} B)
                   → (U ⊆ 𝓘nd)
                   → (b : B) → b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))
                   → b ∈ 𝓘nd
   𝓘nd-is-c-closed = c-closed

   𝓘nd-is-ϕ-closed : (a : ⟨ L ⟩)
                   → (b : B)
                   → (b , a) ∈ ϕ
                   → ((b' : B) → (b' ≤ᴮ a → b' ∈ 𝓘nd))
                   → b ∈ 𝓘nd
   𝓘nd-is-ϕ-closed = ϕ-closed

   𝓘nd-induction : (P : (b : B) → 𝓟 {𝓣} (b ∈ 𝓘nd))
                 → ((U : 𝓟 {𝓥} B) → (f : U ⊆ 𝓘nd)
                  → ((x : B) → (u : x ∈ U) → f x u ∈ P x)
                  → (b : B) → (g : (b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))))
                  → c-closed U f b g ∈ P b)
                 → ((a : ⟨ L ⟩)
                  → (b : B)
                  → (p : (b , a) ∈ ϕ)
                  → (f : (x : B) → (x ≤ᴮ a → x ∈ 𝓘nd))
                  → ((x : B) → (o : x ≤ᴮ a) → f x o ∈ P x)
                  → ϕ-closed a b p f ∈ P b)
                 → (b : B) → (i : b ∈ 𝓘nd) → i ∈ P b
   𝓘nd-induction = Ind-induction

   𝓘nd-recursion : (P : 𝓟 {𝓣} B)
                 → ((U : 𝓟 {𝓥} B)
                  → (U ⊆ 𝓘nd)
                  → (U ⊆ P)
                  → (b : B) → (b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U)))
                  → b ∈ P)
                 → ((a : ⟨ L ⟩)
                  → (b : B)
                  → (b , a) ∈ ϕ
                  → ((x : B) → (x ≤ᴮ a → x ∈ 𝓘nd))
                  → ((x : B) → (x ≤ᴮ a → x ∈ P))
                  → b ∈ P)
                 → 𝓘nd ⊆ P
   𝓘nd-recursion P = 𝓘nd-induction λ b → (λ _ → P b)

   𝓘nd-is-initial : (P : 𝓟 {𝓣} B)
                  → ((U : 𝓟 {𝓥} B)
                   → (U ⊆ P)
                   → ((b : B) → (b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U)))
                   → b ∈ P))
                  → ((a : ⟨ L ⟩)
                   → (b : B)
                   → (b , a) ∈ ϕ
                   → ((b' : B) → (b' ≤ᴮ a → b' ∈ P)) → b ∈ P)
                  → 𝓘nd ⊆ P
   𝓘nd-is-initial {𝓣} P IH₁ IH₂ b b-in-𝓘nd = 𝓘nd-recursion P R S b b-in-𝓘nd
    where
     R : (U : 𝓟 {𝓥} B)
       → U ⊆ 𝓘nd
       → U ⊆ P
       → (x : B) → x ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))
       →  x ∈ P
     R U C₁ C₂ x o = IH₁ U C₂ x o
     S : (a : ⟨ L ⟩)
       → (x : B)
       → (x , a) ∈ ϕ
       → ((z : B) → z ≤ᴮ a → z ∈ 𝓘nd)
       → ((z : B) → z ≤ᴮ a → z ∈ P)
       → x ∈ P
     S a x p f g = IH₂ a x p g

\end{code}

We now consider a restricted class of inductive definitions which we will call
local. Then we define an operator parameterized by local inductive definitions
and prove that it is monotone. Finally, we show that any monotone endo map on
the sup-lattice corresponds to a monotone operator and local inductive
definition. This result plays an essential role in showing the least fixed
point theorem.

\begin{code}

module local-inductive-definitions {𝓤 𝓦 𝓥 : Universe}
                                   {B : 𝓥  ̇}
                                   (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                   (q : B → ⟨ L ⟩)
                                    where

 open small-basis L q
 open Joins _≤_
 open inductive-definitions L q 

 module local-from-small-basis-facts (h : is-small-basis) where

  open PropositionalTruncation pt
  open small-basis-facts h

  S : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → (a : ⟨ L ⟩) → 𝓤 ⊔ 𝓦 ⊔ 𝓥  ̇
  S ϕ a = Σ b ꞉ B , (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds

  S-to-base : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → (a : ⟨ L ⟩) → S ϕ a → B
  S-to-base ϕ a = pr₁

  S-monotonicity-lemma : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                       → (x y : ⟨ L ⟩)
                       → (x ≤ y) holds
                       → S ϕ x
                       → S ϕ y
  S-monotonicity-lemma ϕ x y o = f
   where
    f : S ϕ x → S ϕ y
    f (b , c) = (b , g c)
     where
      g : (Ǝ a' ꞉ ⟨ L ⟩ , ((b , a') ∈ ϕ) × ((a' ≤ x) holds)) holds
        → (Ǝ a' ꞉ ⟨ L ⟩ , ((b , a') ∈ ϕ) × ((a' ≤ y) holds)) holds
      g = ∥∥-rec ∥∥-is-prop g'
       where
        g' : Σ a' ꞉ ⟨ L ⟩ , ((b , a') ∈ ϕ) × ((a' ≤ x) holds)
           → (Ǝ a' ꞉ ⟨ L ⟩ , ((b , a') ∈ ϕ) × ((a' ≤ y) holds)) holds
        g' (a' , p , r) = ∣ (a' , p , is-transitive-for L a' x y r o) ∣

  S-has-sup-implies-monotone : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                             → (x y s s' : ⟨ L ⟩)
                             → (x ≤ y) holds
                             → (s is-lub-of (S ϕ x , q ∘ S-to-base ϕ x)) holds
                             → (s' is-lub-of (S ϕ y , q ∘ S-to-base ϕ y)) holds
                             → (s ≤ s') holds
  S-has-sup-implies-monotone ϕ x y s s' o
                             (is-upbnd , is-least-upbnd)
                             (is-upbnd' , is-least-upbnd') =
     is-least-upbnd ((s' , f))
   where
    f : (s' is-an-upper-bound-of (S ϕ x , q ∘ S-to-base ϕ x)) holds
    f (b , e) = is-upbnd' (S-monotonicity-lemma ϕ x y o ((b , e)))
        
  _is-local : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
  ϕ is-local = (a : ⟨ L ⟩) → S ϕ a is 𝓥 small

  module _ (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) (i : ϕ is-local) where
   
   S' : (a : ⟨ L ⟩) → 𝓥  ̇
   S' a = resized (S ϕ a) (i a)

   S'-≃-S : (a : ⟨ L ⟩) → S' a ≃ S ϕ a
   S'-≃-S a  = resizing-condition (i a)

   S'-to-S : (a : ⟨ L ⟩) → S' a → S ϕ a
   S'-to-S a = ⌜ S'-≃-S a ⌝

   S-to-S' : (a : ⟨ L ⟩) → S ϕ a → S' a 
   S-to-S' a = ⌜ S'-≃-S a ⌝⁻¹

   S'-monotone-ish : (x y : ⟨ L ⟩)
                   → (x ≤ y) holds
                   → S' x
                   → S' y
   S'-monotone-ish x y o =
     S-to-S' y ∘ S-monotonicity-lemma ϕ x y o ∘ S'-to-S x

   Γ : ⟨ L ⟩ → ⟨ L ⟩
   Γ a = ⋁ (S' a , q ∘ pr₁ ∘ S'-to-S a)

   open monotone-endomaps L hiding (_≤_)

   Γ-is-monotone : Γ is-monotone
   Γ-is-monotone x y o = S-has-sup-implies-monotone ϕ x y (Γ x) (Γ y) o
                                                    Γ-x-is-sup Γ-y-is-sup
    where
     Γ-x-is-sup : (Γ x is-lub-of (S ϕ x , q ∘ S-to-base ϕ x)) holds
     Γ-x-is-sup = sup-of-small-fam-is-lub
      where
       open small-types-have-joins L (S ϕ x) (q ∘ S-to-base ϕ x) (i x)       
     Γ-y-is-sup : (Γ y is-lub-of (S ϕ y , q ∘ S-to-base ϕ y)) holds
     Γ-y-is-sup = sup-of-small-fam-is-lub
      where
       open small-types-have-joins L (S ϕ y) (q ∘ S-to-base ϕ y) (i y)

  open monotone-endomaps L hiding (_≤_)

  mono-map-give-local-ind-def : (f : ⟨ L ⟩ → ⟨ L ⟩)
                              → f is-monotone
                              → Σ ϕ ꞉ 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩) ,
                                Σ i ꞉ (ϕ is-local) ,
                                ((x : ⟨ L ⟩) → (Γ ϕ i) x ＝ f x)
  mono-map-give-local-ind-def f f-mono = (ϕ , i , H)
   where
    ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)
    ϕ (b , a) = (Lift 𝓤 (b ≤ᴮ f a) ,
                 equiv-to-prop (Lift-≃ 𝓤 (b ≤ᴮ f a)) _≤ᴮ_-is-prop-valued )
    equiv-1 : (a : ⟨ L ⟩) → small-↓ᴮ (f a) ≃ S ϕ a
    equiv-1 a = Σ-cong' (λ z → z ≤ᴮ f a)
                        ((λ z → (Ǝ a' ꞉ ⟨ L ⟩ ,
                         (z , a') ∈ ϕ × (a' ≤ a) holds) holds)) equiv-2
     where
      equiv-2 : (z : B)
              → (z ≤ᴮ f a) ≃ (Ǝ a' ꞉ ⟨ L ⟩ ,
                             (z , a') ∈ ϕ × (a' ≤ a) holds) holds
      equiv-2 z = ⌜ prop-≃-≃-↔ fe _≤ᴮ_-is-prop-valued ∥∥-is-prop ⌝⁻¹
                  (map-1 , map-2)
       where
        map-1 : z ≤ᴮ f a → (Ǝ a' ꞉ ⟨ L ⟩ , (z , a') ∈ ϕ × (a' ≤ a) holds) holds
        map-1 o = ∣ (a , ⌜ ≃-Lift 𝓤 (z ≤ᴮ f a) ⌝ o , is-reflexive-for L a) ∣
        map-2 : (Ǝ a' ꞉ ⟨ L ⟩ , (z , a') ∈ ϕ × (a' ≤ a) holds) holds → z ≤ᴮ f a
        map-2 = ∥∥-rec _≤ᴮ_-is-prop-valued map-3
         where
          map-3 : Σ a' ꞉ ⟨ L ⟩ , (z , a') ∈ ϕ × (a' ≤ a) holds → z ≤ᴮ f a
          map-3 (a' , o , r) =
             _≤_-to-_≤ᴮ_ (is-transitive-for L (q z) (f a') (f a)
                                              (_≤ᴮ_-to-_≤_
                                                (⌜ ≃-Lift 𝓤 (z ≤ᴮ f a') ⌝⁻¹ o))
                                              (f-mono a' a r))
    i : ϕ is-local 
    i a = (small-↓ᴮ (f a) , equiv-1 a)
    G : (x : ⟨ L ⟩) → (f x is-lub-of (S ϕ x , q ∘ S-to-base ϕ x)) holds 
    G x = (f-is-upbnd , f-is-least)
     where
      f-is-upbnd : (f x is-an-upper-bound-of (S ϕ x , q ∘ S-to-base ϕ x)) holds
      f-is-upbnd (b , e) = map-4 e
       where
        map-4 : (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ x) holds) holds
              → (q b ≤ f x) holds
        map-4 = ∥∥-rec (holds-is-prop (q b ≤ f x)) map-5
         where
          map-5 : Σ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ x) holds
                → (q b ≤ f x) holds
          map-5 (a' , o , r) = is-transitive-for L (q b) (f a') (f x)
                                (_≤ᴮ_-to-_≤_ (⌜ ≃-Lift 𝓤 (b ≤ᴮ f a') ⌝⁻¹ o))
                                (f-mono a' x r)
      f-is-least : ((u , _) : upper-bound (S ϕ x , q ∘ S-to-base ϕ x))
                 → (f x ≤ u) holds
      f-is-least (u , is-upbnd) = (is-least-upper-boundᴮ (f x))
                                  (u , λ z → is-upbnd (⌜ equiv-1 x ⌝ z))
    H : (x : ⟨ L ⟩) → (Γ ϕ i) x ＝ f x
    H x = reindexing-along-equiv-＝-sup ((Γ ϕ i) x)
                                        (f x)
                                        sup-of-small-fam-is-lub
                                        (G x)
     where
      open equivalent-families-have-same-join L (S ϕ x) (S ϕ x)
                                              (id , id-is-equiv (S ϕ x))
                                              (q ∘ S-to-base ϕ x)
      open small-types-have-joins L (S ϕ x) (q ∘ S-to-base ϕ x) (i x)

  ind-def-from-mono-map : (f : ⟨ L ⟩ → ⟨ L ⟩)
                        → f is-monotone
                        → 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)
  ind-def-from-mono-map f f-mono = pr₁ (mono-map-give-local-ind-def f f-mono)

  local-from-mono-map : (f : ⟨ L ⟩ → ⟨ L ⟩)
                      → (f-mono : f is-monotone)
                      → (ind-def-from-mono-map f f-mono) is-local
  local-from-mono-map f f-mono =
    pr₁ (pr₂ (mono-map-give-local-ind-def f f-mono))

  f-＝-Γ-from-mono-map : (f : ⟨ L ⟩ → ⟨ L ⟩)
                       → (f-mono : f is-monotone)
                       → (x : ⟨ L ⟩)
                       → (Γ (ind-def-from-mono-map f f-mono)
                            (local-from-mono-map f f-mono)) x ＝ f x
  f-＝-Γ-from-mono-map f f-mono =
    pr₂ (pr₂ (mono-map-give-local-ind-def f f-mono))

\end{code}

We now spell out a correspondence between small 'closed' subsets and
deflationary points in our suo lattice. This will allow us to show that
monotone operators have a least fixed point under certain smallness assumpions.

\begin{code}

module correspondance-small-ϕ-closed-types-def-points {𝓤 𝓦 𝓥 : Universe}
                                                      {B : 𝓥  ̇}
                                                      (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                                      (q : B → ⟨ L ⟩)
                                                       where

 open small-basis L q
 open Joins _≤_
 open inductive-definitions L q
 open local-inductive-definitions L q

 module correspondance-from-small-basis-facts (h : is-small-basis) where

  open PropositionalTruncation pt
  open small-basis-facts h
  open ind-from-small-basis-facts h
  open local-from-small-basis-facts h

  module correspondance-from-locally-small-ϕ (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                                             (i : ϕ is-local)
                                              where

   _is-small-ϕ-closed-subset : (P : 𝓟 {𝓥} B) → 𝓤 ⊔ (𝓥 ⁺)  ̇
   P is-small-ϕ-closed-subset = ((U : 𝓟 {𝓥} B)
                               → (U ⊆ P)
                               → ((b : B)
                               → b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))
                               → b ∈ P))
                              × ((a : ⟨ L ⟩)
                               → (b : B)
                               → (b , a) ∈ ϕ
                               → ((b' : B) → (b' ≤ᴮ a → b' ∈ P))
                               → b ∈ P)

   is-small-ϕ-closed-subset-is-predicate : (P : 𝓟 {𝓥} B)
                                         → is-prop (P is-small-ϕ-closed-subset)
   is-small-ϕ-closed-subset-is-predicate P =
     ×-is-prop (Π-is-prop fe λ U
                → Π-is-prop fe (λ C
                 → Π-is-prop fe (λ b
                  → Π-is-prop fe (λ f
                   → holds-is-prop (P b)))))
               (Π-is-prop fe (λ a
                → Π-is-prop fe (λ b
                 → Π-is-prop fe (λ p
                  → Π-is-prop fe (λ f
                   → holds-is-prop (P b))))))

   small-ϕ-closed-subsets : 𝓤 ⊔ (𝓥 ⁺)  ̇
   small-ϕ-closed-subsets =  Σ P ꞉ 𝓟 {𝓥} B , P is-small-ϕ-closed-subset

   subset-of-small-ϕ-closed-subset : small-ϕ-closed-subsets → 𝓟 {𝓥} B
   subset-of-small-ϕ-closed-subset (P , c-clsd , ϕ-clsd) = P

   c-closed-of-small-ϕ-closed-subset : (X : small-ϕ-closed-subsets)
                                     → ((U : 𝓟 {𝓥} B)
                                     → U ⊆ subset-of-small-ϕ-closed-subset X
                                     → ((b : B)
                                     → b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))
                                     → b ∈ subset-of-small-ϕ-closed-subset X))
   c-closed-of-small-ϕ-closed-subset (P , c-clsd , ϕ-clsd) = c-clsd

   ϕ-closed-of-small-ϕ-closed-subset : (X : small-ϕ-closed-subsets)
                                     → ((a : ⟨ L ⟩)
                                     → (b : B)
                                     → ((b , a) ∈ ϕ)
                                     → ((b' : B)
                                     → (b' ≤ᴮ a
                                     → b' ∈ subset-of-small-ϕ-closed-subset X))
                                     → b ∈ subset-of-small-ϕ-closed-subset X)
   ϕ-closed-of-small-ϕ-closed-subset (P , c-clsd , ϕ-clsd) = ϕ-clsd

   _is-non-inc : (a : ⟨ L ⟩) → 𝓦  ̇
   a is-non-inc = ((Γ ϕ i) a ≤ a) holds

   is-non-inc-is-predicate : (a : ⟨ L ⟩) → is-prop(a is-non-inc)
   is-non-inc-is-predicate a = holds-is-prop ((Γ ϕ i) a ≤ a)

   non-inc-points : 𝓤 ⊔ 𝓦  ̇
   non-inc-points = Σ a ꞉ ⟨ L ⟩ , (a is-non-inc)

   point-non-inc-points : non-inc-points → ⟨ L ⟩
   point-non-inc-points (a , non-inc) = a

   is-non-inc-non-inc-points : (X : non-inc-points)
                             → (point-non-inc-points X) is-non-inc
   is-non-inc-non-inc-points (a , non-inc) = non-inc

   small-ϕ-closed-subsets-to-non-inc-points : small-ϕ-closed-subsets
                                            → non-inc-points
   small-ϕ-closed-subsets-to-non-inc-points (P , c-closed , ϕ-closed) =
     (sup-P , is-non-inc)
    where
     sup-P : ⟨ L ⟩
     sup-P = ⋁ (𝕋 P , q ∘ 𝕋-to-carrier P)
     open subsets-order-joins L B q hiding (⋁_ ; _≤_)
     is-non-inc : sup-P is-non-inc
     is-non-inc = Γ-is-least-upper-bound (sup-P , is-upper-bound)
      where
       open small-types-have-joins L (S ϕ sup-P)
                                   (q ∘ S-to-base ϕ sup-P) (i sup-P)
                                   hiding (⋁_ ; _≤_)
       Γ-is-sup : ((Γ ϕ i) sup-P is-lub-of (S ϕ sup-P , q ∘ S-to-base ϕ sup-P))
                  holds
       Γ-is-sup = sup-of-small-fam-is-lub
       Γ-is-least-upper-bound :
         ((u , _) : upper-bound (S ϕ sup-P , q ∘ S-to-base ϕ sup-P))
                              → ((Γ ϕ i) sup-P ≤ u) holds
       Γ-is-least-upper-bound = pr₂ Γ-is-sup
       b-in-P-to-b-≤-sup-P : (b : B) → b ∈ P → (q(b) ≤ sup-P) holds
       b-in-P-to-b-≤-sup-P b b-in-P =
         (is-an-upper-bound-for L of (𝕋 P , q ∘ 𝕋-to-carrier P)) (b , b-in-P)
       un-trunc-map : (b : B)
                    → Σ a ꞉ ⟨ L ⟩ , (b , a) ∈ ϕ × (a ≤ sup-P) holds
                    → (q(b) ≤ sup-P) holds
       un-trunc-map b (a , p , o) =
         b-in-P-to-b-≤-sup-P b (ϕ-closed a b p (ϕ-hypothesis))
        where
         ϕ-hypothesis : (b' : B) → b' ≤ᴮ a → b' ∈ P
         ϕ-hypothesis b' r = c-closed P (λ x → id) b' b'-≤-sup-P
          where
           b'-≤-sup-P : b' ≤ᴮ sup-P
           b'-≤-sup-P = _≤_-to-_≤ᴮ_ (is-transitive-for L (q b') a sup-P
                                                       (_≤ᴮ_-to-_≤_ r) o)
       is-upper-bound : ((b , e) : S ϕ sup-P) → (q(b) ≤ sup-P) holds
       is-upper-bound (b , e) = ∥∥-rec (holds-is-prop (q(b) ≤ sup-P))
                                       (un-trunc-map b) e

   non-inc-points-to-small-ϕ-closed-subsets : non-inc-points
                                            → small-ϕ-closed-subsets
   non-inc-points-to-small-ϕ-closed-subsets (a , is-non-inc) =
     (Q a , c-closed , ϕ-closed)
    where
     Q : (x : ⟨ L ⟩) → 𝓟 {𝓥} B
     Q x b = (b ≤ᴮ x , _≤ᴮ_-is-prop-valued)
     sup-Q_ : (x : ⟨ L ⟩) → ⟨ L ⟩
     sup-Q x = ⋁ (𝕋 (Q x) , q ∘ 𝕋-to-carrier (Q x))
     _＝-sup-Q : (x : ⟨ L ⟩) → x ＝ sup-Q x
     x ＝-sup-Q = is-sup'ᴮ x
     open subsets-order-joins L B q hiding (_≤_ ; ⋁_)
     c-closed : (U : 𝓟 {𝓥} B)
              → (U ⊆ Q a)
              → ((b : B) → (b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))) →  b ∈ Q a)
     c-closed U C b o = _≤_-to-_≤ᴮ_ (is-transitive-for L (q b)
                                    (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))
                                    a
                                    (_≤ᴮ_-to-_≤_ o)
                                    (transport (λ z → ((⋁ (𝕋 U ,
                                      q ∘ 𝕋-to-carrier U)) ≤ z) holds)
                                               (a ＝-sup-Q ⁻¹)
                                               (joins-preserve-containment {U}
                                                                     {Q a} C)))
     ϕ-closed : (a' : ⟨ L ⟩)
              → (b : B)
              → ((b , a') ∈ ϕ)
              → ((b' : B) → (b' ≤ᴮ a' → b' ∈ Q a)) → b ∈ Q a
     ϕ-closed a' b p f = trunc-map b ∣ (a' , p , a'-≤-a) ∣
      where
       open small-types-have-joins L (S ϕ a) (q ∘ S-to-base ϕ a) (i a)
                                   hiding (⋁_ ; _≤_)
       Γ-is-sup : ((Γ ϕ i) a is-lub-of (S ϕ a , q ∘ S-to-base ϕ a)) holds
       Γ-is-sup = sup-of-small-fam-is-lub
       Γ-an-upper-bound :
         ((Γ ϕ i) a is-an-upper-bound-of (S ϕ a , q ∘ S-to-base ϕ a)) holds
       Γ-an-upper-bound = pr₁ Γ-is-sup
       trunc-map : (x : B)
                 → (Ǝ a'' ꞉ ⟨ L ⟩ , (x , a'') ∈ ϕ × (a'' ≤ a) holds) holds
                 → x ≤ᴮ a
       trunc-map x e = _≤_-to-_≤ᴮ_
                       (is-transitive-for L (q x) ((Γ ϕ i) a) a
                                          (Γ-an-upper-bound (x , e))
                                          (is-non-inc))
       a'-≤-a : (a' ≤ a) holds
       a'-≤-a = transport (λ z → (z ≤ a) holds)
                          (a' ＝-sup-Q ⁻¹)
                          (transport (λ z → ((sup-Q a') ≤ z) holds)
                                            (a ＝-sup-Q ⁻¹)
                                            (joins-preserve-containment {Q a'}
                                                                     {Q a} f))

   small-ϕ-closed-subsets-≃-non-inc-points :
     small-ϕ-closed-subsets ≃ non-inc-points
   small-ϕ-closed-subsets-≃-non-inc-points =
     (small-ϕ-closed-subsets-to-non-inc-points ,
       qinvs-are-equivs small-ϕ-closed-subsets-to-non-inc-points is-qinv)
    where
     H : non-inc-points-to-small-ϕ-closed-subsets
       ∘ small-ϕ-closed-subsets-to-non-inc-points ∼ id
     H (P , c-closed , ϕ-closed) =
       to-subtype-＝ is-small-ϕ-closed-subset-is-predicate P'-＝-P
      where
       sup-P : ⟨ L ⟩
       sup-P = point-non-inc-points
               (small-ϕ-closed-subsets-to-non-inc-points
                (P , c-closed , ϕ-closed))
       P' : 𝓟 {𝓥} B
       P' = subset-of-small-ϕ-closed-subset
             (non-inc-points-to-small-ϕ-closed-subsets
              (small-ϕ-closed-subsets-to-non-inc-points
               (P , c-closed , ϕ-closed)))
       P'-＝-P : P' ＝ P
       P'-＝-P = dfunext fe P'-∼-P 
        where
         P'-∼-P : P' ∼ P
         P'-∼-P x = to-Ω-＝ fe (pe _≤ᴮ_-is-prop-valued (holds-is-prop (P x))
                               P'-to-P P-to-P')
          where
           P'-to-P : x ≤ᴮ sup-P → x ∈ P
           P'-to-P = c-closed P (λ _ → id) x
           P-to-P' : x ∈ P → x ≤ᴮ sup-P
           P-to-P' r = _≤_-to-_≤ᴮ_ ((is-an-upper-bound-for L of
                                    (𝕋 P , q ∘ 𝕋-to-carrier P)) (x , r))
     G : small-ϕ-closed-subsets-to-non-inc-points
       ∘ non-inc-points-to-small-ϕ-closed-subsets ∼ id
     G (a , is-non-inc) = to-subtype-＝ is-non-inc-is-predicate sup-P-＝-a
      where
       P : 𝓟 {𝓥} B
       P = subset-of-small-ϕ-closed-subset
            (non-inc-points-to-small-ϕ-closed-subsets (a , is-non-inc))
       sup-P : ⟨ L ⟩
       sup-P = point-non-inc-points
                (small-ϕ-closed-subsets-to-non-inc-points
                 (non-inc-points-to-small-ϕ-closed-subsets (a , is-non-inc)))
       sup-P-＝-a : sup-P ＝ a
       sup-P-＝-a = is-sup'ᴮ a ⁻¹
     is-qinv : qinv small-ϕ-closed-subsets-to-non-inc-points
     is-qinv = (non-inc-points-to-small-ϕ-closed-subsets , H , G)

   module small-𝓘nd-from-exists (ind-e : inductively-generated-subset-exists ϕ)
                                 where

    open inductively-generated-subset-exists ind-e
    open trunc-ind-def ϕ ind-e

    module smallness-assumption (j : (b : B) → (b ∈ 𝓘nd) is 𝓥 small) where

     𝓘' : (b : B) →  𝓥  ̇
     𝓘' b = (resized (b ∈ 𝓘nd)) (j b) 

     𝓘'-≃-𝓘nd : (b : B) → 𝓘' b ≃ b ∈ 𝓘nd 
     𝓘'-≃-𝓘nd b = resizing-condition (j b)

     𝓘'-to-𝓘nd : (b : B) → 𝓘' b → b ∈ 𝓘nd
     𝓘'-to-𝓘nd b = ⌜ 𝓘'-≃-𝓘nd b ⌝

     𝓘nd-to-𝓘' : (b : B) → b ∈ 𝓘nd → 𝓘' b
     𝓘nd-to-𝓘' b = ⌜ 𝓘'-≃-𝓘nd b ⌝⁻¹

     𝓘'-is-prop-valued : {b : B} → is-prop (𝓘' b)
     𝓘'-is-prop-valued {b} = equiv-to-prop (𝓘'-≃-𝓘nd b) (Ind-trunc b)

     𝓘'-subset : 𝓟 {𝓥} B
     𝓘'-subset = λ b → (𝓘' b , 𝓘'-is-prop-valued)

     𝓘'-is-c-closed : (U : 𝓟 {𝓥} B)
                    → U ⊆ 𝓘'-subset
                    → (b : B) → b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))
                    → b ∈ 𝓘'-subset
     𝓘'-is-c-closed U C b o =
       𝓘nd-to-𝓘' b (𝓘nd-is-c-closed U (λ x → 𝓘'-to-𝓘nd x ∘ C x) b o)
      
     𝓘'-is-ϕ-closed : (a : ⟨ L ⟩)
                    → (b : B)
                    → (b , a) ∈ ϕ
                    → ((b' : B) → b' ≤ᴮ a → b' ∈ 𝓘'-subset)
                    → b ∈ 𝓘'-subset
     𝓘'-is-ϕ-closed a b p f =
       𝓘nd-to-𝓘' b (𝓘nd-is-ϕ-closed a b p
                   (λ b' → 𝓘'-to-𝓘nd b' ∘ f b'))

     total-space-𝓘-is-small : (𝕋 𝓘nd) is 𝓥 small
     total-space-𝓘-is-small = (𝕋 𝓘'-subset , Σ-cong λ b → 𝓘'-≃-𝓘nd b)
   
     e : 𝕋 𝓘'-subset ≃ 𝕋 𝓘nd
     e = pr₂ total-space-𝓘-is-small

     sup-𝓘 : ⟨ L ⟩
     sup-𝓘 = ⋁ (𝕋 𝓘'-subset , q ∘ 𝕋-to-carrier 𝓘nd ∘ ⌜ e ⌝)

     sup-𝓘-is-lub : (sup-𝓘 is-lub-of (𝕋 𝓘nd , q ∘ 𝕋-to-carrier 𝓘nd)) holds
     sup-𝓘-is-lub = sup-of-small-fam-is-lub
      where
       open small-types-have-joins L (𝕋 𝓘nd) (q ∘ 𝕋-to-carrier 𝓘nd)
                                   total-space-𝓘-is-small

     Γ-has-least-fixed-point : Σ x ꞉ ⟨ L ⟩ ,
                                ((Γ ϕ i) x ＝ x) × ((a : ⟨ L ⟩)
                                                 → ((Γ ϕ i) a ＝ a)
                                                 → (x ≤ a) holds)
     Γ-has-least-fixed-point =
       (sup-𝓘 , is-antisymmetric-for L Γ-sup-≤-sup sup-≤-Γ-sup , sup-𝓘-≤)
      where
       Γ-sup-≤-sup : ((Γ ϕ i) sup-𝓘 ≤ sup-𝓘) holds
       Γ-sup-≤-sup = is-non-inc-non-inc-points
                      (small-ϕ-closed-subsets-to-non-inc-points
                      (𝓘'-subset , 𝓘'-is-c-closed , 𝓘'-is-ϕ-closed))
       sup-≤-Γ-sup : (sup-𝓘 ≤ (Γ ϕ i) sup-𝓘) holds
       sup-≤-Γ-sup = transport (λ z → (sup-𝓘 ≤ z) holds)
                               sup-Q-＝-Γ-sup sup-𝓘-≤-sup-Q
        where
         open subsets-order-joins L B q hiding (_≤_ ; ⋁_)
         Γ-Γ-sup-≤-Γ-sup : ((Γ ϕ i) ((Γ ϕ i) sup-𝓘) ≤ (Γ ϕ i) sup-𝓘) holds
         Γ-Γ-sup-≤-Γ-sup = Γ-is-monotone ϕ i ((Γ ϕ i) sup-𝓘) sup-𝓘 Γ-sup-≤-sup
         Q-Γ-sup : 𝓟 {𝓥} B
         Q-Γ-sup = subset-of-small-ϕ-closed-subset
                    (non-inc-points-to-small-ϕ-closed-subsets
                     ((Γ ϕ i) sup-𝓘 , Γ-Γ-sup-≤-Γ-sup))
         Q-is-c-closed : (U : 𝓟 {𝓥} B)
                       → (U ⊆ Q-Γ-sup)
                       → ((b : B)
                       → b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))
                       → b ∈ Q-Γ-sup)
         Q-is-c-closed =
           c-closed-of-small-ϕ-closed-subset
            (non-inc-points-to-small-ϕ-closed-subsets
             ((Γ ϕ i) sup-𝓘 , Γ-Γ-sup-≤-Γ-sup))
         Q-is-ϕ-closed : (a' : ⟨ L ⟩)
                       → (b : B)
                       → ((b , a') ∈ ϕ)
                       → ((b' : B)
                       → (b' ≤ᴮ a' → b' ∈ Q-Γ-sup))
                       → b ∈ Q-Γ-sup
         Q-is-ϕ-closed = ϕ-closed-of-small-ϕ-closed-subset
                          (non-inc-points-to-small-ϕ-closed-subsets
                           ((Γ ϕ i) sup-𝓘 , Γ-Γ-sup-≤-Γ-sup))
         𝓘nd-⊆-Q-Γ-sup : 𝓘nd ⊆ Q-Γ-sup
         𝓘nd-⊆-Q-Γ-sup = 𝓘nd-is-initial Q-Γ-sup Q-is-c-closed Q-is-ϕ-closed
         𝓘-is-small-subset-⊆-Q-Γ-sup : 𝓘'-subset ⊆ Q-Γ-sup
         𝓘-is-small-subset-⊆-Q-Γ-sup =
           λ z → 𝓘nd-⊆-Q-Γ-sup z ∘ 𝓘'-to-𝓘nd z
         sup-Q : ⟨ L ⟩
         sup-Q = ⋁ (𝕋 Q-Γ-sup , q ∘ 𝕋-to-carrier Q-Γ-sup)
         sup-𝓘-≤-sup-Q : (sup-𝓘 ≤ sup-Q) holds
         sup-𝓘-≤-sup-Q =
           joins-preserve-containment {𝓘'-subset}
                                      {Q-Γ-sup}
                                      𝓘-is-small-subset-⊆-Q-Γ-sup
         sup-Q-＝-Γ-sup : sup-Q ＝ (Γ ϕ i) sup-𝓘
         sup-Q-＝-Γ-sup = is-sup'ᴮ ((Γ ϕ i) sup-𝓘) ⁻¹
       sup-𝓘-≤ : (a : ⟨ L ⟩) → ((Γ ϕ i) a ＝ a) → (sup-𝓘 ≤ a) holds
       sup-𝓘-≤ a p = transport (λ z → (sup-𝓘 ≤ z) holds)
                               sup-P-＝-a
                               sup-𝓘-≤-sup-P
        where
         open subsets-order-joins L B q hiding (_≤_ ; ⋁_)
         Γ-a-≤-a : ((Γ ϕ i) a ≤ a) holds
         Γ-a-≤-a = transport (λ z → ((Γ ϕ i) a ≤ z) holds)
                             p (is-reflexive-for L ((Γ ϕ i) a))
         P-a : 𝓟 {𝓥} B
         P-a = subset-of-small-ϕ-closed-subset
                (non-inc-points-to-small-ϕ-closed-subsets (a , Γ-a-≤-a))
         P-is-c-closed : (U : 𝓟 {𝓥} B)
                       → (U ⊆ P-a)
                       → ((b : B)
                       → b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))
                       → b ∈ P-a)
         P-is-c-closed = c-closed-of-small-ϕ-closed-subset
                          (non-inc-points-to-small-ϕ-closed-subsets
                           (a , Γ-a-≤-a))
         P-is-ϕ-closed : (a' : ⟨ L ⟩)
                       → (b : B)
                       → ((b , a') ∈ ϕ)
                       → ((b' : B)
                       → (b' ≤ᴮ a' → b' ∈ P-a))
                       → b ∈ P-a
         P-is-ϕ-closed = ϕ-closed-of-small-ϕ-closed-subset
                          (non-inc-points-to-small-ϕ-closed-subsets
                           (a , Γ-a-≤-a))
         𝓘nd-⊆-P-a : 𝓘nd ⊆ P-a
         𝓘nd-⊆-P-a = 𝓘nd-is-initial P-a P-is-c-closed P-is-ϕ-closed
         𝓘'-subset-⊆-P-a : 𝓘'-subset ⊆ P-a
         𝓘'-subset-⊆-P-a = λ z → 𝓘nd-⊆-P-a z ∘ 𝓘'-to-𝓘nd z
         sup-P : ⟨ L ⟩
         sup-P = ⋁ (𝕋 P-a , q ∘ 𝕋-to-carrier P-a)
         sup-𝓘-≤-sup-P : (sup-𝓘 ≤ sup-P) holds
         sup-𝓘-≤-sup-P = joins-preserve-containment
                          {𝓘'-subset}
                          {P-a}
                          𝓘'-subset-⊆-P-a
         sup-P-＝-a : sup-P ＝ a
         sup-P-＝-a = is-sup'ᴮ a ⁻¹

\end{code}

We now consider a boundedness restricion on inductive definitions and show
that bounded inductive definitions are local.

An inductive definition is bounded if there is a small indexed family of
types that can be substituted for elements a : L in a sense to be made
precise below.

\begin{code}

module bounded-inductive-definition {𝓤 𝓦 𝓥 : Universe}
                                    {B : 𝓥  ̇}
                                    (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                    (q : B → ⟨ L ⟩)
                                     where

 open small-basis L q
 open Joins _≤_

 module bounded-from-small-basis-facts (h : is-small-basis) where

  open small-basis-facts h
  open PropositionalTruncation pt

  _is-a-small-cover-of_ : (X : 𝓥  ̇) → (Y : 𝓣  ̇) → 𝓥 ⊔ 𝓣  ̇
  X is-a-small-cover-of Y = X ↠ Y

  _has-a-bound : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
  ϕ has-a-bound = Σ I ꞉ 𝓥  ̇ , Σ α ꞉ (I → 𝓥  ̇) ,
                   ((a : ⟨ L ⟩)
                 → (b : B)
                 → (b , a) ∈ ϕ
                 → (Ǝ i ꞉ I , α i is-a-small-cover-of ↓ᴮ a) holds)

  bound-index : {ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)} → ϕ has-a-bound → 𝓥  ̇
  bound-index (I , α , covering) = I

  bound-family : {ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)}
               → (bnd : ϕ has-a-bound)
               → (bound-index {ϕ} bnd → 𝓥  ̇)
  bound-family (I , α , covering) = α

  covering-condition : {ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)}
                     → (bnd : ϕ has-a-bound)
                     → ((a : ⟨ L ⟩)
                     → (b : B)
                     → (b , a) ∈ ϕ
                     → (Ǝ i ꞉ (bound-index {ϕ} bnd) ,
                        ((bound-family {ϕ} bnd) i is-a-small-cover-of ↓ᴮ a))
                         holds)
  covering-condition (I , α , covering) = covering

  _is-bounded : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
  ϕ is-bounded = ((a : ⟨ L ⟩) → (b : B) → ((b , a) ∈ ϕ) is 𝓥 small)
               × (ϕ has-a-bound)

  open local-inductive-definitions L q
  open local-from-small-basis-facts h

  _bounded-implies-local : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                         → ϕ is-bounded
                         → ϕ is-local
  (ϕ bounded-implies-local) (ϕ-small , ϕ-has-bound) a =
    smallness-closed-under-≃ S₀-is-small S₀-≃-S
   where
    I : 𝓥  ̇
    I = bound-index {ϕ} ϕ-has-bound
    α : I → 𝓥  ̇
    α = bound-family {ϕ} ϕ-has-bound
    cov : (a : ⟨ L ⟩)
        → (b : B)
        → (b , a) ∈ ϕ
        → (Ǝ i ꞉ I , (α i is-a-small-cover-of ↓ᴮ a)) holds
    cov = covering-condition {ϕ} ϕ-has-bound
    S₀ : 𝓤 ⊔ 𝓦 ⊔ 𝓥  ̇
    S₀ = Σ b ꞉ B , (Ǝ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
                   (b , ⋁ (α i , ↓ᴮ-inclusion a ∘ m)) ∈ ϕ) holds) holds
    S₀-is-small : S₀ is 𝓥 small
    S₀-is-small =
     Σ-is-small (B , ≃-refl B)
                (λ b → ∥∥-is-small pt (Σ-is-small (I , ≃-refl I)
                       λ i → ∥∥-is-small pt
                             (Σ-is-small (Π-is-small (fe') (α i , ≃-refl (α i))
                             λ _ → ↓ᴮ-is-small)
                             λ m → ϕ-small (⋁ (α i , ↓ᴮ-inclusion a ∘ m)) b)))

    S₀-to-S : S₀ → S ϕ a
    S₀-to-S (b , e) = (b , map₄ e)
     where
      map₁ : (i : I)
           → (Σ m ꞉ (α i → ↓ᴮ a) , (b , (⋁ (α i , ↓ᴮ-inclusion a ∘ m))) ∈ ϕ)
           → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
      map₁ i (m , p) =
        ∣ (⋁ (α i , ↓ᴮ-inclusion a ∘ m) , p ,
          (is-least-upper-bound-for L of (α i , ↓ᴮ-inclusion a ∘ m))
                                         (a , λ z → is-upper-bound-↓ a (m z))) ∣
      map₂ : (i : I)
           → (Ǝ m ꞉ (α i → ↓ᴮ a) ,
             (b , (⋁ (α i , ↓ᴮ-inclusion a ∘ m))) ∈ ϕ) holds
           → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
      map₂ i = ∥∥-rec ∥∥-is-prop (map₁ i)
      map₃ : Σ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
              (b , (⋁ (α i , ↓ᴮ-inclusion a ∘ m))) ∈ ϕ) holds
           → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
      map₃ = uncurry map₂
      map₄ : (Ǝ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
              (b , ⋁ (α i , ↓ᴮ-inclusion a ∘ m)) ∈ ϕ) holds) holds
           → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
      map₄ = ∥∥-rec ∥∥-is-prop map₃

    S-to-S₀ : S ϕ a → S₀
    S-to-S₀ (b , e) = (b , map₄ e)
     where
      ι : (a' : ⟨ L ⟩) → (a' ≤ a) holds → ↓ᴮ a' → ↓ᴮ a
      ι a' o (x , r) = (x , is-transitive-for L (q x) a' a r o)
      map₁ : (a' : ⟨ L ⟩)
           →  (b , a') ∈ ϕ
           → (a' ≤ a) holds
           → (Σ i ꞉ I , (α i is-a-small-cover-of ↓ᴮ a'))
           → (Ǝ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
               (b , ⋁ (α i , ↓ᴮ-inclusion a ∘ m)) ∈ ϕ) holds) holds
      map₁ a' p o (i , α-covers) = ∣ (i , ∣ (m , p') ∣) ∣
       where
        open surjection-implies-equal-joins L (↓ᴮ a') (α i)
                                              α-covers (q ∘ pr₁)
                                               hiding (⋁_ ; _≤_)
        m : α i → ↓ᴮ a
        m = ι a' o ∘ ⌞ α-covers ⌟
        path : a' ＝ ⋁ (α i , ↓ᴮ-inclusion a ∘ m)
        path = reindexing-along-surj-＝-sup a'
                                           (⋁ (α i , ↓ᴮ-inclusion a ∘ m))
                                           (is-sup-↓ a')
                                 (is-lub-for L (α i , ↓ᴮ-inclusion a ∘ m))
        p' : (b , ⋁ (α i , ↓ᴮ-inclusion a ∘ m)) ∈ ϕ
        p' = transport (λ z → (b , z) ∈ ϕ) path p
      map₂ : (a' : ⟨ L ⟩)
           → (b , a') ∈ ϕ
           → (a' ≤ a) holds
           → (Ǝ i ꞉ I , (α i is-a-small-cover-of ↓ᴮ a')) holds
           → (Ǝ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
              (b , (⋁ (α i , ↓ᴮ-inclusion a ∘ m))) ∈ ϕ) holds) holds
      map₂ a' p o = ∥∥-rec ∥∥-is-prop (map₁ a' p o)
      map₃ : Σ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds
           → (Ǝ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
              (b , ⋁ (α i , ↓ᴮ-inclusion a ∘ m)) ∈ ϕ) holds) holds
      map₃ (a' , p , o) = map₂ a' p o (cov a' b p)
      map₄ : (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
           → (Ǝ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
              (b , ⋁ (α i , ↓ᴮ-inclusion a ∘ m)) ∈ ϕ) holds) holds
      map₄ = ∥∥-rec ∥∥-is-prop map₃

    S₀-≃-S : S₀ ≃ S ϕ a
    S₀-≃-S =
      (S₀-to-S , qinvs-are-equivs S₀-to-S is-qinv)
     where
      H : S-to-S₀ ∘ S₀-to-S ∼ id
      H (b , e) = to-subtype-＝ (λ _ → ∥∥-is-prop) refl
      G : S₀-to-S ∘ S-to-S₀ ∼ id
      G (b , e) = to-subtype-＝ (λ _ → ∥∥-is-prop) refl
      is-qinv : qinv S₀-to-S
      is-qinv = (S-to-S₀ , H , G)

\end{code}

We now consider a stronger restriction on sup-lattices. A sup-lattice has a
small presentation if there is a small indexed family of subsets that can be
substituted for arbitrary subsets in a sense to be made precise below.

\begin{code}

module small-presentation-of-lattice {𝓤 𝓦 𝓥 : Universe}
                                     {B : 𝓥  ̇}
                                     (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                     (q : B → ⟨ L ⟩)
                                      where

 open small-basis L q
 open Joins _≤_

 module small-presentation-from-small-basis-facts (h : is-small-basis) where

  open small-basis-facts h
  open PropositionalTruncation pt

  _is-a-small-presentation : Σ J ꞉ 𝓥  ̇ , (J → 𝓟 {𝓥} B) × 𝓟 {𝓥} (B × 𝓟 {𝓥} B)
                           → (𝓥 ⁺)  ̇
  (J , Y , R) is-a-small-presentation = (b : B)
                                      → (X : 𝓟 {𝓥} B)
                                      → b ≤ᴮ (⋁ (𝕋 X , q ∘ 𝕋-to-carrier X))
                                      ≃ ((Ǝ j ꞉ J , Y j ⊆ X × (b , Y j) ∈ R)
                                         holds)

  has-small-presentation : (𝓥 ⁺)  ̇
  has-small-presentation = Σ 𝓡 ꞉ Σ J ꞉ 𝓥  ̇ ,
                            (J → 𝓟 {𝓥} B) × 𝓟 {𝓥} (B × 𝓟 {𝓥} B) ,
                            𝓡 is-a-small-presentation

\end{code}

We will now define, in the context of bounded ϕ and small-presentation 𝓡, a
new QIT that is equivalent to 𝓘nd. Notice the bounded and small-presentation
restrictions allow us to avoid large quantification! 

\begin{code}

module small-QIT {𝓤 𝓦 𝓥 : Universe}
                 {B : 𝓥  ̇}
                 (L : Sup-Lattice 𝓤 𝓦 𝓥)
                 (q : B → ⟨ L ⟩)
                  where

 open small-basis L q
 open bounded-inductive-definition L q
 open small-presentation-of-lattice L q

 module small-QIT-from-small-basis-facts (h : is-small-basis) where
 
  open small-basis-facts h
  open bounded-from-small-basis-facts h
  open small-presentation-from-small-basis-facts h
 
  module small-QIT-from-bounded-and-small-presentation
    (small-pres : has-small-presentation)
    (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
    (bnd : ϕ is-bounded)
     where

   I₁ : 𝓥  ̇
   I₁ = pr₁ (pr₁ small-pres)

   Y : I₁ → 𝓟 {𝓥} B
   Y = pr₁ (pr₂ (pr₁ small-pres))

   R : 𝓟 {𝓥} (B × 𝓟 {𝓥} B)
   R = pr₂ (pr₂ (pr₁ small-pres))

   is-small-pres : (I₁ , Y , R) is-a-small-presentation
   is-small-pres = pr₂ small-pres

   is-small-pres-forward : (b : B)
                         → (X : 𝓟 {𝓥} B)
                         → b ≤ᴮ (⋁ (𝕋 X , q ∘ 𝕋-to-carrier X))
                         → ((Ǝ j ꞉ I₁ , Y j ⊆ X × (b , Y j) ∈ R) holds)
   is-small-pres-forward b X = ⌜ is-small-pres b X ⌝

   is-small-pres-backward : (b : B)
                          → (X : 𝓟 {𝓥} B)
                          → ((Ǝ j ꞉ I₁ , Y j ⊆ X × (b , Y j) ∈ R) holds)
                          → b ≤ᴮ (⋁ (𝕋 X , q ∘ 𝕋-to-carrier X))
   is-small-pres-backward b X = ⌜ is-small-pres b X ⌝⁻¹

   ϕ-is-small : (a : ⟨ L ⟩) → (b : B) → ((b , a) ∈ ϕ) is 𝓥 small
   ϕ-is-small = pr₁ bnd

   small-ϕ : (b : B) → (a : ⟨ L ⟩) → 𝓥  ̇
   small-ϕ b a = pr₁ (ϕ-is-small a b)

   ϕ-is-small-≃ : (a : ⟨ L ⟩) → (b : B) → small-ϕ b a ≃ (b , a) ∈ ϕ
   ϕ-is-small-≃ a b = pr₂ (ϕ-is-small a b)

   ϕ-is-small-forward : (a : ⟨ L ⟩) → (b : B) → small-ϕ b a → (b , a) ∈ ϕ
   ϕ-is-small-forward a b = ⌜ ϕ-is-small-≃ a b ⌝

   ϕ-is-small-backward : (a : ⟨ L ⟩) → (b : B) → (b , a) ∈ ϕ → small-ϕ b a
   ϕ-is-small-backward a b = ⌜ ϕ-is-small-≃ a b ⌝⁻¹

   I₂ : 𝓥  ̇
   I₂ = pr₁ (pr₂ bnd)

   α : I₂ → 𝓥  ̇
   α = pr₁ (pr₂ (pr₂ bnd))

   cover-condition : ((a : ⟨ L ⟩)
                   → (b : B)
                   → (b , a) ∈ ϕ
                   → (Ǝ i ꞉ I₂ , α i is-a-small-cover-of ↓ᴮ a) holds)
   cover-condition = pr₂ (pr₂ (pr₂ bnd))

   data Small-Ind-Check : B → 𝓥  ̇ where
    Small-c-cl' : (i : I₁)
                → ((b : B) → (b ∈ Y i → Small-Ind-Check b))
                → (b : B) → (b , Y i) ∈ R
                → Small-Ind-Check b
    Small-ϕ-cl' : (i : I₂)
                → (m : α i → B)
                → (b : B)
                → small-ϕ b (⋁ (α i , q ∘ m))
                → ((b' : B) → (b' ≤ᴮ (⋁ (α i , q ∘ m)) → Small-Ind-Check b'))
                → Small-Ind-Check b

   record inductively-generated-small-subset-exists : 𝓤ω where
    constructor
     inductively-generated-small-subset

    field
     Small-Ind : B → 𝓥  ̇
     Small-Ind-trunc : (b : B) → is-prop (Small-Ind b)
     Small-c-cl : (i : I₁)
                → ((b : B) → (b ∈ Y i → Small-Ind b))
                → (b : B) → (b , Y i) ∈ R
                → Small-Ind b
     Small-ϕ-cl : (i : I₂)
                → (m : α i → B)
                → (b : B)
                → small-ϕ b (⋁ (α i , q ∘ m))
                → ((b' : B) → (b' ≤ᴮ (⋁ (α i , q ∘ m)) → Small-Ind b'))
                → Small-Ind b
     Small-Ind-Induction : (P : (b : B) → 𝓟 {𝓣} (Small-Ind b))
                         → ((i : I₁) → (f : (x : B) → (x ∈ Y i → Small-Ind x))
                          → ((x : B) → (y : x ∈ Y i) → f x y ∈ P x)
                          → (b : B) → (g : (b , Y i) ∈ R)
                          → Small-c-cl i f b g ∈ P b)
                         → ((i : I₂)
                          → (m : α i → B)
                          → (b : B)
                          → (p : small-ϕ b (⋁ (α i , q ∘ m)))
                          → (f : (x : B)
                          → (x ≤ᴮ (⋁ (α i , q ∘ m))
                          → Small-Ind x))
                          → ((x : B)
                          → (o : x ≤ᴮ (⋁ (α i , q ∘ m)))
                          → f x o ∈ P x)
                          → Small-ϕ-cl i m b p f ∈ P b)
                         → (b : B) → (i : Small-Ind b) → i ∈ P b

   module small-trunc-ind-def
     (ind-e : inductively-generated-small-subset-exists)
      where

    open inductively-generated-small-subset-exists ind-e

    Small-𝓘nd : 𝓟 {𝓥} B
    Small-𝓘nd b = (Small-Ind b , Small-Ind-trunc b)

    Small-𝓘nd-is-c-cl : (i : I₁)
                      → Y i ⊆ Small-𝓘nd
                      → (b : B)
                      → (b , Y i) ∈ R
                      → b ∈ Small-𝓘nd
    Small-𝓘nd-is-c-cl = Small-c-cl

    Small-𝓘nd-is-ϕ-cl : (i : I₂)
                      → (m : α i → B)
                      → (b : B)
                      → small-ϕ b (⋁ (α i , q ∘ m))
                      → ((b' : B)
                      → (b' ≤ᴮ (⋁ (α i , q ∘ m))
                      → b' ∈ Small-𝓘nd))
                      → b ∈ Small-𝓘nd
    Small-𝓘nd-is-ϕ-cl = Small-ϕ-cl

    Small-𝓘nd-Induction : (P : (b : B) → 𝓟 {𝓣} (b ∈ Small-𝓘nd))
                        → ((i : I₁) → (f : Y i ⊆ Small-𝓘nd)
                         → ((x : B) → (y : x ∈ Y i) → f x y ∈ P x)
                         → (b : B) → (g : (b , Y i) ∈ R)
                         → Small-c-cl i f b g ∈ P b)
                        → ((i : I₂)
                         → (m : α i → B)
                         → (b : B)
                         → (p : small-ϕ b (⋁ (α i , q ∘ m)))
                         → (f : (x : B)
                         → (x ≤ᴮ (⋁ (α i , q ∘ m))
                         → x ∈ Small-𝓘nd))
                         → ((x : B)
                         → (o : x ≤ᴮ (⋁ (α i , q ∘ m)))
                         → f x o ∈ P x)
                         → Small-ϕ-cl i m b p f ∈ P b)
                        → (b : B) → (i : b ∈ Small-𝓘nd) → i ∈ P b
    Small-𝓘nd-Induction = Small-Ind-Induction

    Small-𝓘nd-Recursion : (P : 𝓟 {𝓣} B)
                        → ((i : I₁)
                         → (Y i ⊆ Small-𝓘nd)
                         → (Y i ⊆ P)
                         → (b : B) → (b , Y i) ∈ R
                         → b ∈ P)
                        → ((i : I₂)
                         → (m : α i → B)
                         → (b : B)
                         → small-ϕ b (⋁ (α i , q ∘ m))
                         → ((x : B) → (x ≤ᴮ (⋁ (α i , q ∘ m)) → x ∈ Small-𝓘nd))
                         → ((x : B) → (x ≤ᴮ (⋁ (α i , q ∘ m)) → x ∈ P))
                         → b ∈ P)
                        → Small-𝓘nd ⊆ P
    Small-𝓘nd-Recursion P = Small-𝓘nd-Induction λ b → (λ _ → P b)

    Small-𝓘nd-Initial : (P : 𝓟 {𝓣} B)
                      → ((i : I₁)
                       → (Y i ⊆ P)
                       → (b : B) → (b , Y i) ∈ R
                       → b ∈ P)
                      → ((i : I₂)
                       → (m : α i → B)
                       → (b : B)
                       → small-ϕ b (⋁ (α i , q ∘ m))
                       → ((x : B) → (x ≤ᴮ (⋁ (α i , q ∘ m)) → x ∈ P))
                       → b ∈ P)
                      → Small-𝓘nd ⊆ P
    Small-𝓘nd-Initial {𝓣} P IH₁ IH₂ b b-in-Small-𝓘nd =
      Small-𝓘nd-Recursion P S S' b b-in-Small-𝓘nd
     where
      S : (i : I₁)
        → (Y i ⊆ Small-𝓘nd)
        → (Y i ⊆ P)
        → (b : B) → (b , Y i) ∈ R
        → b ∈ P
      S i C₁ C₂ b r = IH₁ i C₂ b r
      S' : (i : I₂)
         → (m : α i → B)
         → (b : B)
         → small-ϕ b (⋁ (α i , q ∘ m))
         → ((x : B) → (x ≤ᴮ (⋁ (α i , q ∘ m)) → x ∈ Small-𝓘nd))
         → ((x : B) → (x ≤ᴮ (⋁ (α i , q ∘ m)) → x ∈ P))
         → b ∈ P
      S' i m b s f g = IH₂ i m b s g

\end{code}

We will now show that under the assumptions of small presentation and bounded
ϕ that b ∈ Small-𝓘nd ≃ b ∈ 𝓘nd. We make essential use of the initiality of
either type here.

This will allow us to satisfy the smallness conditions and salvage a least
fixed point theorem.

\begin{code}

module 𝓘nd-is-small {𝓤 𝓦 𝓥 : Universe}
                    {B : 𝓥  ̇}
                    (L : Sup-Lattice 𝓤 𝓦 𝓥)
                    (q : B → ⟨ L ⟩)
                     where

 open small-basis L q
 open bounded-inductive-definition L q
 open small-presentation-of-lattice L q
 open inductive-definitions L q
 open small-QIT L q

 module 𝓘nd-is-small-from-small-basis-facts (h : is-small-basis) where
 
  open small-basis-facts h
  open bounded-from-small-basis-facts h
  open small-presentation-from-small-basis-facts h
  open ind-from-small-basis-facts h
  open small-QIT-from-small-basis-facts h
 
  module 𝓘nd-is-small-from-bounded-and-small-presentation
    (small-pres : has-small-presentation)
    (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
    (bnd : ϕ is-bounded)
     where

   open small-QIT-from-bounded-and-small-presentation small-pres ϕ bnd

   module 𝓘nd-is-small-QITs-exists
    (ind-e : inductively-generated-subset-exists ϕ)
    (ind-e' : inductively-generated-small-subset-exists)
     where

    open trunc-ind-def ϕ ind-e
    open small-trunc-ind-def ind-e'
    open PropositionalTruncation pt

    𝓘nd-⊆-Small-𝓘nd : 𝓘nd ⊆ Small-𝓘nd
    𝓘nd-⊆-Small-𝓘nd = 𝓘nd-is-initial Small-𝓘nd f g
     where
      f : (U : 𝓟 {𝓥} B)
        → U ⊆ Small-𝓘nd
        → (b : B)
        → b ≤ᴮ (⋁ (𝕋 U , q ∘ 𝕋-to-carrier U))
        → b ∈ Small-𝓘nd
      f U C b o = f'' (is-small-pres-forward b U o)
       where
        f' : (Σ j ꞉ I₁ , Y j ⊆ U × (b , Y j) ∈ R)
           → b ∈ Small-𝓘nd
        f' (j , C' , r) = Small-𝓘nd-is-c-cl j (λ x → λ y → C x (C' x y)) b r
        f'' : (Ǝ j ꞉ I₁ , Y j ⊆ U × (b , Y j) ∈ R) holds
            → b ∈ Small-𝓘nd
        f'' = ∥∥-rec (holds-is-prop (Small-𝓘nd b)) f'
      g : (a : ⟨ L ⟩)
        → (b : B)
        → (b , a) ∈ ϕ
        → ((b' : B) → b' ≤ᴮ a → b' ∈ Small-𝓘nd)
        → b ∈ Small-𝓘nd
      g a b p C = g'' (cover-condition a b p)
       where
        g' : Σ i ꞉ I₂ , α i is-a-small-cover-of ↓ᴮ a
           → b ∈ Small-𝓘nd
        g' (i , s) =
         Small-𝓘nd-is-ϕ-cl i (↓ᴮ-to-base a ∘ ⌞ s ⌟) b
                         (ϕ-is-small-backward (⋁ (α i , ↓ᴮ-inclusion a ∘ ⌞ s ⌟))
                                              b
                                              (transport (λ a' → (b , a') ∈ ϕ)
                                                         (a-＝-⋁-α) p))
                                              (λ b' → C b'
                                                ∘ (transport (λ a'
                                                  → b' ≤ᴮ a') (a-＝-⋁-α ⁻¹))) 
         where
          open surjection-implies-equal-joins L (↓ᴮ a) (α i)
                                              s (↓ᴮ-inclusion a) hiding (⋁_)
          a-＝-⋁-α : a ＝ ⋁ (α i , ↓ᴮ-inclusion a ∘ ⌞ s ⌟)
          a-＝-⋁-α =
            reindexing-along-surj-＝-sup a
                                         (⋁ (α i , ↓ᴮ-inclusion a ∘ ⌞ s ⌟))
                                         (is-sup-↓ a)
                              (is-lub-for L (α i , ↓ᴮ-inclusion a ∘ ⌞ s ⌟))
        g'' : (Ǝ i ꞉ I₂ , α i is-a-small-cover-of ↓ᴮ a) holds
            → b ∈ Small-𝓘nd
        g'' = ∥∥-rec (holds-is-prop (Small-𝓘nd b)) g'

    Small-𝓘nd-⊆-𝓘nd : Small-𝓘nd ⊆ 𝓘nd
    Small-𝓘nd-⊆-𝓘nd = Small-𝓘nd-Initial 𝓘nd f g
     where
      f : (i : I₁)
        → Y i ⊆ 𝓘nd
        → (b : B)
        → (b , Y i) ∈ R
        → b ∈ 𝓘nd
      f i C b r =
        𝓘nd-is-c-closed (Y i) C b
                        (is-small-pres-backward b (Y i)
                                                ∣ (i , (λ _ → id) , r) ∣)
      g : (i : I₂)
        → (m : α i → B)
        → (b : B)
        → small-ϕ b (⋁ (α i , q ∘ m))
        → ((x : B) → x ≤ᴮ (⋁ (α i , q ∘ m)) → x ∈ 𝓘nd)
        → b ∈ 𝓘nd
      g i m b s C =
        𝓘nd-is-ϕ-closed (⋁ (α i , q ∘ m)) b
                        (ϕ-is-small-forward (⋁ (α i , q ∘ m)) b s) C

    𝓘nd-is-small : (b : B) → (b ∈ 𝓘nd) is 𝓥 small
    𝓘nd-is-small b = (b ∈ Small-𝓘nd , equiv)
     where
      equiv : b ∈ Small-𝓘nd ≃ b ∈ 𝓘nd
      equiv = logically-equivalent-props-are-equivalent
               (holds-is-prop (Small-𝓘nd b))
               (holds-is-prop (𝓘nd b))
               (Small-𝓘nd-⊆-𝓘nd b)
               (𝓘nd-⊆-Small-𝓘nd b)

\end{code}

As a corollary of the above result we get a predicative version of the least
fixed point theorem. Notice that we are assuming our lattice is
small-presented and that we have a bounded ϕ that corresponds to our
monotone map. This is the most general statement that can be made but we are
actively exploring other, cleaner, formulations.

\begin{code}

module least-fixed-point {𝓤 𝓦 𝓥 : Universe}
                         {B : 𝓥  ̇}
                         (L : Sup-Lattice 𝓤 𝓦 𝓥)
                         (q : B → ⟨ L ⟩)
                          where

 open small-basis L q 
 open bounded-inductive-definition L q
 open small-presentation-of-lattice L q
 open correspondance-small-ϕ-closed-types-def-points L q
 open inductive-definitions L q
 open small-QIT L q
 open local-inductive-definitions L q
 open monotone-endomaps L hiding (_≤_)
 open 𝓘nd-is-small L q

 module least-fixed-point-from-small-basis-facts (h : is-small-basis) where

  open small-basis-facts h
  open bounded-from-small-basis-facts h
  open small-presentation-from-small-basis-facts h
  open correspondance-from-small-basis-facts h
  open ind-from-small-basis-facts h
  open small-QIT-from-small-basis-facts h
  open local-from-small-basis-facts h
  open 𝓘nd-is-small-from-small-basis-facts h

  Least-Fixed-Point-Theorem : (small-pres : has-small-presentation)
                            → (f : ⟨ L ⟩ → ⟨ L ⟩)
                            → (f-mono : f is-monotone)
                            → (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                            → (bnd : ϕ is-bounded)
                            → ((x : ⟨ L ⟩)
                             → (Γ ϕ ((ϕ bounded-implies-local) bnd)) x ＝ f x)
                            → (ind-e : inductively-generated-subset-exists ϕ)
                            → (ind-e' :
   small-QIT-from-bounded-and-small-presentation.inductively-generated-small-subset-exists
                                        small-pres ϕ bnd)
                            → Σ x ꞉ ⟨ L ⟩ , (f x ＝ x) × ((a : ⟨ L ⟩)
                                                       → (f a ＝ a)
                                                       → (x ≤ a) holds)
  Least-Fixed-Point-Theorem small-pres f f-mono ϕ bnd H ind-e ind-e' =
    transport (λ g → Σ x ꞉ ⟨ L ⟩ , (g x ＝ x) × ((a : ⟨ L ⟩)
                                              → (g a ＝ a)
                                              → (x ≤ a) holds))
              path Γ-has-least-fixed-point
   where
    open correspondance-from-locally-small-ϕ ϕ ((ϕ bounded-implies-local) bnd)
    open small-𝓘nd-from-exists ind-e
    open 𝓘nd-is-small-from-bounded-and-small-presentation small-pres ϕ bnd
    open small-QIT-from-bounded-and-small-presentation small-pres ϕ bnd
    open 𝓘nd-is-small-QITs-exists ind-e ind-e'
    open smallness-assumption 𝓘nd-is-small
    path : Γ ϕ ((ϕ bounded-implies-local) bnd) ＝ f
    path = dfunext fe H

\end{code}



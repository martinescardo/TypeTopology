Ian Ray 01/09/2023.

We formalize Curi's notion of Abstract Inductive Definition (CZF) within the
context of a Sup-Lattice L with small basis B (and q : B → L). An abstract
inductive defintion is a subset ϕ : B × L → Prop which can be thought of as a
'inference rule' concluding b from a. An inductive definition induces a
closure condition. More precisely, a subset S is closed under ϕ if for all
b : B and a : L such that (b , a) ∈ ϕ and ↓ᴮa is 'contained' in S then b ∈ S.
Interestingly, there is an intimate connection between the least-closed
subsets of some inductive definition ϕ and the least fixed point of a monotome
map related to ϕ is a precise way. In this file we will develop this
relationship and prove a predicative version of the least fixed point theorem.
This work follows the paper 'On Tarski's Fixed Point Theorem' by Giovanni Curi. Fortunately, unlike in the realm of set theory, induction rules are first
class citizens in type theory. Using UF + HITs we can construct the least
closed subset under an inductive definition ϕ. Although, it should be noted
since HITs are not native in Agda we simply postulate the existence of the
type and work with it axiomatically. This postulate is of course justified as
the proposed HIT is quite tame. In fact, it is a very special case of a QIT
family, one that quotients every element together. 

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Logic
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Size
open import UF.SmallnessProperties
open import UF.Retracts
open import UF.UniverseEmbedding
open import UF.Equiv-FunExt
open import UF.Powerset-MultiUniverse

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

In the interest of self containment we open this file by defining a Sup-Lattice.

\begin{code}

module Sup-Lattice-Def (𝓤 𝓦 𝓥 : Universe) where

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
Sup-Lattice 𝓤 𝓦 𝓥 = Σ A ꞉ 𝓤  ̇ , rest A
 where
  open Sup-Lattice-Def 𝓤 𝓦 𝓥
  rest : 𝓤  ̇ → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓥 ⁺  ̇ 
  rest A = sup-lattice-structure A

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

We now define a monotone endo-map on lattice. This is sufficient as our intent
is to study fixed-points.

\begin{code}

module Monotone-Endo-Maps {𝓤 𝓦 𝓥 : Universe} (L : Sup-Lattice 𝓤 𝓦 𝓥) where

 _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦
 _≤_ = order-of L

 _is-monotone : (f : ⟨ L ⟩ → ⟨ L ⟩) → 𝓤 ⊔ 𝓦  ̇
 f is-monotone = (x y : ⟨ L ⟩) → (x ≤ y) holds → (f x ≤ f y) holds

\end{code}

We now show that when one subset contains another the join of their total
spaces are ordered as expected. This result will be quite useful throughout
this file.

\begin{code}

module Subsets-Order-Joins {𝓤 𝓦 𝓥 : Universe}
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
                            → ((⋁ ((Σ a ꞉ A , a ∈ P) , m ∘ pr₁))
                            ≤ (⋁ ((Σ a ꞉ A , a ∈ Q ) , m ∘ pr₁))) holds
 joins-preserve-containment {P} {Q} C =
   (is-least-upper-bound-for L of ((Σ a ꞉ A , a ∈ P ) , m ∘ pr₁))
    (⋁ ((Σ a ꞉ A , a ∈ Q ) , m ∘ pr₁) , λ (b , b-in-P)
   → (is-an-upper-bound-for L of ((Σ a ꞉ A , a ∈ Q ) , m ∘ pr₁))
    (b , C b b-in-P))

\end{code}

We now show if a type is small and has a map to the carrier then it has a join.
This seems like strict requirement but as we will see it occurs often when
considering a lattice with a basis. 

\begin{code}

module Small-Types-have-Joins {𝓤 𝓦 𝓥 𝓣 : Universe}
                              (L : Sup-Lattice 𝓤 𝓦 𝓥)
                              (T : 𝓣  ̇)
                              (m : T → ⟨ L ⟩)
                              (t : T is 𝓥 small)
                              where
 
 _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦
 _≤_ = order-of L

 ⋁_ : Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
 ⋁_ = join-for L

 small-type : 𝓥  ̇
 small-type = pr₁ t

 small-≃ : small-type ≃ T
 small-≃ = pr₂ t

 small-map : small-type → T
 small-map = ⌜ small-≃ ⌝

 is-equiv-small-map : is-equiv small-map
 is-equiv-small-map = pr₂ small-≃

 small-map-inv : T → small-type
 small-map-inv =  ⌜ small-≃ ⌝⁻¹

 has-section-small-map : has-section small-map
 has-section-small-map = pr₁ is-equiv-small-map

 is-section-small-map : is-section small-map
 is-section-small-map = pr₂ is-equiv-small-map

 section-small-map : small-map ∘ small-map-inv ∼ id
 section-small-map = pr₂ has-section-small-map

 retraction-small-map : small-map-inv ∘ small-map ∼ id
 retraction-small-map = inverses-are-retractions' small-≃

 small-type-inclusion : small-type → ⟨ L ⟩
 small-type-inclusion = m ∘ small-map

 s : ⟨ L ⟩
 s = ⋁ (small-type , small-type-inclusion)

 open Joins _≤_

 is-lub-of-both : (s is-lub-of ((T , m))) holds
 is-lub-of-both = (s-upper-bound , s-least-upper-bound)
  where
   s-upper-bound : (s is-an-upper-bound-of (T , m)) holds
   s-upper-bound t = t-≤-s
    where
     t-≤-s : (m t ≤ s) holds 
     t-≤-s = transport (λ z → (m z ≤ s) holds) (section-small-map t)
                       ((is-an-upper-bound-for L of
                        (small-type , small-type-inclusion)) (small-map-inv t))
   s-least-upper-bound : ((u , _) : upper-bound (T , m)) → (s ≤ u) holds
   s-least-upper-bound (u , is-upbnd-T) = s-≤-u
    where
     s-≤-u : (s ≤ u) holds
     s-≤-u = pr₂ (is-lub-for L (small-type , small-type-inclusion))
                 ((u , λ i → is-upbnd-T (small-map i)))

\end{code}

We also quickly show that the joins of equivalent types can be identified.
This will prove useful in the coming section.

\begin{code}

module Equivalent-Families-have-same-Join {𝓤 𝓦 𝓥 𝓣 𝓣' : Universe}
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

 ≃-families-＝-sup : (s s' : ⟨ L ⟩)
                   → (s is-lub-of (T , m)) holds
                   → (s' is-lub-of (T' , m ∘ ⌜ e ⌝ )) holds
                   → s ＝ s'
 ≃-families-＝-sup s s' (is-upbnd , is-least-upbnd)
                        (is-upbnd' , is-least-upbnd') =
   is-antisymmetric-for L s-≤-s' s'-≤-s
  where
   s-≤-s' : (s ≤ s') holds
   s-≤-s' = is-least-upbnd (s' , λ t → transport (λ z → (z ≤ s') holds)
                           (＝₁ t) (is-upbnd' (⌜ e ⌝⁻¹ t)))
    where
     ＝₁ : (t : T) → m (⌜ e ⌝ (⌜ e ⌝⁻¹ t)) ＝ m t
     ＝₁ t = ap m (naive-inverses-are-sections ⌜ e ⌝ (pr₂ e) t)
   s'-≤-s : (s' ≤ s) holds
   s'-≤-s = is-least-upbnd' (s , λ t' → is-upbnd (⌜ e ⌝ t'))

\end{code}

We can weaken the above result and simply require a surjection between families.

\begin{code}

module Surjection-implies-equal-joins {𝓤 𝓦 𝓥 𝓣 𝓣' : Universe}
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

 ↠-families-＝-sup : (s s' : ⟨ L ⟩)
                   → (s is-lub-of (T , m)) holds
                   → (s' is-lub-of (T' , m ∘ ⌞ e ⌟)) holds
                   → s ＝ s'
 ↠-families-＝-sup s s' (is-upbnd , is-least-upbnd)
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

We now define a small basis for a Sup-Lattice. This consists of a type B in a
fixed universe and a map q from B to the carrier of the Sup-Lattice. In a sense
to be made precise the pair B and q generate the Sup-Lattice. This notion will
be integral in developing the rest of our theory.

\begin{code}

module Small-Basis {𝓤 𝓦 𝓥 : Universe}
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

 ↓ᴮ-inclusion : (x : ⟨ L ⟩) → ↓ᴮ x → ⟨ L ⟩
 ↓ᴮ-inclusion x = q ∘ pr₁

 is-small-basis : 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⁺  ̇
 is-small-basis = (x : ⟨ L ⟩)
                 → ((b : B) → ((q b ≤ x) holds) is 𝓥 small) ×
                   ((x is-lub-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds)

 module Small-Basis-Facts (h : is-small-basis) where

  ≤-is-small : (x : ⟨ L ⟩) (b : B) → ((q b ≤ x) holds) is 𝓥 small
  ≤-is-small x b = pr₁ (h x) b

  is-sup : (x : ⟨ L ⟩) → (x is-lub-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds
  is-sup x = pr₂ (h x)

  is-upper-bound-↓ : (x : ⟨ L ⟩)
                   → (x is-an-upper-bound-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds
  is-upper-bound-↓ x = pr₁ (is-sup x)

  is-least-upper-bound-↓ : (x : ⟨ L ⟩)
                         → ((u' , _) : upper-bound (↓ᴮ x , ↓ᴮ-inclusion x))
                         → (x ≤ u') holds
  is-least-upper-bound-↓ x = pr₂ (is-sup x)

  _≤ᴮ_ : (b : B) (x : ⟨ L ⟩) → 𝓥  ̇
  b ≤ᴮ x = pr₁ (≤-is-small x b)

  _≤ᴮ_-≃-_≤_ : {b : B} {x : ⟨ L ⟩} → (b ≤ᴮ x) ≃ ((q b) ≤ x) holds
  _≤ᴮ_-≃-_≤_ {b} {x} = pr₂ (≤-is-small x b)

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
  is-sup'ᴮ x = ≃-families-＝-sup
               x
               (⋁ (small-↓ᴮ x , small-↓ᴮ-inclusion x))
               (is-sup x)
               (is-lub-for L ((small-↓ᴮ x , small-↓ᴮ-inclusion x)))
   where
    open Equivalent-Families-have-same-Join L (↓ᴮ x)
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

Now it is time to define the least closed subset of an inductive definition.
We utilize the notion of Higher Inductive Type (HITs), since HIT's are not
supported in Type Topology we postulate the existence of such a type as well
as it's induction principle and work with it axiomatically.

\begin{code}

module Inductive-Definitions {𝓤 𝓦 𝓥 : Universe}
                             {B : 𝓥  ̇}
                             (L : Sup-Lattice 𝓤 𝓦 𝓥)
                             (q : B → ⟨ L ⟩)
                              where

 open Small-Basis L q
 open Joins _≤_

 module Ind-from-Small-Basis-Facts (h : is-small-basis) where

  open Small-Basis-Facts h

  record Inductively-Generated-Subset-Exists (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)): 𝓤ω
   where
   constructor
    inductively-generated-subset

   field
    Ind : B → 𝓤 ⊔ 𝓥 ⁺  ̇
    Ind-trunc : (b : B) → is-prop (Ind b)
    c-closed : (U : 𝓟 {𝓥} B)
             → ((b : B) → (b ∈ U → Ind b))
             → (b : B) → b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁))
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
                   → (g : (b ≤ᴮ (⋁ ((Σ x ꞉ B , U x holds) , q ∘ pr₁))))
                   → c-closed U f b g ∈ P b)
                  → ((a : ⟨ L ⟩)
                   → (b : B)
                   → (p : (b , a) ∈ ϕ)
                   → (f : (x : B) → (x ≤ᴮ a → Ind x))
                   → ((x : B) → (o : x ≤ᴮ a) → f x o ∈ P x)
                   → ϕ-closed a b p f ∈ P b)
                  → (b : B) → (i : Ind b) → i ∈ P b

  module Trunc-Ind-Def (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                       (ind-e : Inductively-Generated-Subset-Exists ϕ)
                        where

   open Inductively-Generated-Subset-Exists ind-e

   𝓘nd : 𝓟 {𝓤 ⊔ 𝓥 ⁺} B
   𝓘nd b = (Ind b , Ind-trunc b)

   𝓘nd-is-c-closed : (U : 𝓟 {𝓥} B)
                   → (U ⊆ 𝓘nd)
                   → (b : B) → b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁))
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
                  → (b : B) → (g : (b ≤ᴮ (⋁ ((Σ x ꞉ B , x ∈ U) , q ∘ pr₁))))
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
                  → (b : B) → (b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁)))
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
                   → ((b : B) → (b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁)))
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
       → (x : B) → x ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁))
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

We now consider a restricted calss of inductive definitions which we will call
local. Then we define an operator on local inductive definitions and prove
that it is monotone. Finally, we show that any monotone maps corresponds to
a monotone operator and local inductive definition. This result is essential
to showing the least fixed point theorem.

\begin{code}

module Local-Inductive-Definitions {𝓤 𝓦 𝓥 : Universe}
                                   {B : 𝓥  ̇}
                                   (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                   (q : B → ⟨ L ⟩)
                                    where

 open Small-Basis L q
 open Joins _≤_
 open Inductive-Definitions L q 

 module Local-from-Small-Basis-Facts (h : is-small-basis) where

  open PropositionalTruncation pt
  open Small-Basis-Facts h

  S : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → (a : ⟨ L ⟩) → 𝓤 ⊔ 𝓦 ⊔ 𝓥  ̇
  S ϕ a = Σ b ꞉ B , (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds

  S-monotone-ish : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                 → (x y : ⟨ L ⟩)
                 → (x ≤ y) holds
                 → S ϕ x
                 → S ϕ y
  S-monotone-ish ϕ x y o = f
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
                             → (s is-lub-of (S ϕ x , q ∘ pr₁)) holds
                             → (s' is-lub-of (S ϕ y , q ∘ pr₁)) holds
                             → (s ≤ s') holds
  S-has-sup-implies-monotone ϕ x y s s' o
                             (is-upbnd , is-least-upbnd)
                             (is-upbnd' , is-least-upbnd') =
     is-least-upbnd ((s' , f))
   where
    f : (s' is-an-upper-bound-of (S ϕ x , q ∘ pr₁)) holds
    f (b , e) = is-upbnd' (S-monotone-ish ϕ x y o ((b , e)))
        
  _is-local : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
  ϕ is-local = (a : ⟨ L ⟩) → S ϕ a is 𝓥 small

  module _ (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) (i : ϕ is-local) where
   
   S-small : (a : ⟨ L ⟩) → 𝓥  ̇
   S-small a = pr₁ (i a)

   S-small-≃ : (a : ⟨ L ⟩) → S-small a ≃ S ϕ a
   S-small-≃ a  = pr₂ (i a)

   S-small-map : (a : ⟨ L ⟩) → S-small a → S ϕ a
   S-small-map a = ⌜ S-small-≃ a ⌝

   S-small-map-inv : (a : ⟨ L ⟩) → S ϕ a → S-small a 
   S-small-map-inv a = ⌜ S-small-≃ a ⌝⁻¹

   S-small-monotone-ish : (x y : ⟨ L ⟩)
                        → (x ≤ y) holds
                        → S-small x
                        → S-small y
   S-small-monotone-ish x y o =
     S-small-map-inv y ∘ S-monotone-ish ϕ x y o ∘ S-small-map x

   Γ : ⟨ L ⟩ → ⟨ L ⟩
   Γ a = ⋁ (S-small a , q ∘ pr₁ ∘ S-small-map a)

   open Monotone-Endo-Maps L hiding (_≤_)

   Γ-is-monotone : Γ is-monotone
   Γ-is-monotone x y o = S-has-sup-implies-monotone ϕ x y (Γ x) (Γ y) o
                                                    Γ-x-is-sup Γ-y-is-sup
    where
     Γ-x-is-sup : (Γ x is-lub-of (S ϕ x , q ∘ pr₁)) holds
     Γ-x-is-sup = is-lub-of-both
      where
       open Small-Types-have-Joins L (S ϕ x) (q ∘ pr₁) (i x)       
     Γ-y-is-sup : (Γ y is-lub-of (S ϕ y , q ∘ pr₁)) holds
     Γ-y-is-sup = is-lub-of-both
      where
       open Small-Types-have-Joins L (S ϕ y) (q ∘ pr₁) (i y)

  open Monotone-Endo-Maps L hiding (_≤_)

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
      equiv-2 z = ⌜ prop-≃-≃-⇔ fe _≤ᴮ_-is-prop-valued ∥∥-is-prop ⌝⁻¹
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
    G : (x : ⟨ L ⟩) → (f x is-lub-of (S ϕ x , q ∘ pr₁)) holds 
    G x = (f-is-upbnd , f-is-least)
     where
      f-is-upbnd : (f x is-an-upper-bound-of (S ϕ x , q ∘ pr₁)) holds
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
      f-is-least : ((u , _) : upper-bound (S ϕ x , q ∘ pr₁)) → (f x ≤ u) holds
      f-is-least (u , is-upbnd) = (is-least-upper-boundᴮ (f x))
                                  (u , λ z → is-upbnd (⌜ equiv-1 x ⌝ z))
    H : (x : ⟨ L ⟩) → (Γ ϕ i) x ＝ f x
    H x = ≃-families-＝-sup ((Γ ϕ i) x) (f x) is-lub-of-both (G x)
     where
      open Equivalent-Families-have-same-Join L (S ϕ x) (S ϕ x)
                                              (id , id-is-equiv (S ϕ x))
                                              (q ∘ pr₁)
      open Small-Types-have-Joins L (S ϕ x) (q ∘ pr₁) (i x)

  ind-def-from-mono-map : (f : ⟨ L ⟩ → ⟨ L ⟩)
                        → f is-monotone
                        → 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)
  ind-def-from-mono-map f f-mono = pr₁ (mono-map-give-local-ind-def f f-mono)

  local-from-mono-map : (f : ⟨ L ⟩ → ⟨ L ⟩)
                      → (f-mono : f is-monotone)
                      → (ind-def-from-mono-map f f-mono) is-local
  local-from-mono-map f f-mono = pr₁ (pr₂ (mono-map-give-local-ind-def f f-mono))

  f-＝-Γ-from-mono-map : (f : ⟨ L ⟩ → ⟨ L ⟩)
                       → (f-mono : f is-monotone)
                       → (x : ⟨ L ⟩)
                       → (Γ (ind-def-from-mono-map f f-mono)
                            (local-from-mono-map f f-mono)) x ＝ f x
  f-＝-Γ-from-mono-map f f-mono =
    pr₂ (pr₂ (mono-map-give-local-ind-def f f-mono))

\end{code}

We now spell out a correspondence between small 'closed' subsets and
deflationary points in our lattice. This will allow us to show that monotone
operators have a least fixed point under certain smallness assumpions.

\begin{code}

module Correspondance-small-ϕ-closed-types-def-points {𝓤 𝓦 𝓥 : Universe}
                                                      {B : 𝓥  ̇}
                                                      (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                                      (q : B → ⟨ L ⟩)
                                                       where

 open Small-Basis L q
 open Joins _≤_
 open Inductive-Definitions L q
 open Local-Inductive-Definitions L q

 module Correspondance-from-Small-Basis-Facts (h : is-small-basis) where

  open PropositionalTruncation pt
  open Small-Basis-Facts h
  open Ind-from-Small-Basis-Facts h
  open Local-from-Small-Basis-Facts h

  module Correspondance-from-Locally-Small-ϕ (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                                             (i : ϕ is-local)
                                              where

   _is-small-ϕ-closed-subset : (P : 𝓟 {𝓥} B) → 𝓤 ⊔ (𝓥 ⁺)  ̇
   P is-small-ϕ-closed-subset = ((U : 𝓟 {𝓥} B)
                               → (U ⊆ P)
                               → ((b : B)
                               → (b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁)))
                               →  b ∈ P))
                              × ((a : ⟨ L ⟩)
                               → (b : B)
                               → ((b , a) ∈ ϕ)
                               → ((b' : B) → (b' ≤ᴮ a → b' ∈ P)) → b ∈ P)

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
                                     → (U ⊆ subset-of-small-ϕ-closed-subset X)
                                     → ((b : B)
                                     → (b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁)))
                                     →  b ∈ subset-of-small-ϕ-closed-subset X))
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
     sup-P = ⋁ ((Σ b ꞉ B , b ∈ P) , q ∘ pr₁)
     open Subsets-Order-Joins L B q hiding (⋁_ ; _≤_)
     is-non-inc : sup-P is-non-inc
     is-non-inc = Γ-is-least-upper-bound (sup-P , is-upper-bound)
      where
       open Small-Types-have-Joins L (S ϕ sup-P) (q ∘ pr₁) (i sup-P)
                                   hiding (⋁_ ; _≤_)
       Γ-is-sup : ((Γ ϕ i) sup-P is-lub-of (S ϕ sup-P , q ∘ pr₁)) holds
       Γ-is-sup = is-lub-of-both
       Γ-is-least-upper-bound : ((u , _) : upper-bound (S ϕ sup-P , q ∘ pr₁))
                              → ((Γ ϕ i) sup-P ≤ u) holds
       Γ-is-least-upper-bound = pr₂ Γ-is-sup
       b-in-P-to-b-≤-sup-P : (b : B) → b ∈ P → (q(b) ≤ sup-P) holds
       b-in-P-to-b-≤-sup-P b b-in-P =
         (is-an-upper-bound-for L of ((Σ b ꞉ B , b ∈ P) , q ∘ pr₁)) (b , b-in-P)
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
     sup-Q x = ⋁ ((Σ b ꞉ B , b ∈ Q x) , q ∘ pr₁)
     _＝-sup-Q : (x : ⟨ L ⟩) → x ＝ sup-Q x
     x ＝-sup-Q = is-sup'ᴮ x
     open Subsets-Order-Joins L B q hiding (_≤_ ; ⋁_)
     c-closed : (U : 𝓟 {𝓥} B)
              → (U ⊆ Q a)
              → ((b : B) → (b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁))) →  b ∈ Q a)
     c-closed U C b o = _≤_-to-_≤ᴮ_ (is-transitive-for L (q b)
                                    (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁))
                                    a
                                    (_≤ᴮ_-to-_≤_ o)
                                    (transport (λ z → ((⋁ ((Σ b ꞉ B , b ∈ U) ,
                                      q ∘ pr₁)) ≤ z) holds)
                                               (a ＝-sup-Q ⁻¹)
                                               (joins-preserve-containment {U}
                                                                     {Q a} C)))
     ϕ-closed : (a' : ⟨ L ⟩)
              → (b : B)
              → ((b , a') ∈ ϕ)
              → ((b' : B) → (b' ≤ᴮ a' → b' ∈ Q a)) → b ∈ Q a
     ϕ-closed a' b p f = trunc-map b ∣ (a' , p , a'-≤-a) ∣
      where
       open Small-Types-have-Joins L (S ϕ a) (q ∘ pr₁) (i a)
                                   hiding (⋁_ ; _≤_)
       Γ-is-sup : ((Γ ϕ i) a is-lub-of (S ϕ a , q ∘ pr₁)) holds
       Γ-is-sup = is-lub-of-both
       Γ-an-upper-bound :
         ((Γ ϕ i) a is-an-upper-bound-of (S ϕ a , q ∘ pr₁)) holds
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
           P'-to-P = c-closed P (λ z → id) x
           P-to-P' : x ∈ P → x ≤ᴮ sup-P
           P-to-P' r = _≤_-to-_≤ᴮ_ ((is-an-upper-bound-for L of
                                    ((Σ b ꞉ B , b ∈ P) , q ∘ pr₁)) (x , r))
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

   module Small-𝓘nd-from-exists (ind-e : Inductively-Generated-Subset-Exists ϕ)
                                 where

    open Inductively-Generated-Subset-Exists ind-e
    open Trunc-Ind-Def ϕ ind-e

    module Smallness-Assumption (j : (b : B) → (b ∈ 𝓘nd) is 𝓥 small) where

     small-𝓘 : (b : B) →  𝓥  ̇
     small-𝓘 b = pr₁ (j b) 

     small-𝓘-≃-𝓘nd : (b : B) → small-𝓘 b ≃ b ∈ 𝓘nd 
     small-𝓘-≃-𝓘nd b = pr₂ (j b)

     small-𝓘-to-𝓘nd : (b : B) → small-𝓘 b → b ∈ 𝓘nd
     small-𝓘-to-𝓘nd b = ⌜ small-𝓘-≃-𝓘nd b ⌝

     𝓘nd-to-small-𝓘 : (b : B) → b ∈ 𝓘nd → small-𝓘 b
     𝓘nd-to-small-𝓘 b = ⌜ small-𝓘-≃-𝓘nd b ⌝⁻¹

     small-𝓘-is-prop-valued : {b : B} → is-prop (small-𝓘 b)
     small-𝓘-is-prop-valued {b} = equiv-to-prop (small-𝓘-≃-𝓘nd b) (Ind-trunc b)

     𝓘-is-small-subset : 𝓟 {𝓥} B
     𝓘-is-small-subset = λ b → (small-𝓘 b , small-𝓘-is-prop-valued)

     small-𝓘-is-c-closed : (U : 𝓟 {𝓥} B)
                         → U ⊆ 𝓘-is-small-subset
                         → (b : B) → b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁))
                         → b ∈ 𝓘-is-small-subset
     small-𝓘-is-c-closed U C b o =
       𝓘nd-to-small-𝓘 b (𝓘nd-is-c-closed U (λ x → small-𝓘-to-𝓘nd x ∘ C x) b o)
      
     small-𝓘-is-ϕ-closed : (a : ⟨ L ⟩)
                         → (b : B)
                         → (b , a) ∈ ϕ
                         → ((b' : B) → b' ≤ᴮ a → b' ∈ 𝓘-is-small-subset)
                         → b ∈ 𝓘-is-small-subset
     small-𝓘-is-ϕ-closed a b p f =
       𝓘nd-to-small-𝓘 b (𝓘nd-is-ϕ-closed a b p
                         (λ b' → small-𝓘-to-𝓘nd b' ∘ f b'))

     total-space-𝓘-is-small : (Σ b ꞉ B , b ∈ 𝓘nd) is 𝓥 small
     total-space-𝓘-is-small = ((Σ b ꞉ B , small-𝓘 b) ,
                               Σ-cong λ b → small-𝓘-≃-𝓘nd b)
   
     e : (Σ b ꞉ B , small-𝓘 b) ≃ (Σ b ꞉ B , b ∈ 𝓘nd)
     e = pr₂ total-space-𝓘-is-small

     sup-𝓘 : ⟨ L ⟩
     sup-𝓘 = ⋁ ((Σ b ꞉ B , small-𝓘 b) , q ∘ pr₁ ∘ ⌜ e ⌝)

     sup-𝓘-is-lub : (sup-𝓘 is-lub-of ((Σ b ꞉ B , b ∈ 𝓘nd) , q ∘ pr₁)) holds
     sup-𝓘-is-lub = is-lub-of-both
      where
       open Small-Types-have-Joins L (Σ b ꞉ B , b ∈ 𝓘nd)
                                   (q ∘ pr₁) total-space-𝓘-is-small

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
                      (𝓘-is-small-subset , small-𝓘-is-c-closed ,
                       small-𝓘-is-ϕ-closed))
       sup-≤-Γ-sup : (sup-𝓘 ≤ (Γ ϕ i) sup-𝓘) holds
       sup-≤-Γ-sup = transport (λ z → (sup-𝓘 ≤ z) holds)
                               sup-Q-＝-Γ-sup sup-𝓘-≤-sup-Q
        where
         open Subsets-Order-Joins L B q hiding (_≤_ ; ⋁_)
         Γ-Γ-sup-≤-Γ-sup : ((Γ ϕ i) ((Γ ϕ i) sup-𝓘) ≤ (Γ ϕ i) sup-𝓘) holds
         Γ-Γ-sup-≤-Γ-sup = Γ-is-monotone ϕ i ((Γ ϕ i) sup-𝓘) sup-𝓘 Γ-sup-≤-sup
         Q-Γ-sup : 𝓟 {𝓥} B
         Q-Γ-sup = subset-of-small-ϕ-closed-subset
                    (non-inc-points-to-small-ϕ-closed-subsets
                     ((Γ ϕ i) sup-𝓘 , Γ-Γ-sup-≤-Γ-sup))
         Q-is-c-closed : (U : 𝓟 {𝓥} B)
                       → (U ⊆ Q-Γ-sup)
                       → ((b : B)
                       → (b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁)))
                       →  b ∈ Q-Γ-sup)
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
         𝓘-is-small-subset-⊆-Q-Γ-sup : 𝓘-is-small-subset ⊆ Q-Γ-sup
         𝓘-is-small-subset-⊆-Q-Γ-sup =
           λ z → 𝓘nd-⊆-Q-Γ-sup z ∘ small-𝓘-to-𝓘nd z
         sup-Q : ⟨ L ⟩
         sup-Q = ⋁ ((Σ b ꞉ B , b ∈ Q-Γ-sup) , q ∘ pr₁)
         sup-𝓘-≤-sup-Q : (sup-𝓘 ≤ sup-Q) holds
         sup-𝓘-≤-sup-Q =
           joins-preserve-containment {𝓘-is-small-subset}
                                      {Q-Γ-sup}
                                      𝓘-is-small-subset-⊆-Q-Γ-sup
         sup-Q-＝-Γ-sup : sup-Q ＝ (Γ ϕ i) sup-𝓘
         sup-Q-＝-Γ-sup = is-sup'ᴮ ((Γ ϕ i) sup-𝓘) ⁻¹
       sup-𝓘-≤ : (a : ⟨ L ⟩) → ((Γ ϕ i) a ＝ a) → (sup-𝓘 ≤ a) holds
       sup-𝓘-≤ a p = transport (λ z → (sup-𝓘 ≤ z) holds)
                               sup-P-＝-a
                               sup-𝓘-≤-sup-P
        where
         open Subsets-Order-Joins L B q hiding (_≤_ ; ⋁_)
         Γ-a-≤-a : ((Γ ϕ i) a ≤ a) holds
         Γ-a-≤-a = transport (λ z → ((Γ ϕ i) a ≤ z) holds)
                             p (is-reflexive-for L ((Γ ϕ i) a))
         P-a : 𝓟 {𝓥} B
         P-a = subset-of-small-ϕ-closed-subset
                (non-inc-points-to-small-ϕ-closed-subsets (a , Γ-a-≤-a))
         P-is-c-closed : (U : 𝓟 {𝓥} B)
                       → (U ⊆ P-a)
                       → ((b : B)
                       → (b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁)))
                       →  b ∈ P-a)
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
         𝓘-is-small-subset-⊆-P-a : 𝓘-is-small-subset ⊆ P-a
         𝓘-is-small-subset-⊆-P-a = λ z → 𝓘nd-⊆-P-a z ∘ small-𝓘-to-𝓘nd z
         sup-P : ⟨ L ⟩
         sup-P = ⋁ ((Σ b ꞉ B , b ∈ P-a) , q ∘ pr₁)
         sup-𝓘-≤-sup-P : (sup-𝓘 ≤ sup-P) holds
         sup-𝓘-≤-sup-P = joins-preserve-containment
                          {𝓘-is-small-subset}
                          {P-a}
                          𝓘-is-small-subset-⊆-P-a
         sup-P-＝-a : sup-P ＝ a
         sup-P-＝-a = is-sup'ᴮ a ⁻¹

\end{code}

We now consider a boundedness restricion on inductive definitions and show
that bounded inductive definitions are local. An inductive definition is
bounded if there is a small indexed family of types that can be substituted
for elements a : L in a sense to be made precise below.

\begin{code}

module Bounded-Inductive-Definition {𝓤 𝓦 𝓥 : Universe}
                                    {B : 𝓥  ̇}
                                    (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                    (q : B → ⟨ L ⟩)
                                     where

 open Small-Basis L q
 open Joins _≤_

 module Bounded-from-Small-Basis-Facts (h : is-small-basis) where

  open Small-Basis-Facts h
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

  open Local-Inductive-Definitions L q
  open Local-from-Small-Basis-Facts h

  _bounded-implies-local : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                         → ϕ is-bounded
                         → ϕ is-local
  (ϕ bounded-implies-local) (ϕ-small , ϕ-has-bound) a =
    smallness-closed-under-≃ small-type-is-small small-type-≃-S
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
    small-type : 𝓤 ⊔ 𝓦 ⊔ 𝓥  ̇
    small-type = Σ b ꞉ B , ((Ǝ i ꞉ I , ((Ǝ m ꞉ (α i → ↓ᴮ a) ,
                  ((b , (⋁ (α i , q ∘ pr₁ ∘ m))) ∈ ϕ)) holds)) holds)
    small-type-is-small : small-type is 𝓥 small
    small-type-is-small =
     Σ-is-small (B , ≃-refl B)
                (λ b → ∥∥-is-small pt (Σ-is-small (I , ≃-refl I)
                       λ i → ∥∥-is-small pt
                             (Σ-is-small (Π-is-small (fe') (α i , ≃-refl (α i))
                             λ _ → ↓ᴮ-is-small)
                                   λ m → ϕ-small (⋁ (α i , q ∘ pr₁ ∘ m)) b)))

    small-type-to-S : small-type → S ϕ a
    small-type-to-S (b , e) = (b , map₄ e)
     where
      map₁ : (i : I)
           → (Σ m ꞉ (α i → ↓ᴮ a) , ((b , (⋁ (α i , q ∘ pr₁ ∘ m))) ∈ ϕ))
           → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
      map₁ i (m , p) =
        ∣ (⋁ (α i , q ∘ pr₁ ∘ m) , p ,
          (is-least-upper-bound-for L of (α i , q ∘ pr₁ ∘ m))
                                         (a , λ z → is-upper-bound-↓ a (m z))) ∣
      map₂ : (i : I)
           → ((Ǝ m ꞉ (α i → ↓ᴮ a) , ((b , (⋁ (α i , q ∘ pr₁ ∘ m))) ∈ ϕ)) holds)
           → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
      map₂ i = ∥∥-rec ∥∥-is-prop (map₁ i)
      map₃ : Σ i ꞉ I , ((Ǝ m ꞉ (α i → ↓ᴮ a) ,
              ((b , (⋁ (α i , q ∘ pr₁ ∘ m))) ∈ ϕ)) holds)
           → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
      map₃ = uncurry map₂
      map₄ : (Ǝ i ꞉ I , ((Ǝ m ꞉ (α i → ↓ᴮ a) ,
              ((b , (⋁ (α i , q ∘ pr₁ ∘ m))) ∈ ϕ)) holds)) holds
           → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
      map₄ = ∥∥-rec ∥∥-is-prop map₃

    S-to-small-type : S ϕ a → small-type
    S-to-small-type (b , e) = (b , map₄ e)
     where
      ι : (a' : ⟨ L ⟩) → (a' ≤ a) holds → ↓ᴮ a' → ↓ᴮ a
      ι a' o (x , r) = (x , is-transitive-for L (q x) a' a r o)
      map₁ : (a' : ⟨ L ⟩)
           →  (b , a') ∈ ϕ
           → (a' ≤ a) holds
           → (Σ i ꞉ I , (α i is-a-small-cover-of ↓ᴮ a'))
           → (Ǝ i ꞉ I , ((Ǝ m ꞉ (α i → ↓ᴮ a) ,
               ((b , (⋁ (α i , q ∘ pr₁ ∘ m))) ∈ ϕ)) holds)) holds
      map₁ a' p o (i , α-covers) = ∣ (i , ∣ (m , p') ∣) ∣
       where
        open Surjection-implies-equal-joins L (↓ᴮ a') (α i)
                                              α-covers (q ∘ pr₁)
                                               hiding (⋁_ ; _≤_)
        m : α i → ↓ᴮ a
        m = ι a' o ∘ ⌞  α-covers ⌟
        path : a' ＝ ⋁ (α i , q ∘ pr₁ ∘ m)
        path = ↠-families-＝-sup a' (⋁ (α i , q ∘ pr₁ ∘ m)) (is-sup a')
                                 (is-lub-for L (α i , q ∘ pr₁ ∘ m))
        p' : (b , (⋁ (α i , q ∘ pr₁ ∘ m))) ∈ ϕ
        p' = transport (λ z → (b , z) ∈ ϕ) path p
      map₂ : (a' : ⟨ L ⟩)
           → (b , a') ∈ ϕ
           → (a' ≤ a) holds
           → (Ǝ i ꞉ I , (α i is-a-small-cover-of ↓ᴮ a')) holds
           → (Ǝ i ꞉ I , ((Ǝ m ꞉ (α i → ↓ᴮ a) ,
              ((b , (⋁ (α i , q ∘ pr₁ ∘ m))) ∈ ϕ)) holds)) holds
      map₂ a' p o = ∥∥-rec ∥∥-is-prop (map₁ a' p o)
      map₃ : Σ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds
           → (Ǝ i ꞉ I , ((Ǝ m ꞉ (α i → ↓ᴮ a) ,
              ((b , (⋁ (α i , q ∘ pr₁ ∘ m))) ∈ ϕ)) holds)) holds
      map₃ (a' , p , o) = map₂ a' p o (cov a' b p)
      map₄ : (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
           → (Ǝ i ꞉ I , ((Ǝ m ꞉ (α i → ↓ᴮ a) ,
              ((b , (⋁ (α i , q ∘ pr₁ ∘ m))) ∈ ϕ)) holds)) holds
      map₄ = ∥∥-rec ∥∥-is-prop map₃

    small-type-≃-S : small-type ≃ S ϕ a
    small-type-≃-S =
      (small-type-to-S , qinvs-are-equivs small-type-to-S is-qinv)
     where
      H : S-to-small-type ∘ small-type-to-S ∼ id
      H (b , e) = to-subtype-＝ (λ _ → ∥∥-is-prop) refl
      G : small-type-to-S ∘ S-to-small-type ∼ id
      G (b , e) = to-subtype-＝ (λ _ → ∥∥-is-prop) refl
      is-qinv : qinv small-type-to-S
      is-qinv = (S-to-small-type , H , G)

\end{code}

We now consider a stronger restriction on Sup-Lattices. A Sup-Lattice has a
small presentation if there is a small indexed family of subsets that can be
substituted for arbitrary subsets in a sense to be made precise below.

\begin{code}

module Small-Presentation-of-Lattice {𝓤 𝓦 𝓥 : Universe}
                                     {B : 𝓥  ̇}
                                     (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                     (q : B → ⟨ L ⟩)
                                      where

 open Small-Basis L q
 open Joins _≤_

 module Small-Presentation-from-Small-Basis-Facts (h : is-small-basis) where

  open Small-Basis-Facts h
  open PropositionalTruncation pt

  _is-a-small-presentation : Σ J ꞉ 𝓥  ̇ , (J → 𝓟 {𝓥} B) × 𝓟 {𝓥} (B × 𝓟 {𝓥} B)
                           → (𝓥 ⁺)  ̇
  (J , Y , R) is-a-small-presentation = (b : B)
                                      → (X : 𝓟 {𝓥} B)
                                      → b ≤ᴮ (⋁ ((Σ x ꞉ B , x ∈ X) , q ∘ pr₁))
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

module Small-QIT {𝓤 𝓦 𝓥 : Universe}
                 {B : 𝓥  ̇}
                 (L : Sup-Lattice 𝓤 𝓦 𝓥)
                 (q : B → ⟨ L ⟩)
                  where

 open Small-Basis L q
 open Bounded-Inductive-Definition L q
 open Small-Presentation-of-Lattice L q

 module Small-QIT-from-Small-Basis-Facts (h : is-small-basis) where
 
  open Small-Basis-Facts h
  open Bounded-from-Small-Basis-Facts h
  open Small-Presentation-from-Small-Basis-Facts h
 
  module Small-QIT-from-Bounded-and-Small-Presentation
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
                         → b ≤ᴮ (⋁ ((Σ x ꞉ B , x ∈ X) , q ∘ pr₁))
                         → ((Ǝ j ꞉ I₁ , Y j ⊆ X × (b , Y j) ∈ R) holds)
   is-small-pres-forward b X = ⌜ is-small-pres b X ⌝

   is-small-pres-backward : (b : B)
                          → (X : 𝓟 {𝓥} B)
                          → ((Ǝ j ꞉ I₁ , Y j ⊆ X × (b , Y j) ∈ R) holds)
                          → b ≤ᴮ (⋁ ((Σ x ꞉ B , x ∈ X) , q ∘ pr₁))
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

   record Inductively-Generated-Small-Subset-Exists : 𝓤ω where
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

   module Small-Trunc-Ind-Def
     (ind-e : Inductively-Generated-Small-Subset-Exists)
      where

    open Inductively-Generated-Small-Subset-Exists ind-e

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

\begin{code}

module 𝓘nd-is-small {𝓤 𝓦 𝓥 : Universe}
                    {B : 𝓥  ̇}
                    (L : Sup-Lattice 𝓤 𝓦 𝓥)
                    (q : B → ⟨ L ⟩)
                     where

 open Small-Basis L q
 open Bounded-Inductive-Definition L q
 open Small-Presentation-of-Lattice L q
 open Inductive-Definitions L q
 open Small-QIT L q

 module 𝓘nd-is-small-from-Small-Basis-Facts (h : is-small-basis) where
 
  open Small-Basis-Facts h
  open Bounded-from-Small-Basis-Facts h
  open Small-Presentation-from-Small-Basis-Facts h
  open Ind-from-Small-Basis-Facts h
  open Small-QIT-from-Small-Basis-Facts h
 
  module 𝓘nd-is-small-from-Bounded-and-Small-Presentation
    (small-pres : has-small-presentation)
    (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
    (bnd : ϕ is-bounded)
     where

   open Small-QIT-from-Bounded-and-Small-Presentation small-pres ϕ bnd

   module 𝓘nd-is-small-QITs-exists
    (ind-e : Inductively-Generated-Subset-Exists ϕ)
    (ind-e' : Inductively-Generated-Small-Subset-Exists)
     where

    open Trunc-Ind-Def ϕ ind-e
    open Small-Trunc-Ind-Def ind-e'
    open PropositionalTruncation pt

    𝓘nd-⊆-Small-𝓘nd : 𝓘nd ⊆ Small-𝓘nd
    𝓘nd-⊆-Small-𝓘nd = 𝓘nd-is-initial Small-𝓘nd f g
     where
      f : (U : 𝓟 {𝓥} B)
        → U ⊆ Small-𝓘nd
        → (b : B)
        → b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁))
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
         Small-𝓘nd-is-ϕ-cl i (pr₁ ∘ ⌞ s ⌟) b
                           (ϕ-is-small-backward (⋁ (α i , q ∘ pr₁ ∘ ⌞ s ⌟))
                                                b
                                                (transport (λ a' → (b , a') ∈ ϕ)
                                                           (a-＝-⋁-α) p))
                                                (λ b' → C b'
                                                  ∘ (transport (λ a'
                                                    → b' ≤ᴮ a') (a-＝-⋁-α ⁻¹))) 
         where
          open Surjection-implies-equal-joins L (↓ᴮ a) (α i)
                                              s (q ∘ pr₁) hiding (⋁_)
          a-＝-⋁-α : a ＝ ⋁ (α i , q ∘ pr₁ ∘ ⌞ s ⌟)
          a-＝-⋁-α =
            ↠-families-＝-sup a (⋁ (α i , q ∘ pr₁ ∘ ⌞ s ⌟)) (is-sup a)
                              (is-lub-for L (α i , q ∘ pr₁ ∘ ⌞ s ⌟))
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
fixed point theorem.

\begin{code}

module Least-Fixed-Point {𝓤 𝓦 𝓥 : Universe}
                         {B : 𝓥  ̇}
                         (L : Sup-Lattice 𝓤 𝓦 𝓥)
                         (q : B → ⟨ L ⟩)
                          where

 open Small-Basis L q 
 open Bounded-Inductive-Definition L q
 open Small-Presentation-of-Lattice L q
 open Correspondance-small-ϕ-closed-types-def-points L q
 open Inductive-Definitions L q
 open Small-QIT L q
 open Local-Inductive-Definitions L q
 open Monotone-Endo-Maps L hiding (_≤_)
 open 𝓘nd-is-small L q

 module Least-Fixed-Point-from-Small-Basis-Facts (h : is-small-basis) where

  open Small-Basis-Facts h
  open Bounded-from-Small-Basis-Facts h
  open Small-Presentation-from-Small-Basis-Facts h
  open Correspondance-from-Small-Basis-Facts h
  open Ind-from-Small-Basis-Facts h
  open Small-QIT-from-Small-Basis-Facts h
  open Local-from-Small-Basis-Facts h
  open 𝓘nd-is-small-from-Small-Basis-Facts h

  Least-Fixed-Point-Theorem : (small-pres : has-small-presentation)
                            → (f : ⟨ L ⟩ → ⟨ L ⟩)
                            → (f-mono : f is-monotone)
                            → (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                            → (bnd : ϕ is-bounded)
                            → ((x : ⟨ L ⟩)
                             → (Γ ϕ ((ϕ bounded-implies-local) bnd)) x ＝ f x)
                            → (ind-e : Inductively-Generated-Subset-Exists ϕ)
                            → (ind-e' :
   Small-QIT-from-Bounded-and-Small-Presentation.Inductively-Generated-Small-Subset-Exists
                                        small-pres ϕ bnd)
                            → Σ x ꞉ ⟨ L ⟩ ,
                               (f x ＝ x) × ((a : ⟨ L ⟩)
                                          → (f a ＝ a)
                                          → (x ≤ a) holds)
  Least-Fixed-Point-Theorem small-pres f f-mono ϕ bnd H ind-e ind-e' =
    transport (λ g → Σ x ꞉ ⟨ L ⟩ , (g x ＝ x) × ((a : ⟨ L ⟩)
                                              → (g a ＝ a)
                                              → (x ≤ a) holds))
              path Γ-has-least-fixed-point
   where
    open Correspondance-from-Locally-Small-ϕ ϕ ((ϕ bounded-implies-local) bnd)
    open Small-𝓘nd-from-exists ind-e
    open 𝓘nd-is-small-from-Bounded-and-Small-Presentation small-pres ϕ bnd
    open Small-QIT-from-Bounded-and-Small-Presentation small-pres ϕ bnd
    open 𝓘nd-is-small-QITs-exists ind-e ind-e'
    open Smallness-Assumption 𝓘nd-is-small
    path : Γ ϕ ((ϕ bounded-implies-local) bnd)
         ＝ f
    path = dfunext fe H

\end{code}



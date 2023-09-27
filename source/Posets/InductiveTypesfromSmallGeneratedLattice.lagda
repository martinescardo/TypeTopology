Ian Ray 01/09/2023.

We formalize Curi's (CZF) notion of Abstract Inductive Definition from a Sup-Lattice L with small
basis B (and q : B → L). An abstract inductive defintion is a subset ϕ : L × B → Prop which can be
thought of as a 'inference rule'. Fortunately, induction rules are first class citizens in type
theory unlike CZF. Using the power of agda's data type constructor (which is justified by inductive
types in book HoTT) we can automatically construct the least ϕ-closed subset given ϕ. We open this
file by defining Sup-Lattices.

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
open import UF.Retracts
open import UF.UniverseEmbedding
open import UF.Equiv-FunExt

module Posets.InductiveTypesfromSmallGeneratedLattice (pt : propositional-truncations-exist)
                                                      (fe : Fun-Ext)
                                                      (pe : Prop-Ext)
                                                      where

open import Locales.Frame pt fe hiding (⟨_⟩)
open import Slice.Family

open AllCombinators pt fe

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

is-partial-order-for : (L : Sup-Lattice 𝓤 𝓦 𝓥) → is-partial-order ⟨ L ⟩ (order-of L)
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
                          → ((order-of L) Joins.is-an-upper-bound-of join-for L U) U holds
is-an-upper-bound-for L of U = pr₁ (is-lub-for L U)

is-least-upper-bound-for_of_ : (L : Sup-Lattice 𝓤 𝓦 𝓥)
                             → (U : Fam 𝓥 ⟨ L ⟩)
                             → ((u' , _) : Joins.upper-bound (order-of L) U) → (order-of L (join-for L U) u') holds
is-least-upper-bound-for L of U = pr₂ (is-lub-for L U)

\end{code}

We define a monotone endo-map on lattice. This is sufficient as our intent is to study fixed-points.

\begin{code}

module Monotone-Endo-Maps {𝓤 𝓦 𝓥 : Universe} (L : Sup-Lattice 𝓤 𝓦 𝓥) where

 _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦
 _≤_ = order-of L

 _is-monotone : (f : ⟨ L ⟩ → ⟨ L ⟩) → 𝓤 ⊔ 𝓦  ̇
 f is-monotone = (x y : ⟨ L ⟩) → (x ≤ y) holds → (f x ≤ f y) holds

\end{code}

We pause to introduce some universe polymorphic powerset notation this will allow us to develop results
in a notation familiar to set theorists.

\begin{code}

module Universe-Polymorphic-Powerset (𝓥 : Universe) where

   𝓟 : {𝓣 : Universe} → 𝓥  ̇ → 𝓥 ⊔ 𝓣 ⁺  ̇
   𝓟 {𝓣} X = X → Ω 𝓣

   _∈_ : {𝓣 : Universe} {X : 𝓥  ̇} → X → 𝓟 {𝓣} X → 𝓣  ̇
   x ∈ A = A x holds
   
   _⊆_ : {𝓣 𝓦 : Universe} {X : 𝓥  ̇} → 𝓟 {𝓣} X → 𝓟 {𝓦} X →  𝓥 ⊔ 𝓣 ⊔ 𝓦  ̇
   A ⊆ B = ∀ x → x ∈ A → x ∈ B

\end{code}

We now show that when one subset contains another the join of their total spaces are ordered as
expected. This result is a familar to set theorist...

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
 open Universe-Polymorphic-Powerset 𝓥

 joins-preserve-containment : {P : 𝓟 {𝓥} A} {Q : 𝓟 {𝓥} A}
                            → (C : P ⊆ Q)
                            → ((⋁ ((Σ a ꞉ A , a ∈ P) , m ∘ pr₁)) ≤ (⋁ ((Σ a ꞉ A , a ∈ Q ) , m ∘ pr₁))) holds
 joins-preserve-containment {P} {Q} C =
   (is-least-upper-bound-for L of ((Σ a ꞉ A , a ∈ P ) , m ∘ pr₁))
    (⋁ ((Σ a ꞉ A , a ∈ Q ) , m ∘ pr₁) , λ (b , b-in-P)
                                        → (is-an-upper-bound-for L of ((Σ a ꞉ A , a ∈ Q ) , m ∘ pr₁)) (b , C b b-in-P))

\end{code}

We take a quick detour to show if a type is small and has a map to the carrier then it has a join.
This seems like strict requirement but as we will see it occurs often when considering a lattice with a base. 

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
                       ((is-an-upper-bound-for L of (small-type , small-type-inclusion)) (small-map-inv t))
   s-least-upper-bound : ((u , _) : upper-bound (T , m)) → (s ≤ u) holds
   s-least-upper-bound (u , is-upbnd-T) = s-≤-u
    where
     s-≤-u : (s ≤ u) holds
     s-≤-u = pr₂ (is-lub-for L (small-type , small-type-inclusion))
                 ((u , λ i → is-upbnd-T (small-map i)))

\end{code}

We also quickly show when the join of equivalents types can be identified.
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
 ≃-families-＝-sup s s' (is-upbnd , is-least-upbnd) (is-upbnd' , is-least-upbnd') =
   is-antisymmetric-for L s-≤-s' s'-≤-s
  where
   s-≤-s' : (s ≤ s') holds
   s-≤-s' = is-least-upbnd (s' , λ t → transport (λ z → (z ≤ s') holds) (＝-1 t) (is-upbnd' (⌜ e ⌝⁻¹ t)))
    where
     ＝-1 : (t : T) → m (⌜ e ⌝ (⌜ e ⌝⁻¹ t)) ＝ m t
     ＝-1 t = ap m (naive-inverses-are-sections ⌜ e ⌝ (pr₂ e) t)
   s'-≤-s : (s' ≤ s) holds
   s'-≤-s = is-least-upbnd' (s , λ t' → is-upbnd (⌜ e ⌝ t'))

\end{code}

We now define a small basis for a Sup-Lattice. This consists of a type B in a fixed universe and a
map q from B to the carrier of the Sup-Lattice. In a sense to be made precise the pair B and q generate
the Sup-Lattice. This notion will be integral in developing the rest of our theory.

\begin{code}

module Sup-Lattice-Small-Basis {𝓤 𝓦 𝓥 : Universe} (L : Sup-Lattice 𝓤 𝓦 𝓥) where

 _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦
 _≤_ = order-of L

 ⋁_ : Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
 ⋁_ = join-for L

 open Joins _≤_

 module Small-Basis {B : 𝓥  ̇} (q : B → ⟨ L ⟩) where

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
   small-↓ᴮ-≃-↓ᴮ {x} = Σ-cong' P Q f
    where
     P : B → 𝓥  ̇
     P b = b ≤ᴮ x
     Q : B → 𝓦  ̇
     Q b = ((q b) ≤ x) holds
     f : (b : B) →  b ≤ᴮ x ≃ ((q b) ≤ x) holds
     f b = _≤ᴮ_-≃-_≤_ {b} {x}

   ↓ᴮ-is-small : {x : ⟨ L ⟩} → ↓ᴮ x is 𝓥 small
   ↓ᴮ-is-small {x} = (small-↓ᴮ x , small-↓ᴮ-≃-↓ᴮ {x})

   is-sup'ᴮ : (x : ⟨ L ⟩) → x ＝ ⋁ (small-↓ᴮ x , small-↓ᴮ-inclusion x)
   is-sup'ᴮ x = ≃-families-＝-sup x (⋁ (small-↓ᴮ x , small-↓ᴮ-inclusion x)) (is-sup x)
                                 (is-lub-for L ((small-↓ᴮ x , small-↓ᴮ-inclusion x)))
    where
     open Equivalent-Families-have-same-Join L (↓ᴮ x) (small-↓ᴮ x) small-↓ᴮ-≃-↓ᴮ (↓ᴮ-inclusion x) hiding (⋁_)

   is-supᴮ : (x : ⟨ L ⟩) → (x is-lub-of (small-↓ᴮ x , small-↓ᴮ-inclusion x)) holds
   is-supᴮ x = transport (λ z → (z is-lub-of (small-↓ᴮ x , small-↓ᴮ-inclusion x)) holds)
                         (is-sup'ᴮ x ⁻¹) (is-lub-for L ((small-↓ᴮ x , small-↓ᴮ-inclusion x)))

   is-upper-boundᴮ : (x : ⟨ L ⟩) → (x is-an-upper-bound-of (small-↓ᴮ x , small-↓ᴮ-inclusion x)) holds
   is-upper-boundᴮ x = pr₁ (is-supᴮ x)

   is-least-upper-boundᴮ : (x : ⟨ L ⟩)
                         → ((u' , _) : upper-bound (small-↓ᴮ x , small-↓ᴮ-inclusion x))
                         → (x ≤ u') holds
   is-least-upper-boundᴮ x = pr₂ (is-supᴮ x)

\end{code}

Now it is time to define the least closed subset of an inductive definition. We are currently exploring
an alternative approach to defining the least-closed subset as a Higher Inductive Type, since HIT's are not
supported in Type Topology we postulate the existence of such a type as well as it's induction principle
and work with it axiomatically.

\begin{code}

module Inductive-Definitions (𝓤 𝓦 𝓥 : Universe) (L : Sup-Lattice 𝓤 𝓦 𝓥) where

 open Sup-Lattice-Small-Basis L
 open Joins _≤_

 module Ind-Small-Basis {B : 𝓥  ̇} (q : B → ⟨ L ⟩) where

  open Small-Basis q

  module Ind-Basis-Facts (h : is-small-basis) where

   open Small-Basis-Facts h

   record Inductively-Generated-Subset-Exists (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)): 𝓤ω where
    constructor
     inductively-generated-subset

    field
     Ind : B → (𝓤 ⊔ 𝓥 ⁺)  ̇
     Ind-trunc : (b : B) → is-prop (Ind b)
     c-closed : (U : B → Ω 𝓥)
              → ((b : B) → ((U b) holds → Ind b))
              → (b : B) → b ≤ᴮ (⋁ ((Σ b ꞉ B , (U b) holds) , q ∘ pr₁))
              → Ind b
     ϕ-closed : (a : ⟨ L ⟩)
              → (b : B)
              → (ϕ (a , b)) holds
              → ((b' : B) → (b' ≤ᴮ a → Ind b'))
              → Ind b
     Ind-induction : (P : (b : B) → Ind b → Ω 𝓣)
                   → ((U : B → Ω 𝓥) → (f : (x : B) → (U x holds → Ind x))
                    → ((x : B) → (u : U x holds) → (P x (f x u)) holds)
                    → (b : B) → (g : (b ≤ᴮ (⋁ ((Σ x ꞉ B , U x holds) , q ∘ pr₁))))
                    → (P b (c-closed U f b g)) holds)
                   → ((a : ⟨ L ⟩)
                    → (b : B)
                    → (p : ϕ (a , b) holds)
                    → (f : (x : B) → (x ≤ᴮ a → Ind x))
                    → ((x : B) → (o : x ≤ᴮ a) → (P x (f x o)) holds)
                    → (P b (ϕ-closed a b p f)) holds)
                   → (b : B) → (i : Ind b) → (P b i) holds

   module Trun-Ind-Def (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)) (ind-e : Inductively-Generated-Subset-Exists ϕ) where

    open Inductively-Generated-Subset-Exists ind-e
    open Universe-Polymorphic-Powerset 𝓥

    𝓘nd : 𝓟 {𝓤 ⊔ 𝓥 ⁺} B
    𝓘nd b = (Ind b , Ind-trunc b)

    𝓘nd-is-c-closed : (U : 𝓟 {𝓥} B)
                    → (U ⊆ 𝓘nd)
                    → (b : B) → b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁))
                    → b ∈ 𝓘nd
    𝓘nd-is-c-closed = c-closed

    𝓘nd-is-ϕ-closed : (a : ⟨ L ⟩)
                    → (b : B)
                    → (ϕ (a , b)) holds
                    → ((b' : B) → (b' ≤ᴮ a → b' ∈ 𝓘nd))
                    → b ∈ 𝓘nd
    𝓘nd-is-ϕ-closed = ϕ-closed

    𝓘nd-induction : (P : (b : B) → b ∈ 𝓘nd → Ω 𝓣)
                  → ((U : 𝓟 {𝓥} B) → (f : U ⊆ 𝓘nd)
                   → ((x : B) → (u : x ∈ U) → (P x (f x u)) holds)
                   → (b : B) → (g : (b ≤ᴮ (⋁ ((Σ x ꞉ B , x ∈ U) , q ∘ pr₁))))
                   → (P b (c-closed U f b g)) holds)
                  → ((a : ⟨ L ⟩)
                   → (b : B)
                   → (p : ϕ (a , b) holds)
                   → (f : (x : B) → (x ≤ᴮ a → x ∈ 𝓘nd))
                   → ((x : B) → (o : x ≤ᴮ a) → (P x (f x o)) holds)
                   → (P b (ϕ-closed a b p f)) holds)
                  → (b : B) → (i : b ∈ 𝓘nd) → (P b i) holds
    𝓘nd-induction = Ind-induction

    𝓘nd-recursion : (P : 𝓟 {𝓣} B)
                  → ((U : 𝓟 {𝓥} B)
                   → (U ⊆ 𝓘nd)
                   → (U ⊆ P)
                   → (b : B) → (b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁)))
                   → b ∈ P)
                  → ((a : ⟨ L ⟩)
                   → (b : B)
                   → (ϕ (a , b) holds)
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
                    → (ϕ (a , b) holds)
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
        → ϕ (a , x) holds
        → ((z : B) → z ≤ᴮ a → z ∈ 𝓘nd)
        → ((z : B) → z ≤ᴮ a → z ∈ P)
        → x ∈ P
      S a x p f g = IH₂ a x p g


\end{code}

We leave this section in for now while we expirement with the new formulation. One could argue that
the existence of this section is in a small way a proof of concept. Although it fails due the truncation
not occuring simulataneously with the other constructors as the type is freely generated.

\begin{code}

   data I (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)) : B → (𝓤 ⊔ 𝓥 ⁺)  ̇ where
    c-cl : (U : B → Ω 𝓥)
         → ((b : B) → ((U b) holds → I ϕ b))
         → (b : B) → b ≤ᴮ (⋁ ((Σ b ꞉ B , (U b) holds) , q ∘ pr₁))
         → I ϕ b
    ϕ-cl : (a : ⟨ L ⟩)
         → (b : B)
         → (ϕ (a , b)) holds
         → ((b' : B) → (b' ≤ᴮ a → I ϕ b'))
         → I ϕ b

   I-induction : (P : {ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)} → (b : B) → I ϕ b → 𝓣  ̇)
               → {ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)}
               → ((U : B → Ω 𝓥) → (f : (x : B) → (U x holds → I ϕ x))
                → ((x : B) → (u : U x holds) → P x (f x u))
                → (b : B) → (g : (b ≤ᴮ (⋁ ((Σ x ꞉ B , U x holds) , q ∘ pr₁))))
                → P b (c-cl U f b g))
               → ((a : ⟨ L ⟩)
                → (b : B)
                → (p : ϕ (a , b) holds)
                → (f : (x : B) → (x ≤ᴮ a → I ϕ x))
                → ((x : B) → (o : x ≤ᴮ a) → P x (f x o))
                → P b (ϕ-cl a b p f))
               → (b : B) → (i : I ϕ b) → P b i
   I-induction P {ϕ} IH₁ IH₂ = θ
    where
     θ : (b : B) → (i : I ϕ b) → P b i
     θ b (c-cl U f .b g) = IH₁ U f r b g
      where
       r : (x : B) → (u : U x holds) → P x (f x u)
       r x u = θ x (f x u)
     θ b (ϕ-cl a .b p f) = IH₂ a b p f r
      where
       r : (x : B) → (o : x ≤ᴮ a) → P x (f x o)
       r x o = θ x (f x o)

   I-recursion : {ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)}
               → (P : B → 𝓣  ̇)
               → ((U : B → Ω 𝓥)
                → ((x : B) → (U x holds → I ϕ x))
                → ((x : B) → (U x holds → P x))
                → (b : B) → (b ≤ᴮ (⋁ ((Σ b ꞉ B , U b holds) , q ∘ pr₁)))
                → P b)
               → ((a : ⟨ L ⟩)
                → (b : B)
                → (ϕ (a , b) holds)
                → ((x : B) → (x ≤ᴮ a → I ϕ x))
                → ((x : B) → (x ≤ᴮ a → P x))
                → P b)
               → (b : B) → I ϕ b → P b
   I-recursion {ϕ} P = I-induction (λ b → (λ _ → P b))

   I-is-initial : {ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)}
                → (P : B → 𝓣  ̇)
                → ((U : B → Ω 𝓥)
                 → ((b : B) → (U b holds → P b))
                 → ((b : B) → (b ≤ᴮ (⋁ ((Σ b ꞉ B , U b holds) , q ∘ pr₁))) → P b))
                → ((a : ⟨ L ⟩)
                 → (b : B)
                 → (ϕ (a , b) holds)
                 → ((b' : B) → (b' ≤ᴮ a → P b')) → P b)
                → (b : B) → I ϕ b → P b
   I-is-initial {𝓣} {ϕ} P IH₁ IH₂ b i = I-recursion P R S b i
    where
     R : (U : B → Ω 𝓥)
       → ((x : B) → U x holds → I ϕ x)
       → ((x : B) → U x holds → P x)
       → (x : B) → x ≤ᴮ (⋁ (Sigma B (λ b₂ → U b₂ holds) , q ∘ pr₁))
       → P x
     R U f f' x g = IH₁ U f' x g
     S : (a : ⟨ L ⟩)
       → (b : B)
       → ϕ (a , b) holds
       → ((x : B) → x ≤ᴮ a → I ϕ x)
       → ((x : B) → x ≤ᴮ a → P x)
       → P b
     S a b p f f' = IH₂ a b p f'

   open PropositionalTruncation pt
   open Universe-Polymorphic-Powerset 𝓥

   𝓘 : (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)) → 𝓟 {𝓤 ⊔ 𝓥 ⁺} B
   𝓘 ϕ b = (∥ I ϕ b ∥ , ∥∥-is-prop)

   𝓘-is-least-closed-subset : {ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)}
                            → (P : 𝓟 {𝓣} B)
                            → ((U : 𝓟 {𝓥} B)
                             → (U ⊆ P)
                             → ((b : B) → (b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁))) →  b ∈ P))
                            → ((a : ⟨ L ⟩)
                             → (b : B)
                             → (ϕ (a , b) holds)
                             → ((b' : B) → (b' ≤ᴮ a → b' ∈ P)) → b ∈ P)
                            → 𝓘 ϕ ⊆ P
   𝓘-is-least-closed-subset {𝓣} {ϕ} P IH₁ IH₂ b = ∥∥-rec (holds-is-prop (P b)) θ
    where
     θ : I ϕ b → b ∈ P
     θ = I-is-initial P' IH₁ IH₂ b
      where
       P' : B → 𝓣  ̇
       P' x = x ∈ P

\end{code}

We now work towards defining a monotone operator on a certain class of inductive definitions which we
will call 'local'. This monotone operator will have a least-fixed point when 𝓘 ϕ is small.

\begin{code}

   S : (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)) → (a : ⟨ L ⟩) → 𝓤 ⊔ 𝓦 ⊔ 𝓥  ̇
   S ϕ a = Σ b ꞉ B , (Ǝ a' ꞉ ⟨ L ⟩ , ϕ (a' , b) holds × (a' ≤ a) holds) holds

   S-monotone-ish : (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)) → (x y : ⟨ L ⟩) → (x ≤ y) holds → S ϕ x → S ϕ y
   S-monotone-ish ϕ x y o = f
    where
     f : S ϕ x → S ϕ y
     f (b , c) = (b , g c)
      where
       g : (Ǝ a' ꞉ ⟨ L ⟩ , (ϕ (a' , b) holds) × ((a' ≤ x) holds)) holds
         → (Ǝ a' ꞉ ⟨ L ⟩ , (ϕ (a' , b) holds) × ((a' ≤ y) holds)) holds
       g = ∥∥-rec ∥∥-is-prop g'
        where
         g' : Σ a' ꞉ ⟨ L ⟩ , (ϕ (a' , b) holds) × ((a' ≤ x) holds)
            → (Ǝ a' ꞉ ⟨ L ⟩ , (ϕ (a' , b) holds) × ((a' ≤ y) holds)) holds
         g' (a' , p , r) = ∣ (a' , p , is-transitive-for L a' x y r o) ∣

   S-has-sup-implies-monotone : (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥))
                              → (x y s s' : ⟨ L ⟩)
                              → (x ≤ y) holds
                              → (s is-lub-of (S ϕ x , q ∘ pr₁)) holds
                              → (s' is-lub-of (S ϕ y , q ∘ pr₁)) holds
                              → (s ≤ s') holds
   S-has-sup-implies-monotone ϕ x y s s' o (is-upbnd , is-least-upbnd) (is-upbnd' , is-least-upbnd') =
     is-least-upbnd ((s' , f))
    where
     f : (s' is-an-upper-bound-of (S ϕ x , q ∘ pr₁)) holds
     f (b , e) = is-upbnd' (S-monotone-ish ϕ x y o ((b , e)))
         
   _is-local : (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)) → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
   ϕ is-local = (a : ⟨ L ⟩) → S ϕ a is 𝓥 small

   module Local-ϕ (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)) (i : ϕ is-local) where
   
    S-small : (a : ⟨ L ⟩) → 𝓥  ̇
    S-small a = pr₁ (i a)

    S-small-≃ : (a : ⟨ L ⟩) → S-small a ≃ S ϕ a
    S-small-≃ a  = pr₂ (i a)

    S-small-map : (a : ⟨ L ⟩) → S-small a → S ϕ a
    S-small-map a = ⌜ S-small-≃ a ⌝

    S-small-map-inv : (a : ⟨ L ⟩) → S ϕ a → S-small a 
    S-small-map-inv a = ⌜ S-small-≃ a ⌝⁻¹

    S-small-monotone-ish : (x y : ⟨ L ⟩) → (x ≤ y) holds → S-small x → S-small y
    S-small-monotone-ish x y o = S-small-map-inv y ∘ S-monotone-ish ϕ x y o ∘ S-small-map x

    Γ : ⟨ L ⟩ → ⟨ L ⟩
    Γ a = ⋁ (S-small a , q ∘ pr₁ ∘ S-small-map a)

    open Monotone-Endo-Maps L hiding (_≤_)

    Γ-is-monotone : Γ is-monotone
    Γ-is-monotone x y o = S-has-sup-implies-monotone ϕ x y (Γ x) (Γ y) o Γ-x-is-sup Γ-y-is-sup
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
                               → Σ ϕ ꞉ (⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)) , Σ i ꞉ (ϕ is-local) ,
                                   ((x : ⟨ L ⟩) → (Local-ϕ.Γ ϕ i) x ＝ f x)
   mono-map-give-local-ind-def f f-mono = (ϕ , i , H)
    where
     ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)
     ϕ (a , b) = ( Lift 𝓤 (b ≤ᴮ f a) , equiv-to-prop (Lift-≃ 𝓤 (b ≤ᴮ f a)) _≤ᴮ_-is-prop-valued )
     equiv-1 : (a : ⟨ L ⟩) → small-↓ᴮ (f a) ≃ S ϕ a
     equiv-1 a = Σ-cong' (λ z → z ≤ᴮ f a)
                         ((λ z → (Ǝ a' ꞉ ⟨ L ⟩ , ϕ (a' , z) holds × (a' ≤ a) holds) holds)) equiv-2
      where
       equiv-2 : (z : B) → (z ≤ᴮ f a) ≃ (Ǝ a' ꞉ ⟨ L ⟩ , ϕ (a' , z) holds × (a' ≤ a) holds) holds
       equiv-2 z = ⌜ prop-≃-≃-⇔ fe _≤ᴮ_-is-prop-valued ∥∥-is-prop ⌝⁻¹ (map-1 , map-2)
        where
         map-1 : z ≤ᴮ f a → (Ǝ a' ꞉ ⟨ L ⟩ , ϕ (a' , z) holds × (a' ≤ a) holds) holds
         map-1 o = ∣ (a , ⌜ ≃-Lift 𝓤 (z ≤ᴮ f a) ⌝ o , is-reflexive-for L a) ∣
         map-2 : (Ǝ a' ꞉ ⟨ L ⟩ , ϕ (a' , z) holds × (a' ≤ a) holds) holds → z ≤ᴮ f a
         map-2 = ∥∥-rec _≤ᴮ_-is-prop-valued map-3
          where
           map-3 : Σ a' ꞉ ⟨ L ⟩ , ϕ (a' , z) holds × (a' ≤ a) holds → z ≤ᴮ f a
           map-3 (a' , o , r) =
              _≤_-to-_≤ᴮ_ (is-transitive-for L (q z) (f a') (f a)
                                               (_≤ᴮ_-to-_≤_ (⌜ ≃-Lift 𝓤 (z ≤ᴮ f a') ⌝⁻¹ o))
                                               (f-mono a' a r))
     i : ϕ is-local 
     i a = (small-↓ᴮ (f a) , equiv-1 a)
     G : (x : ⟨ L ⟩) → (f x is-lub-of (S ϕ x , q ∘ pr₁)) holds 
     G x = (f-is-upbnd , f-is-least)
      where
       f-is-upbnd : (f x is-an-upper-bound-of (S ϕ x , q ∘ pr₁)) holds
       f-is-upbnd (b , e) = map-4 e
        where
         map-4 : (Ǝ a' ꞉ ⟨ L ⟩ , ϕ (a' , b) holds × (a' ≤ x) holds) holds → (q b ≤ f x) holds
         map-4 = ∥∥-rec (holds-is-prop (q b ≤ f x)) map-5
          where
           map-5 : Σ a' ꞉ ⟨ L ⟩ , ϕ (a' , b) holds × (a' ≤ x) holds → (q b ≤ f x) holds
           map-5 (a' , o , r) = is-transitive-for L (q b) (f a') (f x)
                                (_≤ᴮ_-to-_≤_ (⌜ ≃-Lift 𝓤 (b ≤ᴮ f a') ⌝⁻¹ o)) (f-mono a' x r)
       f-is-least : ((u , _) : upper-bound (S ϕ x , q ∘ pr₁)) → (f x ≤ u) holds
       f-is-least (u , is-upbnd) = (is-least-upper-boundᴮ (f x)) (u , λ z → is-upbnd (⌜ equiv-1 x ⌝ z))
     H : (x : ⟨ L ⟩) → (Local-ϕ.Γ ϕ i) x ＝ f x
     H x = ≃-families-＝-sup ((Local-ϕ.Γ ϕ i) x) (f x) is-lub-of-both (G x)
      where
       open Local-ϕ ϕ i
       open Equivalent-Families-have-same-Join L (S ϕ x) (S ϕ x) (id , id-is-equiv (S ϕ x)) (q ∘ pr₁)
       open Small-Types-have-Joins L (S ϕ x) (q ∘ pr₁) (i x)

   module Correspondance-small-ϕ-closed-types-non-inc-points (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥))
                                                             (i : ϕ is-local)
                                                             where
   
    _is-small-ϕ-closed-subset : (P : 𝓟 {𝓥} B) → 𝓤 ⊔ (𝓥 ⁺)  ̇
    P is-small-ϕ-closed-subset = ((U : 𝓟 {𝓥} B)
                                → (U ⊆ P)
                                → ((b : B) → (b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁))) →  b ∈ P))
                               × ((a : ⟨ L ⟩)
                                → (b : B)
                                → (ϕ (a , b) holds)
                                → ((b' : B) → (b' ≤ᴮ a → b' ∈ P)) → b ∈ P)

    is-small-ϕ-closed-subset-is-predicate : (P : 𝓟 {𝓥} B) → is-prop (P is-small-ϕ-closed-subset)
    is-small-ϕ-closed-subset-is-predicate P =
      ×-is-prop (Π-is-prop fe λ U → Π-is-prop fe (λ C → Π-is-prop fe (λ b → Π-is-prop fe (λ f → holds-is-prop (P b)))))
                (Π-is-prop fe (λ a → Π-is-prop fe (λ b → Π-is-prop fe (λ p → Π-is-prop fe (λ f → holds-is-prop (P b))))))

    small-ϕ-closed-subsets : 𝓤 ⊔ (𝓥 ⁺)  ̇
    small-ϕ-closed-subsets =  Σ P ꞉ 𝓟 {𝓥} B , P is-small-ϕ-closed-subset

    _is-non-inc : (a : ⟨ L ⟩) → 𝓦  ̇
    a is-non-inc = (Γ a ≤ a) holds
     where
      open Local-ϕ ϕ i

    is-non-inc-is-predicate : (a : ⟨ L ⟩) → is-prop(a is-non-inc)
    is-non-inc-is-predicate a = holds-is-prop (Γ a ≤ a)
     where
      open Local-ϕ ϕ i

    non-inc-points : 𝓤 ⊔ 𝓦  ̇
    non-inc-points = Σ a ꞉ ⟨ L ⟩ , (a is-non-inc)

    small-ϕ-closed-subsets-to-non-inc-points : small-ϕ-closed-subsets → non-inc-points
    small-ϕ-closed-subsets-to-non-inc-points (P , c-closed , ϕ-closed) = (sup-P , is-non-inc)
     where
      sup-P : ⟨ L ⟩
      sup-P = ⋁ ((Σ b ꞉ B , b ∈ P) , q ∘ pr₁)
      open Subsets-Order-Joins L B q hiding (⋁_ ; _≤_)
      is-non-inc : sup-P is-non-inc
      is-non-inc = Γ-is-least-upper-bound (sup-P , is-upper-bound)
       where
        open Local-ϕ ϕ i
        open Small-Types-have-Joins L (S ϕ sup-P) (q ∘ pr₁) (i sup-P) hiding (⋁_ ; _≤_)
        Γ-is-sup : (Γ sup-P is-lub-of (S ϕ sup-P , q ∘ pr₁)) holds
        Γ-is-sup = is-lub-of-both
        Γ-is-least-upper-bound : ((u , _) : upper-bound (S ϕ sup-P , q ∘ pr₁)) → (Γ sup-P ≤ u) holds
        Γ-is-least-upper-bound = pr₂ Γ-is-sup
        b-in-P-to-b-≤-sup-P : (b : B) → b ∈ P → (q(b) ≤ sup-P) holds
        b-in-P-to-b-≤-sup-P b b-in-P = (is-an-upper-bound-for L of ((Σ b ꞉ B , b ∈ P) , q ∘ pr₁)) (b , b-in-P)
        un-trunc-map : (b : B) → Σ a ꞉ ⟨ L ⟩ , ϕ(a , b) holds × (a ≤ sup-P) holds → (q(b) ≤ sup-P) holds
        un-trunc-map b (a , p , o) = b-in-P-to-b-≤-sup-P b (ϕ-closed a b p (ϕ-hypothesis))
         where
          ϕ-hypothesis : (b' : B) → b' ≤ᴮ a → b' ∈ P
          ϕ-hypothesis b' r = c-closed P (λ x → id) b' b'-≤-sup-P
           where
            b'-≤-sup-P : b' ≤ᴮ sup-P
            b'-≤-sup-P = _≤_-to-_≤ᴮ_ (is-transitive-for L (q b') a sup-P (_≤ᴮ_-to-_≤_ r) o)
        is-upper-bound : ((b , e) : S ϕ sup-P) → (q(b) ≤ sup-P) holds
        is-upper-bound (b , e) = ∥∥-rec (holds-is-prop (q(b) ≤ sup-P)) (un-trunc-map b) e

    non-inc-points-to-small-ϕ-closed-subsets : non-inc-points → small-ϕ-closed-subsets
    non-inc-points-to-small-ϕ-closed-subsets (a , is-non-inc) = (Q a , c-closed , ϕ-closed)
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
                                     (transport (λ z → ((⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁)) ≤ z) holds)
                                                (a ＝-sup-Q ⁻¹)
                                                (joins-preserve-containment {U} {Q a} C)))
      ϕ-closed : (a' : ⟨ L ⟩)
               → (b : B)
               → (ϕ (a' , b) holds)
               → ((b' : B) → (b' ≤ᴮ a' → b' ∈ Q a)) → b ∈ Q a
      ϕ-closed a' b p f = trunc-map b ∣ (a' , p , a'-≤-a) ∣
       where
        open Local-ϕ ϕ i
        open Small-Types-have-Joins L (S ϕ a) (q ∘ pr₁) (i a) hiding (⋁_ ; _≤_)
        Γ-is-sup : (Γ a is-lub-of (S ϕ a , q ∘ pr₁)) holds
        Γ-is-sup = is-lub-of-both
        Γ-an-upper-bound : (Γ a is-an-upper-bound-of (S ϕ a , q ∘ pr₁)) holds
        Γ-an-upper-bound = pr₁ Γ-is-sup
        trunc-map : (x : B) → (Ǝ a'' ꞉ ⟨ L ⟩ , ϕ (a'' , x) holds × (a'' ≤ a) holds) holds → x ≤ᴮ a
        trunc-map x e = _≤_-to-_≤ᴮ_ (is-transitive-for L (q x) (Γ a) a (Γ-an-upper-bound (x , e)) (is-non-inc))
        a'-≤-a : (a' ≤ a) holds
        a'-≤-a = transport (λ z → (z ≤ a) holds)
                           (a' ＝-sup-Q ⁻¹)
                           (transport (λ z → ((sup-Q a') ≤ z) holds)
                                             (a ＝-sup-Q ⁻¹)
                                             (joins-preserve-containment {Q a'} {Q a} f))


    small-ϕ-closed-subsets-≃-non-inc-points : small-ϕ-closed-subsets ≃ non-inc-points
    small-ϕ-closed-subsets-≃-non-inc-points =
      (small-ϕ-closed-subsets-to-non-inc-points , qinvs-are-equivs small-ϕ-closed-subsets-to-non-inc-points is-qinv)
     where
      H : non-inc-points-to-small-ϕ-closed-subsets ∘ small-ϕ-closed-subsets-to-non-inc-points ∼ id
      H (P , c-closed , ϕ-closed) = to-subtype-＝ is-small-ϕ-closed-subset-is-predicate P'-＝-P
       where
        sup-P : ⟨ L ⟩
        sup-P = pr₁ (small-ϕ-closed-subsets-to-non-inc-points (P , c-closed , ϕ-closed))
        P' : 𝓟 {𝓥} B
        P' = pr₁ (non-inc-points-to-small-ϕ-closed-subsets
                (small-ϕ-closed-subsets-to-non-inc-points (P , c-closed , ϕ-closed)))
        P'-＝-P : P' ＝ P
        P'-＝-P = dfunext fe P'-∼-P 
         where
          P'-∼-P : P' ∼ P
          P'-∼-P x = to-Ω-＝ fe (pe _≤ᴮ_-is-prop-valued (holds-is-prop (P x)) P'-to-P P-to-P')
           where
            P'-to-P : x ≤ᴮ sup-P → x ∈ P
            P'-to-P = c-closed P (λ z → id) x
            P-to-P' : x ∈ P → x ≤ᴮ sup-P
            P-to-P' r = _≤_-to-_≤ᴮ_ ((is-an-upper-bound-for L of ((Σ b ꞉ B , b ∈ P) , q ∘ pr₁)) (x , r))
      G : small-ϕ-closed-subsets-to-non-inc-points ∘ non-inc-points-to-small-ϕ-closed-subsets ∼ id
      G (a , is-non-inc) = to-subtype-＝ is-non-inc-is-predicate sup-P-＝-a
       where
        P : 𝓟 {𝓥} B
        P = pr₁ (non-inc-points-to-small-ϕ-closed-subsets (a , is-non-inc))
        sup-P : ⟨ L ⟩
        sup-P = pr₁ (small-ϕ-closed-subsets-to-non-inc-points (non-inc-points-to-small-ϕ-closed-subsets (a , is-non-inc)))
        sup-P-＝-a : sup-P ＝ a
        sup-P-＝-a = is-sup'ᴮ a ⁻¹
      is-qinv : qinv small-ϕ-closed-subsets-to-non-inc-points
      is-qinv = (non-inc-points-to-small-ϕ-closed-subsets , H , G)

    module Small-𝓘nd-exists (ind-e : Inductively-Generated-Subset-Exists ϕ) where

     open Trun-Ind-Def ϕ ind-e
     open Inductively-Generated-Subset-Exists ind-e

     module Small-𝓘nd (j : (b : B) → (b ∈ 𝓘nd) is 𝓥 small) where

      small-𝓘 : (b : B) →  𝓥  ̇
      small-𝓘 b = pr₁ (j b) 

      small-𝓘-≃-𝓘nd : (b : B) → small-𝓘 b ≃ b ∈ 𝓘nd 
      small-𝓘-≃-𝓘nd b = pr₂ (j b)

      small-𝓘-is-prop-valued : {b : B} → is-prop (small-𝓘 b)
      small-𝓘-is-prop-valued {b} = equiv-to-prop (small-𝓘-≃-𝓘nd b) (Ind-trunc b)

      𝓘-is-small-subset : 𝓟 {𝓥} B
      𝓘-is-small-subset = λ b → (small-𝓘 b , small-𝓘-is-prop-valued)

      small-𝓘-is-c-closed : (U : 𝓟 {𝓥} B)
                        → U ⊆ 𝓘-is-small-subset
                        → (b : B) → b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁))
                        → b ∈ 𝓘-is-small-subset
      small-𝓘-is-c-closed U C b o = {!!}
      
      small-𝓘-is-ϕ-closed : (a : ⟨ L ⟩)
                        → (b : B)
                        → ϕ (a , b) holds
                        → ((b' : B) → b' ≤ᴮ a → b' ∈ 𝓘-is-small-subset)
                        → b ∈ 𝓘-is-small-subset
      small-𝓘-is-ϕ-closed a b p f = {!!}

      total-space-𝓘-is-small : (Σ b ꞉ B , b ∈ 𝓘nd) is 𝓥 small
      total-space-𝓘-is-small = ((Σ b ꞉ B , small-𝓘 b) , Σ-cong λ b → small-𝓘-≃-𝓘nd b)
   
      e : (Σ b ꞉ B , small-𝓘 b) ≃ (Σ b ꞉ B , b ∈ 𝓘nd)
      e = pr₂ total-space-𝓘-is-small

      sup-𝓘 : ⟨ L ⟩
      sup-𝓘 = ⋁ ((Σ b ꞉ B , small-𝓘 b) , q ∘ pr₁ ∘ ⌜ e ⌝)

      sup-𝓘-is-lub : (sup-𝓘 is-lub-of ((Σ b ꞉ B , b ∈ 𝓘nd) , q ∘ pr₁)) holds
      sup-𝓘-is-lub = is-lub-of-both
       where
        open Small-Types-have-Joins L (Σ b ꞉ B , b ∈ 𝓘nd) (q ∘ pr₁) total-space-𝓘-is-small

      open Local-ϕ ϕ i

      Γ-has-least-fixed-point : (Γ sup-𝓘 ＝ sup-𝓘) × ((a : ⟨ L ⟩) → (sup-𝓘 ≤ a) holds)
      Γ-has-least-fixed-point = ({!!} , {!!})
       where
        Γ-sup-≤-sup : (Γ sup-𝓘 ≤ sup-𝓘) holds
        Γ-sup-≤-sup = pr₂ (small-ϕ-closed-subsets-to-non-inc-points
                          (𝓘-is-small-subset , small-𝓘-is-c-closed , small-𝓘-is-ϕ-closed))
       
\end{code}

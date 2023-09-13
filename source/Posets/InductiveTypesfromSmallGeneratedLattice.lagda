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

module Posets.InductiveTypesfromSmallGeneratedLattice 
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
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

is-transitive-for : (L : Sup-Lattice 𝓤 𝓦 𝓥) → is-transitive (order-of L) holds
is-transitive-for L = pr₂ (pr₁ (is-partial-order-for L))

is-lub-for : (L : Sup-Lattice 𝓤 𝓦 𝓥) → (U : Fam 𝓥 ⟨ L ⟩) →
                                         ((order-of L) Joins.is-lub-of join-for L U) U holds
is-lub-for (A , (_≤_ , ⋁_) , order , is-lub-of) = is-lub-of

\end{code}

We now define a small basis for a Sup-Lattice. This consists of a type B in a fixed universe and a
map q from B to the carrier of the Sup-Lattice. In sense to be made precise the pair B and q generate
the Sup-Lattice. This notion we be integral in developing the rest of our theory.

\begin{code}

module Sup-Lattice-Small-Basis {𝓤 𝓦 𝓥 : Universe} (L : Sup-Lattice 𝓤 𝓦 𝓥) where

 _≤_ : ⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦
 _≤_ = order-of L

 open Joins _≤_

 module Small-Basis {B : 𝓥  ̇} (q : B → ⟨ L ⟩) where

  ↓ᴮ : ⟨ L ⟩ → 𝓦 ⊔ 𝓥  ̇
  ↓ᴮ x = Σ b ꞉ B , (q b ≤ x) holds

  ↓ᴮ-inclusion : (x : ⟨ L ⟩) → ↓ᴮ x → ⟨ L ⟩
  ↓ᴮ-inclusion x = q ∘ pr₁

  is-small-basis : 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⁺  ̇
  is-small-basis = (x : ⟨ L ⟩) →
                    ((b : B) → ((q b ≤ x) holds) is 𝓥 small) ×
                    ((x is-lub-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds)

  module Small-Basis-Facts (h : is-small-basis) where

   ≤-is-small : (x : ⟨ L ⟩) (b : B) → ((q b ≤ x) holds) is 𝓥 small
   ≤-is-small x b = pr₁ (h x) b

   x-is-sup : (x : ⟨ L ⟩) → (x is-lub-of (↓ᴮ x , ↓ᴮ-inclusion x)) holds
   x-is-sup x = pr₂ (h x)

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

\end{code}

We pause to introduce some universe polymorphic powerset notation which will allow the final product
in the coming section to appear more like its set theoretic incarnation.

\begin{code}

module Universe-Polymorphic-Powerset (𝓥 : Universe) where

   𝓟 : {𝓣 : Universe} → 𝓥  ̇ → 𝓥 ⊔ 𝓣 ⁺  ̇
   𝓟 {𝓣} X = X → Ω 𝓣

   _∈_ : {𝓣 : Universe} {X : 𝓥  ̇} → X → 𝓟 {𝓣} X → 𝓣  ̇
   x ∈ A = A x holds
   
   _⊆_ : {𝓣 𝓦 : Universe} {X : 𝓥  ̇} → 𝓟 {𝓣} X → 𝓟 {𝓦} X →  𝓥 ⊔ 𝓣 ⊔ 𝓦  ̇
   A ⊆ B = ∀ x → x ∈ A → x ∈ B

\end{code}

Now it is time to define the least closed subset of an inductive definition. We start by defining an
auxillary untruncated inductive family and provide an induction principle, etc. We then take the
propositional truncation of this family which yields a predicate and subsequently prove that it is
the least-closed subset under the inductive definition.

\begin{code}

module Inductive-Definitions (𝓤 𝓦 𝓥 : Universe)
                             (L : Sup-Lattice 𝓤 𝓦 𝓥)
                             where
 
 ⋁_ : Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
 ⋁_ = join-for L

 open Sup-Lattice-Small-Basis L
 open Joins _≤_

 module _ {B : 𝓥  ̇} (q : B → ⟨ L ⟩) where

  open Small-Basis q

  module Ind-ϕ (h : is-small-basis) where

   open Small-Basis-Facts h

   data I (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)) : B → (𝓤 ⊔ 𝓥 ⁺)  ̇ where
    c-cl : (U : B → Ω 𝓥) → ((b : B) → ((U b) holds → I ϕ b)) →
           (b : B) → b ≤ᴮ (⋁ ((Σ b ꞉ B , (U b) holds) , q ∘ pr₁)) → I ϕ b
    ϕ-cl : (a : ⟨ L ⟩) → (b : B) → (ϕ (a , b)) holds →
           ((b' : B) → (b' ≤ᴮ a → I ϕ b')) → I ϕ b

   I-induction : (P : {ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)} (b : B) → I ϕ b → 𝓣  ̇) →
                 {ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)} →
                  ((U : B → Ω 𝓥) → (f : (x : B) → (U x holds → I ϕ x)) →
                  (f' : (x : B) → (u : U x holds) → P x (f x u)) →
                  (b : B) → (g : (b ≤ᴮ (⋁ ((Σ x ꞉ B , U x holds) , q ∘ pr₁)))) →
                  P b (c-cl U f b g)) →
                 ((a : ⟨ L ⟩) → (b : B) → (p : ϕ (a , b) holds) →
                  (f : (x : B) → (x ≤ᴮ a → I ϕ x)) →
                  (f' : (x : B) → (o : x ≤ᴮ a) → P x (f x o)) →
                  P b (ϕ-cl a b p f)) →
                 (b : B) → (i : I ϕ b) → P b i
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

   I-recursion : (P : B → 𝓣  ̇) → {ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)} → 
                 ((U : B → Ω 𝓥) → ((x : B) → (U x holds → I ϕ x)) → 
                  ((x : B) → (U x holds → P x)) →
                  (b : B) → (b ≤ᴮ (⋁ ((Σ b ꞉ B , U b holds) , q ∘ pr₁))) → P b) →
                 ((a : ⟨ L ⟩) → (b : B) → (ϕ (a , b) holds) →
                  ((x : B) → (x ≤ᴮ a → I ϕ x)) → ((x : B) → (x ≤ᴮ a → P x)) → P b) →
                 (b : B) → I ϕ b → P b
   I-recursion P = I-induction (λ b → (λ _ → P b))

   I-is-initial : (P : B → 𝓣  ̇) → {ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)} → 
                  ((U : B → Ω 𝓥) → ((b : B) → (U b holds → P b)) →
                   ((b : B) → (b ≤ᴮ (⋁ ((Σ b ꞉ B , U b holds) , q ∘ pr₁))) → P b)) →
                  ((a : ⟨ L ⟩) → (b : B) → (ϕ (a , b) holds) →
                   ((b' : B) → (b' ≤ᴮ a → P b')) → P b) →
                  (b : B) → I ϕ b → P b
   I-is-initial {𝓣} P {ϕ} IH₁ IH₂ b i = I-recursion P R S b i
    where
     R : (U : B → Ω 𝓥) →
         ((x : B) → U x holds → I ϕ x) →
         ((x : B) → U x holds → P x) →
         (x : B) → x ≤ᴮ (⋁ (Sigma B (λ b₂ → U b₂ holds) , q ∘ pr₁)) → P x
     R U f f' x g = IH₁ U f' x g
     S : (a : ⟨ L ⟩) (b : B) → ϕ (a , b) holds →
         ((x : B) → x ≤ᴮ a → I ϕ x) → ((x : B) → x ≤ᴮ a → P x) → P b
     S a b p f f' = IH₂ a b p f'

   open PropositionalTruncation pt
   open Universe-Polymorphic-Powerset 𝓥

   𝓘 : (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)) → 𝓟 {𝓤 ⊔ 𝓥 ⁺} B
   𝓘 ϕ b = (∥ I ϕ b ∥ , ∥∥-is-prop)

   𝓘-is-least-closed-subset : (P : 𝓟 {𝓣} B) → {ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)} →
                              ((U : 𝓟 {𝓥} B) → (U ⊆ P) →
                               ((b : B) → (b ≤ᴮ (⋁ ((Σ b ꞉ B , b ∈ U) , q ∘ pr₁))) →  b ∈ P)) →
                              ((a : ⟨ L ⟩) → (b : B) → (ϕ (a , b) holds) →
                               ((b' : B) → (b' ≤ᴮ a → b' ∈ P)) → b ∈ P) →
                              𝓘 ϕ ⊆ P
   𝓘-is-least-closed-subset {𝓣} P {ϕ} IH₁ IH₂ b = ∥∥-rec (holds-is-prop (P b)) θ
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

   S-monotone : (ϕ : ⟨ L ⟩ × B → Ω (𝓤 ⊔ 𝓥)) → (x y : ⟨ L ⟩) → (x ≤ y) holds → S ϕ x → S ϕ y
   S-monotone ϕ x y o = f
    where
     f : S ϕ x → S ϕ y
     f (b , c) = (b , g c)
      where
       g : (Ǝ a' ꞉ ⟨ L ⟩ , (ϕ (a' , b) holds) × ((a' ≤ x) holds)) holds →
            (Ǝ a' ꞉ ⟨ L ⟩ , (ϕ (a' , b) holds) × ((a' ≤ y) holds)) holds
       g = ∥∥-rec ∥∥-is-prop g'
        where
         g' : Σ a' ꞉ ⟨ L ⟩ , (ϕ (a' , b) holds) × ((a' ≤ x) holds) →
              (Ǝ a' ꞉ ⟨ L ⟩ , (ϕ (a' , b) holds) × ((a' ≤ y) holds)) holds
         g' (a' , p , r) = ∣ (a' , p , is-transitive-for L a' x y r o) ∣
         
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

    S-small-monotone : (x y : ⟨ L ⟩) → (x ≤ y) holds → S-small x → S-small y
    S-small-monotone x y o = S-small-map-inv y ∘ S-monotone ϕ x y o ∘ S-small-map x

    Γ : ⟨ L ⟩ → ⟨ L ⟩
    Γ a = ⋁ ((S-small a , q ∘ pr₁ ∘ S-small-map a))

    cofinal : Fam 𝓥 ⟨ L ⟩ → Fam 𝓥 ⟨ L ⟩ → Ω (𝓦 ⊔ 𝓥)
    cofinal (X , q₁) (Y , q₂) = Ɐ x ꞉ X , Ǝ y ꞉ Y , (q₁ x ≤ q₂ y) holds

    cofinality-implies-ordering-of-joins : (R T : Fam 𝓥 ⟨ L ⟩) → cofinal R T holds → ((⋁ R) ≤ (⋁ T)) holds
    cofinality-implies-ordering-of-joins (X , q₁) (Y , q₂) C = {!!}

    Γ-is-monotone : (x y : ⟨ L ⟩) → (x ≤ y) holds → (Γ x ≤ Γ y) holds
    Γ-is-monotone x y o =
     cofinality-implies-ordering-of-joins (S-small x , q ∘ pr₁ ∘ S-small-map x)
                                          (S-small y , q ∘ pr₁ ∘ S-small-map y) C
     where
      C : cofinal (S-small x , q ∘ pr₁ ∘ S-small-map x)
                  (S-small y , q ∘ pr₁ ∘ S-small-map y) holds
      C s = {!!}

    Γ-is-monotone' : (x y : ⟨ L ⟩) → (x ≤ y) holds → (Γ x ≤ Γ y) holds
    Γ-is-monotone' x y o = pr₂ (is-lub-for L (S-small x , q ∘ pr₁ ∘ S-small-map x))
                           ((Γ y , is-upperbound))
     where
      upperbound-y-implies-upperbound-x :
       ((Γ y) is-an-upper-bound-of (S-small y , q ∘ pr₁ ∘ S-small-map y)) holds →
       ((Γ y) is-an-upper-bound-of (S-small x , q ∘ pr₁ ∘ S-small-map x)) holds
      upperbound-y-implies-upperbound-x up-for-y i = {!!}
      is-upperbound : ((Γ y) is-an-upper-bound-of (S-small x , q ∘ pr₁ ∘ S-small-map x)) holds
      is-upperbound = upperbound-y-implies-upperbound-x
                      (pr₁ (is-lub-for L (S-small y , q ∘ pr₁ ∘ S-small-map y)))




\end{code}




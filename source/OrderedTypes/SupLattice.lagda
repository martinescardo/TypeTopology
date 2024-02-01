Ian Ray 29/01/2024

The concept of a Sup Lattice is formulated in a universe polymorphic manner.
The carrier will live in the universe 𝓤, the order takes values in 𝓦 and
suprema will exist for all families in 𝓥.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Hedberg
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.PropTrunc
open import UF.Retracts
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Size
open import UF.SmallnessProperties
open import UF.UniverseEmbedding

module OrderedTypes.SupLattice
       (pt : propositional-truncations-exist)
       (fe : Fun-Ext)
        where

open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of)
open import Slice.Family
open import UF.ImageAndSurjection pt

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

We commence by defining sup lattices and some boiler plate. 

\begin{code}

module sup-lattice-def (𝓤 𝓦 𝓥 : Universe) where

 sup-lattice-data : 𝓤  ̇ → 𝓤 ⊔ 𝓦 ⁺ ⊔ 𝓥 ⁺  ̇
 sup-lattice-data A = (A → A → Ω 𝓦) × (Fam 𝓥 A → A)
 
 is-sup-lattice : {A : 𝓤  ̇} → sup-lattice-data A → 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⁺  ̇  
 is-sup-lattice {A} (_≤_ , ⋁_) = is-partial-order A _≤_ × suprema
  where
   open Joins _≤_
   suprema : 𝓤 ⊔ 𝓦 ⊔ 𝓥 ⁺  ̇
   suprema = (U : Fam 𝓥 A) → ((⋁ U) is-lub-of U) holds

 sup-lattice-structure : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓦 ⁺ ̇
 sup-lattice-structure A = Σ d ꞉ (sup-lattice-data A) , is-sup-lattice d

Sup-Lattice : (𝓤 𝓦 𝓥 : Universe) → (𝓤 ⊔ 𝓦 ⊔ 𝓥) ⁺  ̇
Sup-Lattice 𝓤 𝓦 𝓥 = Σ A ꞉ 𝓤  ̇ , sup-lattice-structure A
 where
  open sup-lattice-def 𝓤 𝓦 𝓥

⟨_⟩ : Sup-Lattice 𝓤 𝓦 𝓥 → 𝓤  ̇
⟨ A , rest ⟩ = A

order-of : (L : Sup-Lattice 𝓤 𝓦 𝓥) → (⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓦)
order-of (A , (_≤_ , ⋁_) , rest) = _≤_

syntax order-of L x y = x ≤⟨ L ⟩ y

join-of : (L : Sup-Lattice 𝓤 𝓦 𝓥) → Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
join-of (A , (_≤_ , ⋁_) , rest) = ⋁_

syntax join-of L U = ⋁⟨ L ⟩ U

partial-orderedness-of : (L : Sup-Lattice 𝓤 𝓦 𝓥)
                       → is-partial-order ⟨ L ⟩ (order-of L)
partial-orderedness-of (A , (_≤_ , ⋁_) , order , is-lub-of) = order

reflexivity-of : (L : Sup-Lattice 𝓤 𝓦 𝓥) → is-reflexive (order-of L) holds
reflexivity-of L = pr₁ (pr₁ (partial-orderedness-of L))

antisymmetry-of : (L : Sup-Lattice 𝓤 𝓦 𝓥) → is-antisymmetric (order-of L) 
antisymmetry-of L = pr₂ (partial-orderedness-of L)

transitivity-of : (L : Sup-Lattice 𝓤 𝓦 𝓥) → is-transitive (order-of L) holds
transitivity-of L = pr₂ (pr₁ (partial-orderedness-of L))

join-is-lub-of : (L : Sup-Lattice 𝓤 𝓦 𝓥)
               → (U : Fam 𝓥 ⟨ L ⟩)
               → ((order-of L) Joins.is-lub-of join-of L U) U holds
join-is-lub-of (A , (_≤_ , ⋁_) , order , suprema) = suprema

join-is-upper-bound-of : (L : Sup-Lattice 𝓤 𝓦 𝓥)
                       → (U : Fam 𝓥 ⟨ L ⟩)
                       → ((order-of L) Joins.is-an-upper-bound-of
                                          join-of L U) U holds
join-is-upper-bound-of L U = pr₁ (join-is-lub-of L U)

join-is-least-upper-bound-of : (L : Sup-Lattice 𝓤 𝓦 𝓥)
                             → (U : Fam 𝓥 ⟨ L ⟩)
                             → ((u' , _) : Joins.upper-bound (order-of L) U)
                             → (order-of L (join-of L U) u') holds
join-is-least-upper-bound-of L U = pr₂ (join-is-lub-of L U)

sethood-of : (L : Sup-Lattice 𝓤 𝓦 𝓥) → is-set ⟨ L ⟩
sethood-of L =
  type-with-prop-valued-refl-antisym-rel-is-set
   (λ x → λ y → order-of L x y holds)
   (λ x → λ y → holds-is-prop (order-of L x y))
   (λ x → reflexivity-of L x)
   (λ x → λ y → antisymmetry-of L)

\end{code}

We now define monotone endomaps on a sup-lattice. This notion is not too
restrictive as our interest is with fixed points.

\begin{code}

module _ {𝓤 𝓦 𝓥 : Universe} (L : Sup-Lattice 𝓤 𝓦 𝓥) where

 is-monotone : (f : ⟨ L ⟩ → ⟨ L ⟩) → 𝓤 ⊔ 𝓦  ̇
 is-monotone f = (x y : ⟨ L ⟩) → (x ≤⟨ L ⟩ y) holds → (f x ≤⟨ L ⟩ f y) holds

\end{code}

We now show that when one subset contains another the join of their total
spaces are ordered as expected. 

\begin{code}

module _ {𝓤 𝓦 𝓥 : Universe}
         (L : Sup-Lattice 𝓤 𝓦 𝓥)
         {A : 𝓥  ̇}
         (m : A → ⟨ L ⟩)
          where

 open Joins (order-of L)

 joins-preserve-containment : {P : 𝓟 {𝓥} A} {Q : 𝓟 {𝓥} A}
                            → P ⊆ Q
                            → ((⋁⟨ L ⟩ (𝕋 P , m ∘ 𝕋-to-carrier P))
                             ≤⟨ L ⟩ (⋁⟨ L ⟩ (𝕋 Q , m ∘ 𝕋-to-carrier Q))) holds
 joins-preserve-containment {P} {Q} C =
   (join-is-least-upper-bound-of L (𝕋 P , m ∘ 𝕋-to-carrier P))
    (⋁⟨ L ⟩ (𝕋 Q , m ∘ 𝕋-to-carrier Q) ,
    (λ (b , b-in-P)
      → (join-is-upper-bound-of L (𝕋 Q , m ∘ 𝕋-to-carrier Q))
        (b , C b b-in-P)))

\end{code}

We now show if a type is small and has a map to the carrier then it has a join.

\begin{code}

module _ {𝓤 𝓦 𝓥 𝓣 : Universe}
         (L : Sup-Lattice 𝓤 𝓦 𝓥)
         {T : 𝓣  ̇}
         (m : T → ⟨ L ⟩)
         (t : T is 𝓥 small)
          where
 private 
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
  s = ⋁⟨ L ⟩ (T' , T'-inclusion)

 open Joins (order-of L)

 sup-of-small-fam-is-lub : (s is-lub-of (T , m)) holds
 sup-of-small-fam-is-lub = (I , III)
  where
   I : (s is-an-upper-bound-of (T , m)) holds
   I t = II
    where
     II : (m t ≤⟨ L ⟩ s) holds 
     II = transport (λ z → (m z ≤⟨ L ⟩ s) holds)
                    (section-T'-to-T t)
                    (join-is-upper-bound-of L (T' , T'-inclusion) (T-to-T' t))
   III : ((u , _) : upper-bound (T , m)) → (s ≤⟨ L ⟩ u) holds
   III (u , is-upbnd-T) = IV
    where
     IV : (s ≤⟨ L ⟩ u) holds
     IV = join-is-least-upper-bound-of
            L (T' , T'-inclusion) (u , λ i → is-upbnd-T (T'-to-T i))

\end{code}

We now show that reindexing families along a surjection preserves the supremum.

\begin{code}

module _ {𝓤 𝓦 𝓥 𝓣 𝓣' : Universe}
         (L : Sup-Lattice 𝓤 𝓦 𝓥)
         {T : 𝓣  ̇}
         {T' : 𝓣'  ̇}
         (e : T' ↠ T)
         (m : T → ⟨ L ⟩)
          where

 open Joins (order-of L)

 reindexing-along-surj-＝-sup : (s s' : ⟨ L ⟩)
                              → (s is-lub-of (T , m)) holds
                              → (s' is-lub-of (T' , m ∘ ⌞ e ⌟)) holds
                              → s ＝ s'
 reindexing-along-surj-＝-sup
   s s' (is-upbnd , is-least-upbnd) (is-upbnd' , is-least-upbnd') =
   antisymmetry-of L I IV
  where
   I : (s ≤⟨ L ⟩ s') holds
   I = is-least-upbnd (s' , λ t → III t (⌞⌟-is-surjection e t))
    where
     II : (t : T)
        → Σ t' ꞉ T' , ⌞ e ⌟ t' ＝ t
        → (m t ≤⟨ L ⟩ s') holds
     II t (t' , path) =
       transport (λ z → (m z ≤⟨ L ⟩ s') holds) path (is-upbnd' t')
     III : (t : T)
         → (Ǝ t' ꞉ T' , ⌞ e ⌟ t' ＝ t) holds
         → (m t ≤⟨ L ⟩ s') holds
     III t = ∥∥-rec (holds-is-prop (m t ≤⟨ L ⟩ s')) (II t)
   IV : (s' ≤⟨ L ⟩ s) holds
   IV = is-least-upbnd' (s , λ t' → is-upbnd (⌞ e ⌟ t'))

\end{code}

We can also show that reindexing along an equivalence preserves the supremum.
This follows from the previous result as any equivalence can be demoted to a
surjection.

\begin{code}

module _ {𝓤 𝓦 𝓥 𝓣 𝓣' : Universe}
         (L : Sup-Lattice 𝓤 𝓦 𝓥)
         {T : 𝓣  ̇}
         {T' : 𝓣'  ̇}
         (e : T' ≃ T)
         (m : T → ⟨ L ⟩)
          where

 open Joins (order-of L)

 reindexing-along-equiv-＝-sup : (s s' : ⟨ L ⟩)
                               → (s is-lub-of (T , m)) holds
                               → (s' is-lub-of (T' , m ∘ ⌜ e ⌝ )) holds
                               → s ＝ s'
 reindexing-along-equiv-＝-sup =
   reindexing-along-surj-＝-sup
     L (⌜ e ⌝ , equivs-are-surjections ⌜ e ⌝-is-equiv) m

\end{code}

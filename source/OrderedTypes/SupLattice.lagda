Ian Ray, started: 2023-09-12 - updated: 2024-02-05.

A Sup Lattice L is a set with a partial order ≤ that has suprema of 'small'
types. We will use three universe parameters: 𝓤 for the carrier, 𝓦 for the
order values and 𝓥 for the families which have suprema.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.FunExt
open import UF.HedbergApplications
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.PropTrunc
open import UF.Retracts
open import UF.Sets
open import UF.SubtypeClassifier
open import UF.Size

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

We commence by defining sup lattices.

\begin{code}

module _ (𝓤 𝓣 𝓥 : Universe) where

 sup-lattice-data : 𝓤 ̇ → 𝓤 ⊔ 𝓣 ⁺ ⊔ 𝓥 ⁺ ̇
 sup-lattice-data A = (A → A → Ω 𝓣) × (Fam 𝓥 A → A)

 is-sup-lattice : {A : 𝓤 ̇ } → sup-lattice-data A → 𝓤 ⊔ 𝓣 ⊔ 𝓥 ⁺ ̇
 is-sup-lattice {A} (_≤_ , ⋁_) = is-partial-order A _≤_ × suprema
  where
   open Joins _≤_
   suprema : 𝓤 ⊔ 𝓣 ⊔ 𝓥 ⁺ ̇
   suprema = (U : Fam 𝓥 A) → ((⋁ U) is-lub-of U) holds

 sup-lattice-structure : 𝓤 ̇ → 𝓤 ⊔ 𝓥 ⁺ ⊔ 𝓣 ⁺ ̇
 sup-lattice-structure A = Σ d ꞉ (sup-lattice-data A) , is-sup-lattice d

 Sup-Lattice : (𝓤 ⊔ 𝓣 ⊔ 𝓥) ⁺ ̇
 Sup-Lattice = Σ A ꞉ 𝓤 ̇ , sup-lattice-structure A

\end{code}

Now we give some naming conventions which will be useful.

\begin{code}

⟨_⟩ : Sup-Lattice 𝓤 𝓣 𝓥 → 𝓤 ̇
⟨ A , rest ⟩ = A

order-of : (L : Sup-Lattice 𝓤 𝓣 𝓥) → (⟨ L ⟩ → ⟨ L ⟩ → Ω 𝓣)
order-of (A , (_≤_ , ⋁_) , rest) = _≤_

syntax order-of L x y = x ≤⟨ L ⟩ y

join-of : (L : Sup-Lattice 𝓤 𝓣 𝓥) → Fam 𝓥 ⟨ L ⟩ → ⟨ L ⟩
join-of (A , (_≤_ , ⋁_) , rest) = ⋁_

syntax join-of L U = ⋁⟨ L ⟩ U

partial-orderedness-of : (L : Sup-Lattice 𝓤 𝓣 𝓥)
                       → is-partial-order ⟨ L ⟩ (order-of L)
partial-orderedness-of (A , (_≤_ , ⋁_) , order , is-lub-of) = order

reflexivity-of : (L : Sup-Lattice 𝓤 𝓣 𝓥) → is-reflexive (order-of L) holds
reflexivity-of L = pr₁ (pr₁ (partial-orderedness-of L))

antisymmetry-of : (L : Sup-Lattice 𝓤 𝓣 𝓥) → is-antisymmetric (order-of L)
antisymmetry-of L = pr₂ (partial-orderedness-of L)

transitivity-of : (L : Sup-Lattice 𝓤 𝓣 𝓥) → is-transitive (order-of L) holds
transitivity-of L = pr₂ (pr₁ (partial-orderedness-of L))

join-is-lub-of : (L : Sup-Lattice 𝓤 𝓣 𝓥)
               → (U : Fam 𝓥 ⟨ L ⟩)
               → ((order-of L) Joins.is-lub-of join-of L U) U holds
join-is-lub-of (A , (_≤_ , ⋁_) , order , suprema) = suprema

join-is-upper-bound-of : (L : Sup-Lattice 𝓤 𝓣 𝓥)
                       → (U : Fam 𝓥 ⟨ L ⟩)
                       → ((order-of L) Joins.is-an-upper-bound-of
                          join-of L U) U holds
join-is-upper-bound-of L U = pr₁ (join-is-lub-of L U)

join-is-least-upper-bound-of : (L : Sup-Lattice 𝓤 𝓣 𝓥)
                             → (U : Fam 𝓥 ⟨ L ⟩)
                             → ((u' , _) : Joins.upper-bound (order-of L) U)
                             → (order-of L (join-of L U) u') holds
join-is-least-upper-bound-of L U = pr₂ (join-is-lub-of L U)

sethood-of : (L : Sup-Lattice 𝓤 𝓣 𝓥) → is-set ⟨ L ⟩
sethood-of L =
 type-with-prop-valued-refl-antisym-rel-is-set
  (λ x → λ y → order-of L x y holds)
  (λ x → λ y → holds-is-prop (order-of L x y))
  (λ x → reflexivity-of L x)
  (λ x → λ y → antisymmetry-of L)

＝-to-≤ : (L : Sup-Lattice 𝓤 𝓣 𝓥) {x y : ⟨ L ⟩}
        → x ＝ y
        → (x ≤⟨ L ⟩ y) holds
＝-to-≤ L {x} {.x} refl = reflexivity-of L x

\end{code}

We now define monotone endomaps on a sup-lattice and specify monotone endomaps
as a special case.

\begin{code}

module _ where

 is-monotone : {𝓤 𝓤' 𝓣 𝓣' 𝓥 𝓥' : Universe}
             → (L : Sup-Lattice 𝓤 𝓣 𝓥) (M : Sup-Lattice 𝓤' 𝓣' 𝓥')
             → (f : ⟨ L ⟩ → ⟨ M ⟩)
             → 𝓤 ⊔ 𝓣 ⊔ 𝓣' ̇
 is-monotone L M f = (x y : ⟨ L ⟩)
                   → (x ≤⟨ L ⟩ y) holds
                   → (f x ≤⟨ M ⟩ f y) holds

 is-monotone-endomap : {𝓤 𝓣 𝓥 : Universe}
                     → (L : Sup-Lattice 𝓤 𝓣 𝓥)
                     → (f : ⟨ L ⟩ → ⟨ L ⟩)
                     → 𝓤 ⊔ 𝓣 ̇
 is-monotone-endomap L f = is-monotone L L f

\end{code}

We now show that when one subset contains another the join of their total
spaces are ordered as expected.

\begin{code}

module _
        {𝓤 𝓣 𝓥 : Universe}
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        {A : 𝓥 ̇ }
        (m : A → ⟨ L ⟩)
       where

 open Joins (order-of L)

 joins-preserve-containment : {P : 𝓟 {𝓥} A} {Q : 𝓟 {𝓥} A}
                            → P ⊆ Q
                            → ((⋁⟨ L ⟩ 【 m , P 】)
                             ≤⟨ L ⟩ (⋁⟨ L ⟩ 【 m , Q 】)) holds
 joins-preserve-containment {P} {Q} C =
  (join-is-least-upper-bound-of L 【 m , P 】)
   (⋁⟨ L ⟩ 【 m , Q 】 ,
    (λ (b , b-in-P) → (join-is-upper-bound-of L 【 m , Q 】)
                      (b , C b b-in-P)))

\end{code}

We now show if a type is small and has a map to the carrier then it has a join.

\begin{code}

module _
        {𝓤 𝓣 𝓥 𝓦 : Universe}
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        {T : 𝓦 ̇ }
        (m : T → ⟨ L ⟩)
        (T-is-small : T is 𝓥 small)
       where
 private
  T' : 𝓥 ̇
  T' = (resized T) T-is-small

  T'-≃-T : T' ≃ T
  T'-≃-T = resizing-condition T-is-small

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
     II = transport (λ - → (m - ≤⟨ L ⟩ s) holds)
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

module _
        {𝓤 𝓣 𝓥 𝓦 𝓦' : Universe}
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        {T : 𝓦 ̇ }
        {T' : 𝓦' ̇ }
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

module _
        {𝓤 𝓣 𝓥 𝓦 𝓦' : Universe}
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        {T : 𝓦 ̇ }
        {T' : 𝓦' ̇ }
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

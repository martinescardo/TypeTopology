Fredrik Bakke, April 2025

The Cantor-Schröder-Bernstein assuming WLPO in Agda
-------------------------------------------------------------------------

We prove a generalization of the Cantor-Schröder-Bernstein theorem assuming
WLPO. We do not assume function extensionality.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module CantorSchroederBernstein.CSB-WLPO where

open import CoNaturals.Type
open import MLTT.Plus-Properties
open import MLTT.Spartan
open import Naturals.Properties
open import TypeTopology.CompactTypes
open import TypeTopology.DenseMapsProperties
open import TypeTopology.Density
open import TypeTopology.GenericConvergentSequenceCompactness
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ClassicalLogic
open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable
open import UF.FunExt
open import UF.Lower-FunExt
open import UF.PropTrunc
open import UF.SubtypeClassifier
open import UF.Retracts
open import UF.Sets
open import UF.NotNotStablePropositions
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import CantorSchroederBernstein.CSB

\end{code}

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (g : Y → X) where

 is-perfect-image-at : X → ℕ → 𝓤 ⊔ 𝓥 ̇
 is-perfect-image-at x n =
   ((x₀ , _) : fiber ((g ∘ f) ^ n) x) → fiber g x₀

 is-perfect-image : X → 𝓤 ⊔ 𝓥 ̇
 is-perfect-image x = (n : ℕ) → is-perfect-image-at x n

 dual-is-perfect-image-at : ℕ → X → 𝓤 ⊔ 𝓥 ̇
 dual-is-perfect-image-at n x =
   ((x₀ , _) : fiber ((g ∘ f) ^ n) x) → fiber g x₀

 dual-is-perfect-image : ℕ → 𝓤 ⊔ 𝓥 ̇
 dual-is-perfect-image n =
   (x : X) → is-perfect-image-at x n

\end{code}

The map g has a section on its perfect image.

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

 has-section-on-perfect-image : (x : X) → is-perfect-image f g x → fiber g x
 has-section-on-perfect-image x ρ = ρ 0 (x , refl)

 inverse-on-perfect-image : (x : X) → is-perfect-image f g x → Y
 inverse-on-perfect-image x ρ = pr₁ (has-section-on-perfect-image x ρ)

 inverse-on-perfect-image-is-section : (x : X) (ρ : is-perfect-image f g x)
                                     → g (inverse-on-perfect-image x ρ) ＝ x
 inverse-on-perfect-image-is-section x ρ = pr₂ (has-section-on-perfect-image x ρ)

 inverse-on-perfect-image-is-retraction : left-cancellable g
                                        → (y : Y)
                                        → (ρ : is-perfect-image f g (g y))
                                        → inverse-on-perfect-image (g y) ρ ＝ y
 inverse-on-perfect-image-is-retraction lc-g y ρ =
  lc-g (inverse-on-perfect-image-is-section (g y) ρ)

\end{code}

If g (f x) is a perfect image then so is x.

\begin{code}

 previous-perfect-image-at : (x : X) (n : ℕ)
                           → is-perfect-image-at f g (g (f x)) (succ n)
                           → is-perfect-image-at f g x n
 previous-perfect-image-at x n ρ (x₀ , p) = ρ (x₀ , ap (g ∘ f) p)

 previous-perfect-image : (x : X)
                        → is-perfect-image f g (g (f x))
                        → is-perfect-image f g x
 previous-perfect-image x ρ n = previous-perfect-image-at x n (ρ (succ n))

\end{code}

The perfect image of g relative to f is disjoint from the image of f.

\begin{code}

 perfect-image-is-disjoint : (x x₀ : X)
                           → ¬ (is-perfect-image f g x)
                           → (ρ : is-perfect-image f g x₀)
                           → f x ≠ inverse-on-perfect-image x₀ ρ
 perfect-image-is-disjoint x x₀ nρ ρ p = v ρ
  where
   q : g (f x) ＝ x₀
   q = ap g p ∙ inverse-on-perfect-image-is-section x₀ ρ

   s : ¬ (is-perfect-image f g (g (f x)))
   s = contrapositive (previous-perfect-image x) nρ

   v : ¬ (is-perfect-image f g x₀)
   v = transport (λ x' → ¬ (is-perfect-image f g x')) q s

\end{code}

Double negation elimination on nonperfect fibers.

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (g : Y → X) where

 is-nonperfect-image : X → 𝓤 ⊔ 𝓥 ̇
 is-nonperfect-image x =
  Σ x₀ ꞉ X , Σ n ꞉ ℕ , (((g ∘ f) ^ n) x₀ ＝ x) × ¬ (fiber g x₀)

 has-nonperfect-fiber : Y → 𝓤 ⊔ 𝓥 ̇
 has-nonperfect-fiber y =
  Σ (x₀ , _) ꞉ fiber f y , ¬ (is-perfect-image f g x₀)

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

 double-negation-elimination-on-perfect-image : is-¬¬-stable-map g
                                              → (x : X)
                                              → ¬ (is-nonperfect-image f g x)
                                              → is-perfect-image f g x
 double-negation-elimination-on-perfect-image ¬¬elim-g x nρ n (x₀ , p) =
  ¬¬elim-g x₀ (λ x₁ → nρ (x₀ , n , p , x₁))

\end{code}

If g y is not a perfect image, then f has a fiber over y, f x ＝ y, that is not
a perfect image of g. We assume that g is ¬¬-stable and left-cancellable,
although note that this implies g is an embedding (at least if we assume
negations are propositions).

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

 not-perfect-images-are-not-not-nonperfect
  : is-¬¬-stable-map g
  → (y : Y)
  → ¬ (is-perfect-image f g (g y))
  → ¬¬ (is-nonperfect-image f g (g y))
 not-perfect-images-are-not-not-nonperfect ¬¬elim-g y nρ nμ =
   nρ (double-negation-elimination-on-perfect-image ¬¬elim-g (g y) nμ)

 nonperfect-images-have-nonperfect-fibers
  : left-cancellable g
  → (y : Y)
  → is-nonperfect-image f g (g y)
  → has-nonperfect-fiber f g y
 nonperfect-images-have-nonperfect-fibers lc-g y (x₀ , zero , p , v) =
  𝟘-elim (v (y , (p ⁻¹)))
 nonperfect-images-have-nonperfect-fibers lc-g y (x₀ , succ n , p , v) =
  (((g ∘ f) ^ n) x₀ , lc-g p) , λ μ → v (μ n (x₀ , refl))

 not-perfect-images-dont-not-have-nonperfect-fibers
  : is-¬¬-stable-map g
  → left-cancellable g
  → (y : Y)
  → ¬ (is-perfect-image f g (g y))
  → ¬¬ (has-nonperfect-fiber f g y)
 not-perfect-images-dont-not-have-nonperfect-fibers ¬¬elim-g lc-g y nρ nnμ =
  not-perfect-images-are-not-not-nonperfect ¬¬elim-g y nρ
   (nnμ ∘ nonperfect-images-have-nonperfect-fibers lc-g y)

\end{code}

If f has ¬¬-compact fibers (e.g., if f is a complemented embedding),
then the nonperfect fibers of g are ¬¬-stable.

\begin{code}

is-¬¬-Compact' : 𝓤 ̇  → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
is-¬¬-Compact' {𝓤} A {𝓥} =
 (B : A → 𝓥 ̇ ) → ((x : A) → ¬¬ (B x) → B x) → ¬¬ Σ B → Σ B

decidable-types-with-double-negation-dense-equality-are-¬¬-Compact'
 : {A : 𝓤 ̇ }
 → is-decidable A
 → ((x y : A) → ¬¬ (x ＝ y))
 → is-¬¬-Compact' A {𝓦}
decidable-types-with-double-negation-dense-equality-are-¬¬-Compact' d H =
  cases (λ x B ¬¬elim nnab → x , ¬¬elim x (λ nb → nnab (λ (x' , b') → H x' x (λ p → nb (transport B p b'))))) (λ nx B ¬¬elim nnab → 𝟘-elim (nnab (λ (x , b) → nx x))) d

is-¬¬-Compact : 𝓤 ̇  → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
is-¬¬-Compact {𝓤} A {𝓥} =
 (B : A → Ω¬¬ 𝓥) → ¬¬ (Σ a ꞉ A , (B a holds¬¬)) → Σ a ꞉ A , (B a holds¬¬)

¬¬-Compact-types-are-¬¬-stable : {A : 𝓤 ̇ } → is-¬¬-Compact A {𝓤} → ¬¬-stable A
¬¬-Compact-types-are-¬¬-stable α nna =
 pr₁ (α (λ _ → ((𝟙 , 𝟙-is-prop) , λ _ → ⋆)) (¬¬-functor (λ a → a , ⋆) nna))

¬¬-Compact'-types-are-¬¬-stable : {A : 𝓤 ̇ } → is-¬¬-Compact' A {𝓤} → ¬¬-stable A
¬¬-Compact'-types-are-¬¬-stable α nna =
 pr₁ (α (λ _ → 𝟙) (λ _ _ → ⋆) (¬¬-functor (λ a → a , ⋆) nna))

is-¬¬-Compact'-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                  → (X → Y) → {𝓦 : Universe} → 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
is-¬¬-Compact'-map {𝓤} {𝓥} {X} {Y} f {𝓦} =
 each-fiber-of f (λ T → is-¬¬-Compact' T {𝓦})

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} (αf : is-¬¬-Compact'-map f) where

 nonperfect-fibers-are-¬¬-stable' : (y : Y)
                                  → ¬¬-stable (has-nonperfect-fiber f g y)
 nonperfect-fibers-are-¬¬-stable' y =
  αf y (λ (x , p) → ¬ is-perfect-image f g x) (λ _ → three-negations-imply-one)

 module _
  (¬¬elim-g : is-¬¬-stable-map g)
  (lc-g : left-cancellable g)
  (y : Y)
  (nρ : ¬ (is-perfect-image f g (g y)))
  where

  not-perfect-images-have-nonperfect-fibers' : has-nonperfect-fiber f g y
  not-perfect-images-have-nonperfect-fibers' =
   nonperfect-fibers-are-¬¬-stable' y
    (not-perfect-images-dont-not-have-nonperfect-fibers ¬¬elim-g lc-g y nρ)

  underlying-fiber-of-nonperfect-fiber-of-not-perfect-image' : fiber f y
  underlying-fiber-of-nonperfect-fiber-of-not-perfect-image' =
   pr₁ (not-perfect-images-have-nonperfect-fibers')

  element-in-nonperfect-fiber-of-not-perfect-image' : X
  element-in-nonperfect-fiber-of-not-perfect-image' =
   pr₁ (underlying-fiber-of-nonperfect-fiber-of-not-perfect-image')

  compute-element-in-nonperfect-fiber-of-not-perfect-image'
   : f element-in-nonperfect-fiber-of-not-perfect-image' ＝ y
  compute-element-in-nonperfect-fiber-of-not-perfect-image' =
   pr₂ (underlying-fiber-of-nonperfect-fiber-of-not-perfect-image')

  nonperfect-fiber-of-not-perfect-image-is-not-perfect'
   : ¬ is-perfect-image f g element-in-nonperfect-fiber-of-not-perfect-image'
  nonperfect-fiber-of-not-perfect-image-is-not-perfect' =
   pr₂ not-perfect-images-have-nonperfect-fibers'

\end{code}

With this in hand, the construction is straightforward!

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

 map-construction : (x : X) → is-decidable (is-perfect-image f g x) → Y
 map-construction x (inl γ) = inverse-on-perfect-image x γ
 map-construction x (inr nγ) = f x

 map-construction-CSB :
  ((x : X) → is-decidable (is-perfect-image f g x)) → X → Y
 map-construction-CSB D x = map-construction x (D x)

 map-construction-is-left-cancellable :
  (lc-f : left-cancellable f) →
  {x x' : X}
  (d : is-decidable (is-perfect-image f g x))
  (d' : is-decidable (is-perfect-image f g x')) →
  map-construction x d ＝ map-construction x' d' → x ＝ x'
 map-construction-is-left-cancellable lc-f {x} {x'} (inl ρ) (inl ρ') p =
  inverse-on-perfect-image-is-section x ρ ⁻¹
  ∙ ap g p
  ∙ inverse-on-perfect-image-is-section x' ρ'
 map-construction-is-left-cancellable lc-f {x} {x'} (inl ρ) (inr nρ') p =
  𝟘-elim (perfect-image-is-disjoint x' x nρ' ρ (p ⁻¹))
 map-construction-is-left-cancellable lc-f {x} {x'} (inr nρ) (inl ρ') p =
  𝟘-elim (perfect-image-is-disjoint x x' nρ ρ' p)
 map-construction-is-left-cancellable lc-f {x} {x'} (inr nρ) (inr nρ') = lc-f

 map-construction-CSB-is-left-cancellable :
  left-cancellable f →
  (D : (x : X) → is-decidable (is-perfect-image f g x)) →
  left-cancellable (map-construction-CSB D)
 map-construction-CSB-is-left-cancellable lc-f D {x} {x'} =
  map-construction-is-left-cancellable lc-f (D x) (D x')

\end{code}


\begin{code}

module _
 {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X}
 (¬¬elim-g : is-¬¬-stable-map g)
 (lc-g : left-cancellable g)
 (αf : is-¬¬-Compact'-map f {𝓤 ⊔ 𝓥})
 where

 compute-construction-on-perfect-image :
  (y : Y) →
  (γ : is-perfect-image f g (g y)) →
  (d : is-decidable (is-perfect-image f g (g y))) →
  map-construction (g y) d ＝ y
 compute-construction-on-perfect-image y γ (inl v') =
  inverse-on-perfect-image-is-retraction lc-g y v'
 compute-construction-on-perfect-image y γ (inr v) = 𝟘-elim (v γ)

 compute-construction-on-not-perfect-image :
  (y : Y) →
  (nγ : ¬ (is-perfect-image f g (g y))) →
  (d :
    is-decidable
      ( is-perfect-image f g
       ( element-in-nonperfect-fiber-of-not-perfect-image' αf ¬¬elim-g lc-g y nγ))) →
  map-construction
    (element-in-nonperfect-fiber-of-not-perfect-image' αf ¬¬elim-g lc-g y nγ)
    (d) ＝
  y
 compute-construction-on-not-perfect-image y nγ (inl v) =
  𝟘-elim (nonperfect-fiber-of-not-perfect-image-is-not-perfect' αf ¬¬elim-g lc-g y nγ v)
 compute-construction-on-not-perfect-image y nγ (inr _) =
  compute-element-in-nonperfect-fiber-of-not-perfect-image' αf ¬¬elim-g lc-g y nγ

 inverse-construction :
   (y : Y) → is-decidable (is-perfect-image f g (g y)) → X
 inverse-construction y (inl _) = g y
 inverse-construction y (inr nγ) =
   element-in-nonperfect-fiber-of-not-perfect-image' αf ¬¬elim-g lc-g y nγ

 construction-is-retraction :
  (y : Y)
  (d : is-decidable (is-perfect-image f g (g y))) →
  (d' : is-decidable (is-perfect-image f g (inverse-construction y d))) →
  map-construction (inverse-construction y d) d' ＝ y
 construction-is-retraction y (inl γ) =
   compute-construction-on-perfect-image y γ
 construction-is-retraction y (inr nγ) =
   compute-construction-on-not-perfect-image y nγ

 inverse-construction-CSB :
  ((y : Y) → is-decidable (is-perfect-image f g (g y))) → Y → X
 inverse-construction-CSB D y = inverse-construction y (D y)

 is-section-inverse-construction-CSB :
  (D : (x : X) → is-decidable (is-perfect-image f g x)) →
  map-construction-CSB D ∘ inverse-construction-CSB (D ∘ g) ∼ id
 is-section-inverse-construction-CSB D y =
   construction-is-retraction y
    (D (g y))
    (D (inverse-construction-CSB (D ∘ g) y))

 map-construction-CSB-has-section
  : (D : (x : X) → is-decidable (is-perfect-image f g x))
  → has-section (map-construction-CSB D)
 map-construction-CSB-has-section D =
  ( inverse-construction-CSB (D ∘ g) ,
    is-section-inverse-construction-CSB D)

 retract-CSB :
  ((x : X) → is-decidable (is-perfect-image f g x)) → retract Y of X
 retract-CSB D =
  ( map-construction-CSB D , map-construction-CSB-has-section D)

 construction-CSB-is-equiv :
  left-cancellable f →
  (D : (x : X) → is-decidable (is-perfect-image f g x))
  → is-equiv (map-construction-CSB D)
 construction-CSB-is-equiv lc-f D =
  lc-retractions-are-equivs (map-construction-CSB D)
   (map-construction-CSB-is-left-cancellable lc-f D)
   (map-construction-CSB-has-section D)

 equiv-CSB :
  left-cancellable f
  → ((x : X) → is-decidable (is-perfect-image f g x))
  → X ≃ Y
 equiv-CSB lc-f D = (map-construction-CSB D , construction-CSB-is-equiv lc-f D)

\end{code}

Finally, we need conditions under which the `is-perfect-image` predicate is
decidable. For this purpose we consider maps with Π-compact fibers. This class
includes complemented embeddings, but is in general much larger. For instance,
the fibers will in general only be weakly complemented, and can include things
like the type ℕ∞, or be complemented and weakly connected in the sense that
equality is double negation dense.

\begin{code}

is-Π-Compact-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                 → (X → Y) → {𝓦 : Universe} → 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
is-Π-Compact-map {𝓤} {𝓥} {X} {Y} f {𝓦} =
 each-fiber-of f (λ T → is-Π-Compact T {𝓦})

id-is-Π-Compact-map : {X : 𝓤 ̇ } → is-Π-Compact-map (𝑖𝑑 X) {𝓦}
id-is-Π-Compact-map {𝓤} {𝓦} {X} x =
 Σ-Compact-types-are-Π-Compact
  (fiber (𝑖𝑑 X) x)
  (singletons-are-Compact (id-is-vv-equiv X x))

∘-is-Π-Compact-map : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {Z : 𝓦 ̇ } {f : X → Y} {g : Y → Z}
                   → is-Π-Compact-map f {𝓤'}
                   → is-Π-Compact-map g {𝓤 ⊔ 𝓥 ⊔ 𝓤'}
                   → is-Π-Compact-map (g ∘ f) {𝓤'}
∘-is-Π-Compact-map {𝓤} {𝓥} {𝓦} {𝓤'} {X} {Y} {Z} {f} {g} αf αg z =
 equiv-Π-Compact'
  (≃-sym (fiber-of-composite f g z))
  (Σ-is-Π-Compact (αg z) (αf ∘ pr₁))

iterate-is-Π-Compact-map : {X : 𝓤 ̇ } {f : X → X}
                         → is-Π-Compact-map f {𝓤 ⊔ 𝓦}
                         → (n : ℕ) → is-Π-Compact-map (f ^ n) {𝓦}
iterate-is-Π-Compact-map αf zero = id-is-Π-Compact-map
iterate-is-Π-Compact-map αf (succ n) =
 ∘-is-Π-Compact-map (iterate-is-Π-Compact-map αf n) αf

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

 perfect-images-at-are-decidable' : is-Π-Compact-map (g ∘ f) {𝓤 ⊔ 𝓥}
                                  → is-complemented-map g
                                  → (x : X) (n : ℕ)
                                  → is-decidable (is-perfect-image-at f g x n)
 perfect-images-at-are-decidable' αgf dg x n =
  iterate-is-Π-Compact-map αgf n x
   (λ (y , _) → fiber g y)
   (λ (x , _) → dg x)

 perfect-images-at-are-decidable : is-Π-Compact-map f {𝓤 ⊔ 𝓥}
                                 → is-Π-Compact-map g {𝓤 ⊔ 𝓥}
                                 → is-¬¬-stable-map g
                                 → (x : X) (n : ℕ)
                                 → is-decidable (is-perfect-image-at f g x n)
 perfect-images-at-are-decidable αf αg ¬¬elim-g =
  perfect-images-at-are-decidable'
   (∘-is-Π-Compact-map αf αg)
   (λ z →
    ¬¬-stable-De-Morgan-types-are-decidable
     (Π-Compact-types-have-decidable-negations (αg z))
     (¬¬elim-g z))

 perfect-images-are-complemented-assuming-WLPO : is-Π-Compact ℕ {𝓤 ⊔ 𝓥}
                                               → is-Π-Compact-map f {𝓤 ⊔ 𝓥}
                                               → is-Π-Compact-map g {𝓤 ⊔ 𝓥}
                                               → is-¬¬-stable-map g
                                               → is-complemented
                                                  (is-perfect-image f g)
 perfect-images-are-complemented-assuming-WLPO wlpo αf αg ¬¬elim-g x =
  wlpo
   (is-perfect-image-at f g x)
   (perfect-images-at-are-decidable αf αg ¬¬elim-g x)

\end{code}

This gives us the conclusion we want.

\begin{code}

module _
 (wlpo : is-Π-Compact ℕ {𝓤 ⊔ 𝓥})
 {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X}
 where

 private
   lemma : is-complemented-map g
         → is-embedding g
         → is-Π-Compact-map f {𝓤 ⊔ 𝓥}
         → (x : X) → is-decidable (is-perfect-image f g x)
   lemma  cg emb-g βf =
    perfect-images-are-complemented-assuming-WLPO wlpo βf
     (λ y →
      Σ-Compact-types-are-Π-Compact
       (fiber g y)
       (compact-types-are-Compact
        (decidable-propositions-are-compact (fiber g y) (emb-g y) (cg y))))
     (λ y → ¬¬-elim (cg y))

 retract-CSB-assuming-WLPO : is-complemented-map g
                           → is-embedding g
                           → is-¬¬-Compact'-map f {𝓤 ⊔ 𝓥}
                           → is-Π-Compact-map f {𝓤 ⊔ 𝓥}
                           → retract Y of X
 retract-CSB-assuming-WLPO cg emb-g αf βf =
  retract-CSB
   (λ y → ¬¬-elim (cg y))
   (embeddings-are-lc g emb-g)
   (αf)
   (lemma cg emb-g βf)

 equiv-CSB-assuming-WLPO : is-complemented-map g
                         → is-embedding g
                         → is-¬¬-Compact'-map f {𝓤 ⊔ 𝓥}
                         → is-Π-Compact-map f {𝓤 ⊔ 𝓥}
                         → left-cancellable f
                         → X ≃ Y
 equiv-CSB-assuming-WLPO cg emb-g αf βf lc-f =
  equiv-CSB
   (λ y → ¬¬-elim (cg y))
   (embeddings-are-lc g emb-g)
   (αf)
   (lc-f)
   (lemma cg emb-g βf)


 equiv-CSB-assuming-WLPO' : is-complemented-map g
                          → is-embedding g
                          → is-complemented-map f
                          → is-embedding f
                          → X ≃ Y
 equiv-CSB-assuming-WLPO' cg emb-g cf emb-f =
  equiv-CSB
   (λ y → ¬¬-elim (cg y))
   (embeddings-are-lc g emb-g)
   (λ y → decidable-types-with-double-negation-dense-equality-are-¬¬-Compact' (cf y) (λ p q → ¬¬-intro (emb-f y p q)))
   (embeddings-are-lc f emb-f)
   (lemma cg emb-g
    (λ y → Σ-Compact-types-are-Π-Compact (fiber f y) (compact-types-are-Compact (decidable-propositions-are-compact (fiber f y) (emb-f y) (cf y)))))

\end{code}

Fredrik Bakke, April 2025

The Cantor-Schröder-Bernstein assuming WLPO in Agda
-------------------------------------------------------------------------

We prove a generalization of the Cantor-Schröder-Bernstein theorem assuming
WLPO. We do not assume function extensionality.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module CantorSchroederBernstein.CSB-WLPO where

open import CantorSchroederBernstein.PerfectImages

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

Using our lemmas about perfect images, the construction is straight forward!

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

Computations with the construction.

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
  (nγ : ¬ is-perfect-image f g (g y)) →
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
\end{code}

The construction is an equivalence.

\begin{code}
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
                         -- The following three imply $f$ is a complemented embedding
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
   (λ y →
    decidable-types-with-double-negation-dense-equality-are-¬¬-Compact'
     (cf y)
     (λ p q → ¬¬-intro (emb-f y p q)))
   (embeddings-are-lc f emb-f)
   (lemma cg emb-g
    (λ y →
     Σ-Compact-types-are-Π-Compact
      (fiber f y)
      (compact-types-are-Compact
       (decidable-propositions-are-compact (fiber f y) (emb-f y) (cf y)))))

\end{code}

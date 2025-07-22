Fredrik Bakke, April 2025

The Cantor-Schröder-Bernstein theorem assuming WLPO in Agda
-----------------------------------------------------------

We prove a generalization of the Cantor-Schröder-Bernstein theorem assuming
the weak limited principle of omniscience.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module CantorSchroederBernstein.CSB-WLPO where

open import CantorSchroederBernstein.PerfectImages

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import TypeTopology.CompactTypes
open import TypeTopology.DenseMapsProperties
open import UF.Embeddings
open import UF.Equiv
open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable
open import UF.Retracts

\end{code}

In this file we consider a generalization of the Cantor–Schröder–Bernstein (CSB)
theorem assuming the weak limited principle of omniscience (WLPO), based on
König's argument.

 Theorem.
 Assuming WLPO, then for every pair of types X and Y, if there are complemented
 embeddings X ↪ Y and Y ↪ X, then X is equivalent to Y.

In particular, we do not assume function extensionality.

This theorem can be viewed as a proper generalization of the
Cantor–Schröder–Bernstein theorem to arbitrary non-topological ∞-topoi, since,
under the assumption of the law of excluded middle (LEM), every embedding is
complemented. On the other hand, It was shown by Pradic and Brown (2022) that
the Cantor–Schröder–Bernstein theorem in its most naïve form implies the law of
excluded middle:

 If it is true that for every pair of sets X and Y, if X injects into Y and Y
 injects into X then X and Y are in bijection, then the law of excluded middle
 holds.

Hence we also know that in the absence of the law of excluded middle, the
hypotheses of the theorem must be strengthened.

Construction
------------

For our formalization we import a series of properties of perfect images from
which the construction is straight forward.

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

 map-construction : (x : X) → is-decidable (is-perfect-image f g x) → Y
 map-construction x (inl γ) = inverse-on-perfect-image x γ
 map-construction x (inr nγ) = f x

 map-construction-CSB :
  ((x : X) → is-decidable (is-perfect-image f g x)) → X → Y
 map-construction-CSB D x = map-construction x (D x)

 map-construction-is-left-cancellable
  : (lc-f : left-cancellable f)
  → {x x' : X}
  → (d : is-decidable (is-perfect-image f g x))
  → (d' : is-decidable (is-perfect-image f g x'))
  → map-construction x d ＝ map-construction x' d'
  → x ＝ x'
 map-construction-is-left-cancellable lc-f {x} {x'} (inl ρ) (inl ρ') p =
  x                                ＝⟨ inverse-on-perfect-image-is-section x ρ ⁻¹ ⟩
  g (inverse-on-perfect-image x ρ) ＝⟨ ap g p ⟩
  g (map-construction x' (inl ρ')) ＝⟨ inverse-on-perfect-image-is-section x' ρ' ⟩
  x'                               ∎
 map-construction-is-left-cancellable lc-f {x} {x'} (inl ρ) (inr nρ') p =
  𝟘-elim (perfect-image-is-disjoint x' x nρ' ρ (p ⁻¹))
 map-construction-is-left-cancellable lc-f {x} {x'} (inr nρ) (inl ρ') p =
  𝟘-elim (perfect-image-is-disjoint x x' nρ ρ' p)
 map-construction-is-left-cancellable lc-f {x} {x'} (inr nρ) (inr nρ') = lc-f

 map-construction-CSB-is-left-cancellable
  : left-cancellable f
  → (D : (x : X) → is-decidable (is-perfect-image f g x))
  → left-cancellable (map-construction-CSB D)
 map-construction-CSB-is-left-cancellable lc-f D {x} {x'} =
  map-construction-is-left-cancellable lc-f (D x) (D x')

\end{code}

Computations with the construction.

\begin{code}

module _ {X        : 𝓤 ̇ }
         {Y        : 𝓥 ̇ }
         {f        : X → Y}
         {g        : Y → X}
         (¬¬elim-g : is-¬¬-stable-map g)
         (lc-g     : left-cancellable g)
         (αf       : is-¬¬-Compact'-map f {𝓤 ⊔ 𝓥})
       where

 compute-construction-on-perfect-image
  : (y : Y)
  → (γ : is-perfect-image f g (g y))
  → (d : is-decidable (is-perfect-image f g (g y)))
  → map-construction (g y) d ＝ y
 compute-construction-on-perfect-image y γ (inl v') =
  inverse-on-perfect-image-is-retraction lc-g y v'
 compute-construction-on-perfect-image y γ (inr v) = 𝟘-elim (v γ)

 compute-construction-on-not-perfect-image
  : (y : Y)
  → (nγ : ¬ is-perfect-image f g (g y))
  → (d : is-decidable
          (is-perfect-image f g
           (element-in-nonperfect-fiber-of-not-perfect-image' αf ¬¬elim-g lc-g y nγ)))
  → map-construction
     (element-in-nonperfect-fiber-of-not-perfect-image' αf ¬¬elim-g lc-g y nγ)
     (d)
    ＝ y
 compute-construction-on-not-perfect-image y nγ (inl v) =
  𝟘-elim (nonperfect-fiber-of-not-perfect-image-is-not-perfect' αf ¬¬elim-g lc-g y nγ v)
 compute-construction-on-not-perfect-image y nγ (inr _) =
  compute-element-in-nonperfect-fiber-of-not-perfect-image' αf ¬¬elim-g lc-g y nγ

\end{code}

The construction is an equivalence.

\begin{code}

 inverse-construction
  : (y : Y) → is-decidable (is-perfect-image f g (g y)) → X
 inverse-construction y (inl _) = g y
 inverse-construction y (inr nγ) =
   element-in-nonperfect-fiber-of-not-perfect-image' αf ¬¬elim-g lc-g y nγ

 construction-is-retraction
  : (y : Y)
  → (d : is-decidable (is-perfect-image f g (g y)))
  → (d' : is-decidable (is-perfect-image f g (inverse-construction y d)))
  → map-construction (inverse-construction y d) d' ＝ y
 construction-is-retraction y (inl γ) =
   compute-construction-on-perfect-image y γ
 construction-is-retraction y (inr nγ) =
   compute-construction-on-not-perfect-image y nγ

 inverse-construction-CSB
  : ((y : Y) → is-decidable (is-perfect-image f g (g y))) → Y → X
 inverse-construction-CSB D y = inverse-construction y (D y)

 is-section-inverse-construction-CSB
  : (D : (x : X) → is-decidable (is-perfect-image f g x))
  → map-construction-CSB D ∘ inverse-construction-CSB (D ∘ g) ∼ id
 is-section-inverse-construction-CSB D y =
   construction-is-retraction y
    (D (g y))
    (D (inverse-construction-CSB (D ∘ g) y))

 map-construction-CSB-has-section
  : (D : (x : X) → is-decidable (is-perfect-image f g x))
  → has-section (map-construction-CSB D)
 map-construction-CSB-has-section D =
  (inverse-construction-CSB (D ∘ g) , is-section-inverse-construction-CSB D)

 retract-CSB
   : ((x : X) → is-decidable (is-perfect-image f g x)) → retract Y of X
 retract-CSB D =
  (map-construction-CSB D , map-construction-CSB-has-section D)

 construction-CSB-is-equiv
  : left-cancellable f
  → (D : (x : X) → is-decidable (is-perfect-image f g x))
  → is-equiv (map-construction-CSB D)
 construction-CSB-is-equiv lc-f D =
  lc-retractions-are-equivs (map-construction-CSB D)
   (map-construction-CSB-is-left-cancellable lc-f D)
   (map-construction-CSB-has-section D)

 equiv-CSB
  : left-cancellable f
  → ((x : X) → is-decidable (is-perfect-image f g x))
  → X ≃ Y
 equiv-CSB lc-f D = (map-construction-CSB D , construction-CSB-is-equiv lc-f D)

\end{code}

Note in particular that the above definition gives us a fully constructive
version of König's argument:

If f and g are such that

 1. g is left cancellable and ¬¬-stable,
 2. f is left cancellable and has ¬¬-compact fibers
 3. the perfect image of g relative to f is complemented

then X ≃ Y.

Now, if WLPO holds and f and g are complemented embeddings we can show that the
perfect image is always complemented, hence deriving our main result.

\begin{code}

module _ (wlpo : is-Π-Compact ℕ {𝓤 ⊔ 𝓥})
         {X    : 𝓤 ̇ }
         {Y    : 𝓥 ̇ }
         {f    : X → Y}
         {g    : Y → X}
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

\end{code}

In the preceding definition, the three assumptions on f imply that it is a
complemented embedding.

\begin{code}

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

References
----------

 - Cantor-Bernstein implies Excluded Middle
   (Pradic & Brown 2022, https://arxiv.org/abs/1904.09193).

 - The Cantor–Schröder–Bernstein theorem in ∞-Topoi, slides
   (Bakke 2025, https://hott-uf.github.io/2025/slides/Bakke.pdf)

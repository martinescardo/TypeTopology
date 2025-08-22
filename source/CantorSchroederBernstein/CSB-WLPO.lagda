Fredrik Bakke, April 2025

The Cantor-Schröder-Bernstein theorem assuming WLPO in Agda
───────────────────────────────────────────────────────────

We prove a generalization of the Cantor-Schröder-Bernstein theorem assuming
the weak limited principle of omniscience.

\begin{code}

{-# OPTIONS --safe --without-K #-}

module CantorSchroederBernstein.CSB-WLPO where

open import CantorSchroederBernstein.PerfectImages

open import MLTT.Plus-Properties
open import MLTT.Spartan
open import Taboos.WLPO
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
König's argument (1906).

 Theorem.
 Assuming WLPO, then for every pair of types X and Y, if there are complemented
 embeddings X ↪ Y and Y ↪ X, then X is equivalent to Y.

In particular, we do not assume function extensionality.

This theorem can be viewed as a generalization of the Cantor–Schröder–Bernstein
theorem to arbitrary non-topological ∞-topoi, since, under the assumption of the
law of excluded middle (LEM), every embedding is complemented. On the other
hand, It was shown by Pradic and Brown (2022) that the Cantor–Schröder–Bernstein
theorem in its most naïve form implies the law of excluded middle:

 If it is true that for every pair of sets X and Y, if X injects into Y and Y
 injects into X then X and Y are in bijection, then the law of excluded middle
 holds.

Hence we also know that in the absence of the law of excluded middle, the
hypotheses of the theorem must be strengthened.

Construction
────────────

For our formalization we import a series of properties of perfect images from
which the construction is straightforward.

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

 CSB-construction-map'
  : (x : X) → is-decidable (is-perfect-image f g x) → Y
 CSB-construction-map' x (inl γ) = inverse-on-perfect-image x γ
 CSB-construction-map' x (inr nγ) = f x

 CSB-construction-map
  : ((x : X) → is-decidable (is-perfect-image f g x)) → X → Y
 CSB-construction-map D x = CSB-construction-map' x (D x)

 CSB-construction-map-is-left-cancellable'
  : (lc-f : left-cancellable f)
  → {x x' : X}
  → (d : is-decidable (is-perfect-image f g x))
  → (d' : is-decidable (is-perfect-image f g x'))
  → CSB-construction-map' x d ＝ CSB-construction-map' x' d'
  → x ＝ x'
 CSB-construction-map-is-left-cancellable' lc-f {x} {x'} (inl ρ) (inl ρ') p =
  x                                     ＝⟨ inverse-on-perfect-image-is-section x ρ ⁻¹ ⟩
  g (inverse-on-perfect-image x ρ)      ＝⟨ ap g p ⟩
  g (CSB-construction-map' x' (inl ρ')) ＝⟨ inverse-on-perfect-image-is-section x' ρ' ⟩
  x'                                    ∎
 CSB-construction-map-is-left-cancellable' lc-f {x} {x'} (inl ρ) (inr nρ') p =
  𝟘-elim (perfect-image-is-disjoint x' x nρ' ρ (p ⁻¹))
 CSB-construction-map-is-left-cancellable' lc-f {x} {x'} (inr nρ) (inl ρ') p =
  𝟘-elim (perfect-image-is-disjoint x x' nρ ρ' p)
 CSB-construction-map-is-left-cancellable' lc-f {x} {x'} (inr nρ) (inr nρ') =
  lc-f

 CSB-construction-map-is-left-cancellable
  : left-cancellable f
  → (D : (x : X) → is-decidable (is-perfect-image f g x))
  → left-cancellable (CSB-construction-map D)
 CSB-construction-map-is-left-cancellable lc-f D {x} {x'} =
  CSB-construction-map-is-left-cancellable' lc-f (D x) (D x')

\end{code}

We compute how the constructed map behaves on the perfect image and its
complement.

\begin{code}

module _ {X        : 𝓤 ̇ }
         {Y        : 𝓥 ̇ }
         {f        : X → Y}
         {g        : Y → X}
         (¬¬elim-g : is-¬¬-stable-map g)
         (lc-g     : left-cancellable g)
         (αf       : is-¬¬-Compact'-map f {𝓤 ⊔ 𝓥})
       where

 CSB-construction-map-on-perfect-image
  : (y : Y)
  → (γ : is-perfect-image f g (g y))
  → (d : is-decidable (is-perfect-image f g (g y)))
  → CSB-construction-map' (g y) d ＝ y
 CSB-construction-map-on-perfect-image y γ (inl v') =
  inverse-on-perfect-image-is-retraction lc-g y v'
 CSB-construction-map-on-perfect-image y γ (inr v) =
  𝟘-elim (v γ)

 CSB-construction-map-on-not-perfect-image
  : (y : Y)
  → (nγ : ¬ is-perfect-image f g (g y))
  → (d : is-decidable
          (is-perfect-image f g
           (element-in-nonperfect-fiber-of-not-perfect-image'
             αf ¬¬elim-g lc-g y nγ)))
  → CSB-construction-map'
     (element-in-nonperfect-fiber-of-not-perfect-image'
       αf ¬¬elim-g lc-g y nγ)
     (d)
    ＝ y
 CSB-construction-map-on-not-perfect-image y nγ (inl v) =
  𝟘-elim
   (nonperfect-fiber-of-not-perfect-image-is-not-perfect'
     αf ¬¬elim-g lc-g y nγ v)
 CSB-construction-map-on-not-perfect-image y nγ (inr _) =
  compute-element-in-nonperfect-fiber-of-not-perfect-image'
   αf ¬¬elim-g lc-g y nγ

\end{code}

The construction is an equivalence.

\begin{code}

 CSB-construction-inverse-map'
  : (y : Y) → is-decidable (is-perfect-image f g (g y)) → X
 CSB-construction-inverse-map' y (inl _) =
  g y
 CSB-construction-inverse-map' y (inr nγ) =
  element-in-nonperfect-fiber-of-not-perfect-image' αf ¬¬elim-g lc-g y nγ

 CSB-construction-map-is-retraction'
  : (y : Y)
  → (d : is-decidable (is-perfect-image f g (g y)))
  → (d' : is-decidable
           (is-perfect-image f g (CSB-construction-inverse-map' y d)))
  → CSB-construction-map' (CSB-construction-inverse-map' y d) d' ＝ y
 CSB-construction-map-is-retraction' y (inl γ) =
  CSB-construction-map-on-perfect-image y γ
 CSB-construction-map-is-retraction' y (inr nγ) =
  CSB-construction-map-on-not-perfect-image y nγ

 CSB-construction-inverse-map
  : ((y : Y) → is-decidable (is-perfect-image f g (g y))) → Y → X
 CSB-construction-inverse-map D y =
  CSB-construction-inverse-map' y (D y)

 CSB-construction-map-is-retraction
  : (D : (x : X) → is-decidable (is-perfect-image f g x))
  → CSB-construction-map D ∘ CSB-construction-inverse-map (D ∘ g) ∼ id
 CSB-construction-map-is-retraction D y =
   CSB-construction-map-is-retraction' y
    (D (g y))
    (D (CSB-construction-inverse-map (D ∘ g) y))

 CSB-construction-map-has-section
  : (D : (x : X) → is-decidable (is-perfect-image f g x))
  → has-section (CSB-construction-map D)
 CSB-construction-map-has-section D =
  (CSB-construction-inverse-map (D ∘ g) , CSB-construction-map-is-retraction D)

 CSB-construction-retract
   : ((x : X) → is-decidable (is-perfect-image f g x)) → retract Y of X
 CSB-construction-retract D =
  (CSB-construction-map D , CSB-construction-map-has-section D)

 CSB-construction-is-equiv
  : left-cancellable f
  → (D : (x : X) → is-decidable (is-perfect-image f g x))
  → is-equiv (CSB-construction-map D)
 CSB-construction-is-equiv lc-f D =
  lc-retractions-are-equivs
   (CSB-construction-map D)
   (CSB-construction-map-is-left-cancellable lc-f D)
   (CSB-construction-map-has-section D)

 CSB-construction-equiv
  : left-cancellable f
  → ((x : X) → is-decidable (is-perfect-image f g x))
  → X ≃ Y
 CSB-construction-equiv lc-f D =
  (CSB-construction-map D , CSB-construction-is-equiv lc-f D)

\end{code}

Note in particular that the above definition gives us a fully constructive
version of König's argument:

 Proposition.
 Given maps f : X → Y and g : Y → X such that

  1. g is left cancellable and ¬¬-stable,
  2. f is left cancellable and has ¬¬-compact fibers
  3. the perfect image of g relative to f is complemented

 then X ≃ Y.

Now, if WLPO holds and f and g are complemented embeddings we can show that the
perfect image is always complemented, hence we can apply the above proposition
and derive our main result.

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

 CSB-retract-assuming-WLPO' : is-complemented-map g
                            → is-embedding g
                            → is-¬¬-Compact'-map f {𝓤 ⊔ 𝓥}
                            → is-Π-Compact-map f {𝓤 ⊔ 𝓥}
                            → retract Y of X
 CSB-retract-assuming-WLPO' cg emb-g αf βf =
  CSB-construction-retract
   (λ y → ¬¬-elim (cg y))
   (embeddings-are-lc g emb-g)
   (αf)
   (lemma cg emb-g βf)

 CSB-equiv-assuming-WLPO' : is-complemented-map g
                          → is-embedding g
                          → is-¬¬-Compact'-map f {𝓤 ⊔ 𝓥}
                          → is-Π-Compact-map f {𝓤 ⊔ 𝓥}
                          → left-cancellable f
                          → X ≃ Y
 CSB-equiv-assuming-WLPO' cg emb-g αf βf lc-f =
  CSB-construction-equiv
   (λ y → ¬¬-elim (cg y))
   (embeddings-are-lc g emb-g)
   (αf)
   (lc-f)
   (lemma cg emb-g βf)

\end{code}

In the preceding definition the three assumptions on f are equivalent to f being
a complemented embedding. We formalize that they at least follow from the
latter.

\begin{code}

 CSB-equiv-assuming-WLPO : is-complemented-map g
                         → is-embedding g
                         → is-complemented-map f
                         → is-embedding f
                         → X ≃ Y
 CSB-equiv-assuming-WLPO cg emb-g cf emb-f =
  CSB-construction-equiv
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

Finally, to dispell all doubt, we instantiate the previous theorem at the
traditional phrasing of WLPO.

\begin{code}

is-Π-compact : 𝓤 ̇ → 𝓤 ̇
is-Π-compact X = (p : X → 𝟚) → is-decidable ((x : X) → p x ＝ ₁)

Π-compact-types-are-Π-Compact : {X : 𝓤 ̇ } → is-Π-compact X → is-Π-Compact X {𝓥}
Π-compact-types-are-Π-Compact {𝓤} {𝓥} {X} H A δ =
 +functor
  (λ na  x → cases
              (id)
              (𝟘-elim ∘ characteristic-map-property₁ ¬A ¬δ x (na x))
              (δ x))
  (λ nna f → nna
              (λ x → characteristic-map-property₁-back ¬A ¬δ x
                      (¬¬-intro (f x))))
  (H (characteristic-map ¬A ¬δ))
  where
   ¬A : X → 𝓥 ̇
   ¬A x = ¬ (A x)

   ¬δ : is-complemented ¬A
   ¬δ x = decidable-types-are-closed-under-negations (δ x)

CSB-equiv-assuming-traditional-WLPO : WLPO-traditional
                                    → {X : 𝓤 ̇ }
                                    → {Y : 𝓥 ̇ }
                                    → {f : X → Y}
                                    → {g : Y → X}
                                    → is-complemented-map g
                                    → is-embedding g
                                    → is-complemented-map f
                                    → is-embedding f
                                    → X ≃ Y
CSB-equiv-assuming-traditional-WLPO wlpo =
 CSB-equiv-assuming-WLPO (Π-compact-types-are-Π-Compact wlpo)

\end{code}

References
──────────
 - König, 1906. Sur la théorie des ensembles.
   https://gallica.bnf.fr/ark:/12148/bpt6k30977.image.f110.langEN

 - Pradic & Brown, 2022. Cantor-Bernstein implies Excluded Middle.
   https://arxiv.org/abs/1904.09193

 - Bakke, 2025. The Cantor–Schröder–Bernstein theorem in ∞-Topoi.
   https://hott-uf.github.io/2025/slides/Bakke.pdf (slides)

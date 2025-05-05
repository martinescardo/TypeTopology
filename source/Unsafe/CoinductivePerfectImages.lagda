Fredrik Bakke, 7-8 April 2025.

\begin{code}

{-# OPTIONS --without-K --guardedness #-}

module Unsafe.CoinductivePerfectImages where

open import MLTT.Spartan
open import CantorSchroederBernstein.PerfectImages
open import TypeTopology.Density
open import NotionsOfDecidability.Complemented
open import NotionsOfDecidability.Decidable
open import TypeTopology.DenseMapsProperties

record is-coinductive-perfect-image
 {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (g : Y → X) (x : X) : 𝓤 ⊔ 𝓥 ̇  where
 coinductive
 field
  y : Y
  eq : g y ＝ x
  coind : (x₀ : X) → y ＝ f x₀ → is-coinductive-perfect-image f g x₀

open is-coinductive-perfect-image public

record similarity-of-the-coinductive-perfect-image-predicate
  {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} {x : X}
  (u v : is-coinductive-perfect-image f g x) : 𝓤 ⊔ 𝓥 ̇  where
  coinductive
  field
    eq-y : u .y ＝ v .y
    eq-eq : u .eq ＝ ap g eq-y ∙' v .eq
    eq-coind
      : (x₀ : X) (p : v .y ＝ f x₀)
      → similarity-of-the-coinductive-perfect-image-predicate (u .coind x₀ (eq-y ∙' p)) (v .coind x₀ p)

open similarity-of-the-coinductive-perfect-image-predicate public

\end{code}

Extended perfect images are perfect images. Again we must assume
left-cancellability of g.

\begin{code}
module _
 {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} (lc-g : left-cancellable g)
 where

 coinductive-perfect-images-are-perfect-images :
  (x : X) → is-coinductive-perfect-image f g x → is-perfect-image f g x
 coinductive-perfect-images-are-perfect-images x ρ zero (x₀ , q) =
  (ρ .y , (ρ .eq ∙ q ⁻¹))
 coinductive-perfect-images-are-perfect-images x ρ (succ n) (x₀ , q) =
   coinductive-perfect-images-are-perfect-images
    (((g ∘ f) ^ n) x₀)
    (ρ .coind (((g ∘ f) ^ n) x₀) (lc-g (ρ .eq ∙ q ⁻¹)))
    (n)
    (x₀ , refl)

 perfect-images-are-coinductive-perfect-images :
  (x : X) → is-perfect-image f g x → is-coinductive-perfect-image f g x
 perfect-images-are-coinductive-perfect-images x ρ .y = ρ 0 (x , refl) .pr₁
 perfect-images-are-coinductive-perfect-images x ρ .eq = ρ 0 (x , refl) .pr₂
 perfect-images-are-coinductive-perfect-images x ρ .coind x₀ p₀ =
  perfect-images-are-coinductive-perfect-images x₀
   (λ n (x₁ , p₁) →
    ρ (succ n) (x₁ , (ap (g ∘ f) p₁ ∙ ap g (p₀ ⁻¹) ∙ ρ 0 (x , refl) .pr₂)))

--  coinductive-perfect-images-are-perfect-images-is-a-retraction
--   : (x : X) (u : is-coinductive-perfect-image f g x)
--   → similarity-of-the-coinductive-perfect-image-predicate
--      (perfect-images-are-coinductive-perfect-images x
--       (coinductive-perfect-images-are-perfect-images x u))
--      u
--  coinductive-perfect-images-are-perfect-images-is-a-retraction x u .eq-y = refl
--  coinductive-perfect-images-are-perfect-images-is-a-retraction x u .eq-eq = refl
--  coinductive-perfect-images-are-perfect-images-is-a-retraction x u .eq-coind x₀ p₀ = {!   !}

\end{code}

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

 has-section-on-coinductive-perfect-image
  : (x : X)
  → is-coinductive-perfect-image f g x
  → fiber g x
 has-section-on-coinductive-perfect-image x ρ = ρ .y , ρ .eq

 inverse-on-coinductive-perfect-image
  : (x : X)
  → is-coinductive-perfect-image f g x
  → Y
 inverse-on-coinductive-perfect-image x ρ =
  pr₁ (has-section-on-coinductive-perfect-image x ρ)

 inverse-on-coinductive-perfect-image-is-section
  : (x : X)
  → (ρ : is-coinductive-perfect-image f g x)
  → g (inverse-on-coinductive-perfect-image x ρ) ＝ x
 inverse-on-coinductive-perfect-image-is-section x ρ =
  pr₂ (has-section-on-coinductive-perfect-image x ρ)

 inverse-on-coinductive-perfect-image-is-retraction
  : left-cancellable g
  → (y : Y)
  → (ρ : is-coinductive-perfect-image f g (g y))
  → inverse-on-coinductive-perfect-image (g y) ρ ＝ y
 inverse-on-coinductive-perfect-image-is-retraction lc-g y ρ =
  lc-g (inverse-on-coinductive-perfect-image-is-section (g y) ρ)

\end{code}

If g (f x) is a perfect image then so is x.

\begin{code}

 previous-coinductive-perfect-image
  : left-cancellable g
  → (x : X)
  → is-coinductive-perfect-image f g (g (f x))
  → is-coinductive-perfect-image f g x
 previous-coinductive-perfect-image lc-g x ρ = ρ .coind x (lc-g (ρ .eq))

\end{code}

The perfect image of g relative to f is disjoint from the image of f.

\begin{code}

 coinductive-perfect-image-is-disjoint
  : left-cancellable g
  → (x x₀ : X)
  → ¬ is-coinductive-perfect-image f g x
  → (ρ : is-coinductive-perfect-image f g x₀)
  → f x ≠ inverse-on-coinductive-perfect-image x₀ ρ
 coinductive-perfect-image-is-disjoint lc-g x x₀ nρ ρ p = v ρ
  where
   q : g (f x) ＝ x₀
   q = ap g p ∙ inverse-on-coinductive-perfect-image-is-section x₀ ρ

   s : ¬ is-coinductive-perfect-image f g (g (f x))
   s = contrapositive (previous-coinductive-perfect-image lc-g x) nρ

   v : ¬ is-coinductive-perfect-image f g x₀
   v = transport (λ x' → ¬ is-coinductive-perfect-image f g x') q s

\end{code}

Double negation elimination on extended nonperfect fibers.

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (g : Y → X) where

 has-extended-nonperfect-fiber : Y → 𝓤 ⊔ 𝓥 ̇
 has-extended-nonperfect-fiber y =
  Σ (x₀ , _) ꞉ fiber f y , ¬ is-coinductive-perfect-image f g x₀

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

 double-negation-elimination-on-coinductive-perfect-image
  : is-¬¬-stable-map g
  → (x : X)
  → ¬ is-nonperfect-image f g x
  → is-coinductive-perfect-image f g x
 double-negation-elimination-on-coinductive-perfect-image ¬¬elim-g x nρ .y =
  ¬¬elim-g x (λ nq → nρ (x , 0 , refl , nq)) .pr₁
 double-negation-elimination-on-coinductive-perfect-image ¬¬elim-g x nρ .eq =
  ¬¬elim-g x (λ nq → nρ (x , 0 , refl , nq)) .pr₂
 double-negation-elimination-on-coinductive-perfect-image
  ¬¬elim-g x nρ .coind x₀ p =
  double-negation-elimination-on-coinductive-perfect-image ¬¬elim-g x₀
   (λ (y₀ , n , s , nq₀) →
    nρ (y₀ , succ n
       , (ap g (ap f s ∙ p ⁻¹) ∙ pr₂ (¬¬elim-g x (λ nq → nρ (x , 0 , refl , nq))))
       , nq₀))

\end{code}

If g y is not a perfect image, then f has a fiber over y, f x ＝ y, that is not
a perfect image of g. We assume that g is ¬¬-stable and left-cancellable,
although note that this implies g is an embedding (at least if we assume
negations are propositions).

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

 extended-not-perfect-images-are-not-not-nonperfect
  : is-¬¬-stable-map g
  → (y : Y)
  → ¬ is-coinductive-perfect-image f g (g y)
  → ¬¬ is-nonperfect-image f g (g y)
 extended-not-perfect-images-are-not-not-nonperfect ¬¬elim-g y nρ nμ =
   nρ (double-negation-elimination-on-coinductive-perfect-image ¬¬elim-g (g y) nμ)

 nonperfect-images-have-extended-nonperfect-fibers
  : left-cancellable g
  → (y : Y)
  → is-nonperfect-image f g (g y)
  → has-extended-nonperfect-fiber f g y
 nonperfect-images-have-extended-nonperfect-fibers lc-g y (x₀ , zero , p , v) =
  𝟘-elim (v (y , (p ⁻¹)))
 nonperfect-images-have-extended-nonperfect-fibers lc-g y (x₀ , succ n , p , v) =
  (((g ∘ f) ^ n) x₀ , lc-g p) , (λ μ → v (coinductive-perfect-images-are-perfect-images lc-g (((g ∘ f) ^ n) x₀) μ n (x₀ , refl)))

 extended-not-perfect-images-dont-not-have-nonperfect-fibers
  : is-¬¬-stable-map g
  → left-cancellable g
  → (y : Y)
  → ¬ is-coinductive-perfect-image f g (g y)
  → ¬¬ has-extended-nonperfect-fiber f g y
 extended-not-perfect-images-dont-not-have-nonperfect-fibers ¬¬elim-g lc-g y nρ nnμ =
  extended-not-perfect-images-are-not-not-nonperfect ¬¬elim-g y nρ
   (nnμ ∘ nonperfect-images-have-extended-nonperfect-fibers lc-g y)

\end{code}


If f has ¬¬-compact fibers (e.g., if f is a complemented embedding),
then the extended nonperfect fibers of g are ¬¬-stable.

\begin{code}

module _
 {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X}
 (αf : is-¬¬-Compact'-map f {𝓤 ⊔ 𝓥})
 where

 extended-nonperfect-fibers-are-¬¬-stable' : (y : Y)
                                           → ¬¬-stable (has-extended-nonperfect-fiber f g y)
 extended-nonperfect-fibers-are-¬¬-stable' y =
  αf y (λ (x , p) → ¬ is-coinductive-perfect-image f g x) (λ _ → three-negations-imply-one)

 module _
  (¬¬elim-g : is-¬¬-stable-map g)
  (lc-g : left-cancellable g)
  (y : Y)
  (nρ : ¬ is-coinductive-perfect-image f g (g y))
  where

  not-perfect-images-have-extended-nonperfect-fibers' : has-extended-nonperfect-fiber f g y
  not-perfect-images-have-extended-nonperfect-fibers' =
   extended-nonperfect-fibers-are-¬¬-stable' y
    (extended-not-perfect-images-dont-not-have-nonperfect-fibers ¬¬elim-g lc-g y nρ)

  underlying-fiber-of-extended-nonperfect-fiber-of-not-perfect-image' : fiber f y
  underlying-fiber-of-extended-nonperfect-fiber-of-not-perfect-image' =
   pr₁ (not-perfect-images-have-extended-nonperfect-fibers')

  element-in-extended-nonperfect-fiber-of-extended-not-perfect-image' : X
  element-in-extended-nonperfect-fiber-of-extended-not-perfect-image' =
   pr₁ (underlying-fiber-of-extended-nonperfect-fiber-of-not-perfect-image')

  compute-element-in-extended-nonperfect-fiber-of-extended-not-perfect-image'
   : f element-in-extended-nonperfect-fiber-of-extended-not-perfect-image' ＝ y
  compute-element-in-extended-nonperfect-fiber-of-extended-not-perfect-image' =
   pr₂ underlying-fiber-of-extended-nonperfect-fiber-of-not-perfect-image'

  extended-nonperfect-fiber-of-not-coinductive-perfect-image-is-not-extended-perfect'
   : ¬ is-coinductive-perfect-image f g element-in-extended-nonperfect-fiber-of-extended-not-perfect-image'
  extended-nonperfect-fiber-of-not-coinductive-perfect-image-is-not-extended-perfect' =
   pr₂ not-perfect-images-have-extended-nonperfect-fibers'

\end{code}


Finally, we need conditions under which `is-coinductive-perfect-image` predicate is
decidable. For this purpose we consider maps with Π-compact fibers. This class
includes complemented embeddings, but is in general much larger. For instance,
the fibers will in general only be weakly complemented, and can include things
like the type ℕ∞, or be complemented and weakly connected in the sense that
equality is double negation dense.

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

--  perfect-images-at-are-decidable' : is-Π-Compact-map (g ∘ f) {𝓤 ⊔ 𝓥}
--                                   → is-complemented-map g
--                                   → (x : X) (n : ℕ)
--                                   → is-decidable (is-perfect-image-at f g x n)
--  perfect-images-at-are-decidable' αgf dg x n =
--   iterate-is-Π-Compact-map αgf n x
--    (λ (y , _) → fiber g y)
--    (λ (x , _) → dg x)

--  perfect-images-at-are-decidable : is-Π-Compact-map f {𝓤 ⊔ 𝓥}
--                                  → is-Π-Compact-map g {𝓤 ⊔ 𝓥}
--                                  → is-¬¬-stable-map g
--                                  → (x : X) (n : ℕ)
--                                  → is-decidable (is-perfect-image-at f g x n)
--  perfect-images-at-are-decidable αf αg ¬¬elim-g =
--   perfect-images-at-are-decidable'
--    (∘-is-Π-Compact-map αf αg)
--    (λ z →
--     ¬¬-stable-De-Morgan-types-are-decidable
--      (Π-Compact-types-have-decidable-negations (αg z))
--      (¬¬elim-g z))


--  coinductive-perfect-images-are-complemented
--   : is-Π-Compact-map f {𝓤 ⊔ 𝓥}
--   → is-Π-Compact-map g {𝓤 ⊔ 𝓥}
--   → is-complemented-map f
--   → is-complemented-map g
--   → is-complemented (is-coinductive-perfect-image f g)
--  coinductive-perfect-images-are-complemented αf αg cf cg x =
--   decidable-↔ {!   !} (αg x {!   !} {!   !})

\end{code}

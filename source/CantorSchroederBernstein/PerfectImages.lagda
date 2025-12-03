Fredrik Bakke, April 2025

Perfect images
──────────────

\begin{code}

{-# OPTIONS --safe --without-K #-}

module CantorSchroederBernstein.PerfectImages where

open import MLTT.Spartan
open import TypeTopology.CompactTypes
open import TypeTopology.DenseMapsProperties
open import UF.Equiv
open import UF.EquivalenceExamples
open import NotionsOfDecidability.Complemented
open import UF.NotNotStablePropositions
open import UF.Subsingletons

\end{code}

We introduce the concept of perfect images as used by König in his argument
(1906) for the Cantor–Schröder–Bernstein theorem, and study logical properties
of it. In CantorSchroederBernstein.CSB-WLPO we use these properties to give a
generalization of the Cantor–Schröder–Bernstein theorem assuming the weak
limited principle of omniscience.

Definition.
Given maps f : X → Y and g : Y → X, then an element x : X is said to be a
"perfect image" of g relative to f, if for every natural number n and every
preimage x₀ of x under (g ∘ f)ⁿ, i.e., (g ∘ f)ⁿ x₀ = x, then x₀ has a further
preimage under g.

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (g : Y → X) where

 is-perfect-image-at : X → ℕ → 𝓤 ⊔ 𝓥 ̇
 is-perfect-image-at x n =
   ((x₀ , _) : fiber ((g ∘ f) ^ n) x) → fiber g x₀

 is-perfect-image : X → 𝓤 ⊔ 𝓥 ̇
 is-perfect-image x = (n : ℕ) → is-perfect-image-at x n

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
                           → ¬ is-perfect-image f g x
                           → (ρ : is-perfect-image f g x₀)
                           → f x ≠ inverse-on-perfect-image x₀ ρ
 perfect-image-is-disjoint x x₀ nρ ρ p = v ρ
  where
   q : g (f x) ＝ x₀
   q = ap g p ∙ inverse-on-perfect-image-is-section x₀ ρ

   s : ¬ is-perfect-image f g (g (f x))
   s = contrapositive (previous-perfect-image x) nρ

   v : ¬ is-perfect-image f g x₀
   v = transport (λ x' → ¬ is-perfect-image f g x') q s

\end{code}

Double negation elimination on nonperfect fibers.

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (f : X → Y) (g : Y → X) where

 is-nonperfect-image : X → 𝓤 ⊔ 𝓥 ̇
 is-nonperfect-image x =
  Σ x₀ ꞉ X , Σ n ꞉ ℕ , (((g ∘ f) ^ n) x₀ ＝ x) × (¬ fiber g x₀)

 has-nonperfect-fiber : Y → 𝓤 ⊔ 𝓥 ̇
 has-nonperfect-fiber y =
  Σ (x₀ , _) ꞉ fiber f y , ¬ is-perfect-image f g x₀

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

 double-negation-elimination-on-perfect-image : is-¬¬-stable-map g
                                              → (x : X)
                                              → ¬ is-nonperfect-image f g x
                                              → is-perfect-image f g x
 double-negation-elimination-on-perfect-image ¬¬elim-g x nρ n (x₀ , p) =
  ¬¬elim-g x₀ (λ x₁ → nρ (x₀ , n , p , x₁))

\end{code}

If g y is not a perfect image, then f has a fiber over y, f x ＝ y, that is not
a perfect image of g.

Note that in the formalization we assume that g is ¬¬-stable and
left-cancellable, though this implies that g is an embedding if negations are
propositions, which is for instance true if function extensionality holds.

\begin{code}

module _ {X : 𝓤 ̇ } {Y : 𝓥 ̇ } {f : X → Y} {g : Y → X} where

 not-perfect-images-are-not-not-nonperfect
  : is-¬¬-stable-map g
  → (y : Y)
  → ¬ is-perfect-image f g (g y)
  → ¬¬ is-nonperfect-image f g (g y)
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
  → ¬ is-perfect-image f g (g y)
  → ¬¬ has-nonperfect-fiber f g y
 not-perfect-images-dont-not-have-nonperfect-fibers ¬¬elim-g lc-g y nρ nnμ =
  not-perfect-images-are-not-not-nonperfect ¬¬elim-g y nρ
   (nnμ ∘ nonperfect-images-have-nonperfect-fibers lc-g y)

\end{code}

Double negation elimination on nonperfect fibers.

We introduce the concept of a ¬¬-compact type and show that if the map f has
¬¬-compact fibers (e.g. if f is a complemented embedding) then the nonperfect
fibers of g are ¬¬-stable.

Definition.
A type A is "¬¬-compact" if for every family of types B : A → 𝓤 that satisfy
double negation elimination

 (x : A) → ¬¬ B x → B x,

the dependent sum (Σ (a ꞉ A), B a) again satisfies double negation elimination.

\begin{code}

is-¬¬-Compact' : 𝓤 ̇  → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
is-¬¬-Compact' {𝓤} A {𝓥} =
 (B : A → 𝓥 ̇ ) → ((x : A) → ¬¬ B x → B x) → ¬¬ Σ B → Σ B

is-¬¬-Compact'-map : {X : 𝓤 ̇ }
                   → {Y : 𝓥 ̇ }
                   → (X → Y)
                   → {𝓦 : Universe}
                   → 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
is-¬¬-Compact'-map {𝓤} {𝓥} {X} {Y} f {𝓦} =
 each-fiber-of f (λ T → is-¬¬-Compact' T {𝓦})

decidable-types-with-double-negation-dense-equality-are-¬¬-Compact'
 : {A : 𝓤 ̇ }
 → is-decidable A
 → ((x y : A) → ¬¬ (x ＝ y))
 → is-¬¬-Compact' A {𝓦}
decidable-types-with-double-negation-dense-equality-are-¬¬-Compact' d H =
  cases
   (λ x B ¬¬elim nnab →
    x ,
    ¬¬elim x (λ nb → nnab (λ (x' , b') → H x' x (λ p → nb (transport B p b')))))
   (λ nx B ¬¬elim nnab → 𝟘-elim (nnab (λ (x , b) → nx x))) d

is-¬¬-Compact : 𝓤 ̇  → {𝓥 : Universe} → 𝓤 ⊔ (𝓥 ⁺) ̇
is-¬¬-Compact {𝓤} A {𝓥} =
 (B : A → Ω¬¬ 𝓥) → ¬¬ (Σ a ꞉ A , (B a holds¬¬)) → Σ a ꞉ A , (B a holds¬¬)

¬¬-Compact-types-are-¬¬-stable : {A : 𝓤 ̇ }
                               → is-¬¬-Compact A {𝓤}
                               → ¬¬-stable A
¬¬-Compact-types-are-¬¬-stable α nna =
 pr₁ (α (λ _ → ((𝟙 , 𝟙-is-prop) , λ _ → ⋆)) (¬¬-functor (λ a → a , ⋆) nna))

¬¬-Compact'-types-are-¬¬-stable : {A : 𝓤 ̇ }
                                → is-¬¬-Compact' A {𝓤}
                                → ¬¬-stable A
¬¬-Compact'-types-are-¬¬-stable α nna =
 pr₁ (α (λ _ → 𝟙) (λ _ _ → ⋆) (¬¬-functor (λ a → a , ⋆) nna))

\end{code}

If f has ¬¬-compact fibers then the nonperfect fibers of g are ¬¬-stable.

\begin{code}

module _ {X  : 𝓤 ̇ }
         {Y  : 𝓥 ̇ }
         {f  : X → Y}
         {g  : Y → X}
         (αf : is-¬¬-Compact'-map f)
       where

 nonperfect-fibers-are-¬¬-stable' : (y : Y)
                                  → ¬¬-stable (has-nonperfect-fiber f g y)
 nonperfect-fibers-are-¬¬-stable' y =
  αf y (λ (x , p) → ¬ is-perfect-image f g x) (λ _ → three-negations-imply-one)

 module _ (¬¬elim-g : is-¬¬-stable-map g)
          (lc-g     : left-cancellable g)
          (y        : Y)
          (nρ       : ¬ is-perfect-image f g (g y))
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

Complementedness of the perfect image.

Finally, we need conditions under which the perfect image is complemented. For
this purpose we consider maps with Π-compact fibers. This class includes
complemented embeddings, but is much larger. For instance, the fibers are only
weakly complemented in general, and can have multiple distinct elements. For
example, the (infinite) type of conatural numbers ℕ∞ is Π-compact.

\begin{code}

is-Π-Compact-map : {X : 𝓤 ̇ }
                 → {Y : 𝓥 ̇ }
                 → (X → Y)
                 → {𝓦 : Universe}
                 → 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
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
iterate-is-Π-Compact-map αf zero =
 id-is-Π-Compact-map
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
    ¬¬-stable-weakly-decidable-types-are-decidable
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

References
──────────
 - König, 1906. Sur la théorie des ensembles.
   https://gallica.bnf.fr/ark:/12148/bpt6k30977.image.f110.langEN

 - Fredrik Bakke, 2025. The Cantor–Schröder–Bernstein theorem in ∞-Topoi.
   https://hott-uf.github.io/2025/slides/Bakke.pdf (slides)

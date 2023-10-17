Lane Biocini, 21 January 2026

The equational theory of PSL2Z. Although s² = 1 and r³ = 1 hold
definitionally (by computation), we provide propositional witnesses
for use in equational reasoning chains. The main result is that
PSL2Z has decidable equality, making it a set (h-level 2).

The decidability proof exploits the mutual inductive structure:
S-edge and R-edge each have decidable equality by structural
recursion, and the disjoint sum PSL2Z = S-edge + R-edge inherits
decidability.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

module Groups.ModularGroup.Properties where

open import MLTT.Spartan
open import MLTT.Two-Properties
open import MLTT.Plus-Properties using (+disjoint; +functor; inl-lc; inr-lc)
open import MLTT.Unit-Properties using (𝟙-is-not-𝟘)
open import UF.Base
open import UF.DiscreteAndSeparated using (is-discrete; discrete-types-are-sets)
open import UF.Sets using (is-set)
open import Groups.ModularGroup.Type
open import Groups.ModularGroup.Base

s² : (x : PSL2Z) → s (s x) ＝ x
s² (η e₀)  = refl
s² (η e₁)  = refl
s² (s∙ re) = refl
s² (θ re)  = refl

r³ : (x : PSL2Z) → r (r (r x)) ＝ x
r³ (η e₀)            = refl
r³ (η e₁)            = refl
r³ (s∙ re)           = refl
r³ (r∙ e₀)           = refl
r³ (r∙ e₁)           = refl
r³ (r∙ cross re)     = refl
r³ (r²∙ e₀)          = refl
r³ (r²∙ e₁)          = refl
r³ (r²∙ cross re)    = refl

r²-r : (x : PSL2Z) → r² (r x) ＝ x
r²-r = r³

r-r² : (x : PSL2Z) → r (r² x) ＝ x
r-r² = r³

s-E : s E ＝ S
s-E = refl

s-S : s S ＝ E
s-S = refl

r-E : r E ＝ R
r-E = refl

r-R : r R ＝ R²
r-R = refl

r-R² : r R² ＝ E
r-R² = refl

r²-E : r² E ＝ R²
r²-E = refl

r²-R : r² R ＝ E
r²-R = refl

r²-R² : r² R² ＝ R
r²-R² = refl

r-η : (se : S-edge) → r (η se) ＝ r∙ se
r-η e₀         = refl
r-η e₁         = refl
r-η (cross re) = refl

r²-η : (se : S-edge) → r² (η se) ＝ r²∙ se
r²-η e₀         = refl
r²-η e₁         = refl
r²-η (cross re) = refl

r-θ-r+ : (se : S-edge) → r (θ (r+ se)) ＝ θ (r- se)
r-θ-r+ e₀         = refl
r-θ-r+ e₁         = refl
r-θ-r+ (cross re) = refl

r-θ-r- : (se : S-edge) → r (θ (r- se)) ＝ η se
r-θ-r- e₀         = refl
r-θ-r- e₁         = refl
r-θ-r- (cross re) = refl

r²-θ-r+ : (se : S-edge) → r² (θ (r+ se)) ＝ η se
r²-θ-r+ se = ap r (r-θ-r+ se) ∙ r-θ-r- se

r²-θ-r- : (se : S-edge) → r² (θ (r- se)) ＝ θ (r+ se)
r²-θ-r- se = ap r (r-θ-r- se) ∙ r-η se

sr-η : (se : S-edge) → s (r (η se)) ＝ sr∙ se
sr-η e₀         = refl
sr-η e₁         = refl
sr-η (cross re) = refl

sr²-η : (se : S-edge) → s (r² (η se)) ＝ sr²∙ se
sr²-η e₀         = refl
sr²-η e₁         = refl
sr²-η (cross re) = refl

rs-θ : (re : R-edge) → r (s (θ re)) ＝ rs∙ re
rs-θ (r+ se) = refl
rs-θ (r- se) = refl

r²s-θ : (re : R-edge) → r² (s (θ re)) ＝ r²s∙ re
r²s-θ (r+ se) = refl
r²s-θ (r- se) = refl

srs-θ : (re : R-edge) → s (r (s (θ re))) ＝ s∙ r+ cross re
srs-θ (r+ se) = refl
srs-θ (r- se) = refl

sr²s-θ : (re : R-edge) → s (r² (s (θ re))) ＝ s∙ r- cross re
sr²s-θ (r+ se) = refl
sr²s-θ (r- se) = refl

\end{code}

Cancellation lemmas follow from the order relations. Since s² = 1 and
r³ = 1, the generators are self-inverse (s⁻¹ = s, r⁻¹ = r²) and thus
left-cancellable.

\begin{code}

s-lc : left-cancellable s
s-lc {x} {y} p = s² x ⁻¹ ∙ ap s p ∙ s² y

r-lc : left-cancellable r
r-lc {x} {y} p = r³ x ⁻¹ ∙ ap r² p ∙ r³ y

r²-lc : left-cancellable r²
r²-lc = r-lc ∘ r-lc

private
 η-helper : PSL2Z → S-edge
 η-helper (η se) = se
 η-helper (θ _) = e₀  -- dummy, but won't be used in valid cases

 θ-helper : PSL2Z → R-edge
 θ-helper (η _) = r+ e₀  -- dummy
 θ-helper (θ re) = re

 cross-helper : S-edge → R-edge
 cross-helper (cross re) = re
 cross-helper e₀ = step ₀ e₀
 cross-helper e₁ = step ₀ e₁

 r-helper : R-edge → S-edge
 r-helper (r+ se) = se
 r-helper (r- se) = se

 r-sgn : R-edge → R-sgn
 r-sgn (step d _) = d

\end{code}

The injections η and θ are left-cancellable, enabling us to reduce
equality in PSL2Z to equality in the component types.

\begin{code}

η-lc : {x y : S-edge} → Id {𝓤₀} {PSL2Z} (η x) (η y) → x ＝ y
η-lc refl = refl

θ-lc : {x y : R-edge} → Id {𝓤₀} {PSL2Z} (θ x) (θ y) → x ＝ y
θ-lc refl = refl

S-is-not-E : S ≠ E
S-is-not-E p = 𝟙-is-not-𝟘 (g (η-lc {e₁} {e₀} p))
 where
  f : S-edge → 𝓤₀ ̇
  f e₀ = 𝟘
  f e₁ = 𝟙
  f (cross _) = 𝟘

  g : e₁ ＝ e₀ → 𝟙 ＝ 𝟘
  g = ap f

η-is-not-θ : (x : S-edge) (y : R-edge) → η x ≠ θ y
η-is-not-θ x y p = +disjoint p

θ-is-not-η : (x : R-edge) (y : S-edge) → θ x ≠ η y
θ-is-not-η x y p = +disjoint (p ⁻¹)

fibers-of-η-over-E : (x : S-edge) → is-decidable (η x ＝ E)
fibers-of-η-over-E e₀ = inl refl
fibers-of-η-over-E e₁ = inr S-is-not-E
fibers-of-η-over-E (cross x) = inr (λ p → θ-is-not-η x e₁ (ap s p))

fibers-of-η-over-S : (x : S-edge) → is-decidable (η x ＝ S)
fibers-of-η-over-S e₀ = inr (λ p → S-is-not-E (p ⁻¹))
fibers-of-η-over-S e₁ = inl refl
fibers-of-η-over-S (cross x) = inr (λ p → θ-is-not-η x e₀ (ap s p))

\end{code}

Decidability of equality is established by mutual recursion on the
graph structure. We decide equality fiber-by-fiber over each
constructor, using the order relations to distinguish r+ from r-.

\begin{code}

fibers-of-η-over-cross : (x : S-edge) (y : R-edge)
                       → is-decidable ((inl x) ＝ inl (cross y))
fibers-of-θ-over-r+ : (x : R-edge) (y : S-edge)
                    → is-decidable ((inr x) ＝ inr (r+ y))
fibers-of-θ-over-r- : (x : R-edge) (y : S-edge)
                    → is-decidable ((inr x) ＝ inr (r- y))

S-edge-is-discrete : is-discrete S-edge
R-edge-is-discrete : is-discrete R-edge

η-is-decidable : (x y : S-edge)
               → is-decidable ((inl {𝓤₀} {𝓤₀} {S-edge} {R-edge} x) ＝ inl y)
θ-is-decidable : (x y : R-edge)
               → is-decidable ((inr {𝓤₀} {𝓤₀} {S-edge} {R-edge} x) ＝ inr y)

fibers-of-η-over-cross e₀ y = inr (η-is-not-θ e₁ y ∘ ap s)
fibers-of-η-over-cross e₁ y = inr (η-is-not-θ e₀ y ∘ ap s)
fibers-of-η-over-cross (cross x) y =
 +functor (ap (λ re → η (cross re)))
          (contrapositive cross-inj)
          (R-edge-is-discrete x y)
 where
  cross-inj : {a b : R-edge} → η (cross a) ＝ η (cross b) → a ＝ b
  cross-inj p = ap (θ-helper ∘ s) p

fibers-of-θ-over-r+ (r+ x) y =
 +functor (ap (λ se → θ (r+ se)))
          (contrapositive r+inj)
          (S-edge-is-discrete x y)
 where
  r+inj : {a b : S-edge} → θ (r+ a) ＝ θ (r+ b) → a ＝ b
  r+inj {a} {b} p = η-lc (r²-θ-r+ a ⁻¹ ∙ ap r² p ∙ r²-θ-r+ b)
fibers-of-θ-over-r+ (r- x) y = inr lemma
 where
  lemma : θ (r- x) ＝ θ (r+ y) → 𝟘
  lemma p = η-is-not-θ x (r- y) (r-θ-r- x ⁻¹ ∙ ap r p ∙ r-θ-r+ y)
fibers-of-θ-over-r- (r+ x) y = inr lemma
 where
  lemma : θ (r+ x) ＝ θ (r- y) → 𝟘
  lemma p = η-is-not-θ x (r+ y) (r²-θ-r+ x ⁻¹ ∙ ap r² p ∙ r²-θ-r- y)
fibers-of-θ-over-r- (r- x) y =
  +functor (ap (λ se → θ (r- se)))
           (contrapositive r-inj)
           (S-edge-is-discrete x y)
  where
    r-inj : {a b : S-edge} → θ (r- a) ＝ θ (r- b) → a ＝ b
    r-inj {a} {b} p = η-lc (r-θ-r- a ⁻¹ ∙ ap r p ∙ r-θ-r- b)

S-edge-is-discrete e₀ e₀ = inl refl
S-edge-is-discrete e₀ e₁ = inr (λ p → S-is-not-E (ap inl (p ⁻¹)))
S-edge-is-discrete e₀ (cross y) = inr (λ p → η-is-not-θ e₁ y (ap s (ap inl p)))
S-edge-is-discrete e₁ e₀ = inr (λ p → S-is-not-E (ap inl p))
S-edge-is-discrete e₁ e₁ = inl refl
S-edge-is-discrete e₁ (cross y) = inr (λ p → η-is-not-θ e₀ y (ap s (ap inl p)))
S-edge-is-discrete (cross x) e₀ =
  inr (λ p → η-is-not-θ e₁ x (ap s (ap inl (p ⁻¹))))
S-edge-is-discrete (cross x) e₁ =
  inr (λ p → η-is-not-θ e₀ x (ap s (ap inl (p ⁻¹))))
S-edge-is-discrete (cross x) (cross y) =
  +functor (ap cross) (contrapositive cross-inj) (R-edge-is-discrete x y)
  where
    cross-inj : {a b : R-edge} → cross a ＝ cross b → a ＝ b
    cross-inj {a} {b} p = ap cross-helper p

R-edge-is-discrete (r+ x) (r+ y) =
 +functor (ap (λ se → r+ se)) (contrapositive r+inj) (S-edge-is-discrete x y)
 where
   r+inj : {a b : S-edge} → r+ a ＝ r+ b → a ＝ b
   r+inj {a} {b} p = ap r-helper p
R-edge-is-discrete (r+ x) (r- y) = inr (λ p → zero-is-not-one (ap r-sgn p))
R-edge-is-discrete (r- x) (r+ y) = inr (λ p → one-is-not-zero (ap r-sgn p))
R-edge-is-discrete (r- x) (r- y) =
 +functor (ap (λ se → r- se)) (contrapositive r-inj) (S-edge-is-discrete x y)
 where
   r-inj : {a b : S-edge} → r- a ＝ r- b → a ＝ b
   r-inj {a} {b} p = ap r-helper p

η-is-decidable x e₀ = fibers-of-η-over-E x
η-is-decidable x e₁ = fibers-of-η-over-S x
η-is-decidable x (cross y) = fibers-of-η-over-cross x y

θ-is-decidable x (r+ y) = fibers-of-θ-over-r+ x y
θ-is-decidable x (r- y) = fibers-of-θ-over-r- x y

PSL2Z-is-discrete : is-discrete PSL2Z
PSL2Z-is-discrete (η x) (η y) = η-is-decidable x y
PSL2Z-is-discrete (η x) (θ y) = inr (η-is-not-θ x y)
PSL2Z-is-discrete (θ x) (η y) = inr (≠-sym (η-is-not-θ y x))
PSL2Z-is-discrete (θ x) (θ y) = θ-is-decidable x y

PSL2Z-is-set : is-set PSL2Z
PSL2Z-is-set = discrete-types-are-sets PSL2Z-is-discrete

\end{code}

Although we have our main result, why not these as well.

\begin{code}

S-edge-is-set : is-set S-edge
S-edge-is-set = discrete-types-are-sets S-edge-is-discrete

R-edge-is-set : is-set R-edge
R-edge-is-set = discrete-types-are-sets R-edge-is-discrete

\end{code}

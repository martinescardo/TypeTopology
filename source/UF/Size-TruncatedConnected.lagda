Ian Ray, 4th Febuary 2024.

Modifications made by Ian Ray on 14 October 2024.

Modifications made by Ian Ray on 7 January 2025.

Modification made by Ian Ray on 17 August 2025.

We develop some results that relate size, truncation and connectedness from
the following paper:
[1] Christensen, J.D. (2024), Non-accessible localizations.
    Journal of Topology, 17: e12336.
    https://doi.org/10.1112/topo.12336

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt
open import UF.Truncations
open import MLTT.Spartan hiding (_+_)

module UF.Size-TruncatedConnected
        (fe : Fun-Ext)
        (te : general-truncations-exist fe)
        (𝓥 : Universe)
       where

open import Notation.CanonicalMap
open import Notation.Decimal
open import UF.ConnectedTypes fe
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PropTrunc
open import UF.SmallnessProperties
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.TruncatedTypes fe
open import UF.TruncationLevels
open import UF.Univalence

private
 pt : propositional-truncations-exist
 pt = general-truncations-give-propositional-truncations fe te

open import UF.ImageAndSurjection pt
open import UF.Replacement pt

\end{code}

We begin by giving some definitions from [1] and proving important properties
about them. We have fixed the universe parameter 𝓥 and use it as our point of
reference for 'smallness'. Univalence is not required for every result, so we
will explicitly assume it only when it is used.

\begin{code}

_is_locally-small : (X : 𝓤 ̇ ) → (n : ℕ) → 𝓤 ⊔ (𝓥 ⁺) ̇
X is zero locally-small = X is 𝓥 small
X is (succ n) locally-small = (x x' : X) → (x ＝ x') is n locally-small

being-locally-small-is-prop : {X : 𝓤 ̇ } {n : ℕ}
                            → Univalence
                            → is-prop (X is n locally-small)
being-locally-small-is-prop {_} {X} {zero} ua = being-small-is-prop ua X 𝓥
being-locally-small-is-prop {_} {X} {succ n} ua
 = Π₂-is-prop fe (λ x y → being-locally-small-is-prop ua)

being-locally-small-is-upper-closed : {X : 𝓤 ̇ } {n : ℕ}
                                    → X is n locally-small
                                    → X is (succ n) locally-small
being-locally-small-is-upper-closed {_} {X} {zero}
 = small-implies-locally-small X 𝓥
being-locally-small-is-upper-closed {_} {X} {succ n} X-loc-small x x'
 = being-locally-small-is-upper-closed (X-loc-small x x')

locally-small-types-are-small : {X : 𝓤 ̇ } {n : ℕ}
                              → X is 𝓥 small
                              → X is n locally-small
locally-small-types-are-small {_} {_} {zero} X-small = X-small
locally-small-types-are-small {_} {X} {succ n} X-small x x'
 = locally-small-types-are-small (small-implies-locally-small X 𝓥 X-small x x')

\end{code}

Local smallness is closed under equivalence, sigma types and truncation for
each n : ℕ.

\begin{code}

local-smallness-is-closed-under-≃ : {X : 𝓤 ̇ } {Y : 𝓦 ̇ } {n : ℕ}
                                  → X ≃ Y
                                  → X is n locally-small
                                  → Y is n locally-small
local-smallness-is-closed-under-≃ {_} {_} {_} {_} {zero} e X-small
 = smallness-closed-under-≃ X-small e
local-smallness-is-closed-under-≃ {_} {_} {_} {_} {succ n} e X-loc-small y y' =
 local-smallness-is-closed-under-≃ path-equiv
  (X-loc-small (⌜ e ⌝⁻¹ y) (⌜ e ⌝⁻¹ y'))
 where
  path-equiv : (⌜ e ⌝⁻¹ y ＝ ⌜ e ⌝⁻¹ y') ≃ (y ＝ y')
  path-equiv = ≃-sym (ap ⌜ e ⌝⁻¹ , ap-is-equiv ⌜ e ⌝⁻¹ (⌜⌝⁻¹-is-equiv e))

local-smallness-is-closed-under-Σ : {X : 𝓤 ̇ } {Y : X → 𝓦 ̇ } {n : ℕ}
                                  → X is n locally-small
                                  → ((x : X) → (Y x) is n locally-small)
                                  → (Σ x ꞉ X , Y x) is n locally-small
local-smallness-is-closed-under-Σ {_} {_} {_} {_} {zero} X-small Y-small
 = Σ-is-small X-small Y-small
local-smallness-is-closed-under-Σ {_} {_} {_} {Y} {succ n}
 X-loc-small Y-loc-small (x , y) (x' , y')
 = local-smallness-is-closed-under-≃ (≃-sym Σ-＝-≃)
    (local-smallness-is-closed-under-Σ (X-loc-small x x')
     (λ - → Y-loc-small x' (transport Y - y) y'))

open general-truncations-exist te

local-smallness-is-closed-under-truncation
 : {X : 𝓤 ̇ } {n : ℕ₋₂}
 → Univalence
 → X is ι (n + 2) locally-small
 → ∥ X ∥[ n ] is ι (n + 2) locally-small
local-smallness-is-closed-under-truncation {_} {X} {−2} ua
 = truncations-of-small-types-are-small
local-smallness-is-closed-under-truncation {_} {X} {succ n} ua X-loc-small
 = ∥∥ₙ-ind₂ (λ u v → (u ＝ v) is ι (n + 2) locally-small)
            (λ u v → truncation-levels-are-upper-closed' ⋆
             (is-prop-implies-is-prop' (being-locally-small-is-prop ua)))
            (λ x y → local-smallness-is-closed-under-≃
             (eliminated-trunc-identity-char (ua _))
             (local-smallness-is-closed-under-truncation ua (X-loc-small x y)))

\end{code}

Many of the results in [1] follow from a fact that some call the type theoretic
axiom of replacement. It states that given a small type A, a locally small type
X and a function f : A → X the image of f is small.

We note that while the name for this result is due to its 'apparent' similarity
to the axiom of replacement from set theory, but replacement in type theory is
quite a modest assumption in comparison. Indeed, type replacement follows from
the existence of pushouts (see UF/Replacement for further discussion on the
modest strength of replacement) as demonstrated by "The Join Construction" by
Egbert Rijke (https://arxiv.org/abs/1701.07538).

In the interest of keeping the present work self-contained and requiring only
the weakest assumptions possible, we simply assume the relevant form of
replacement as it is needed.

\begin{code}

open connectedness-results te

Replacement'' : {𝓤 𝓦 : Universe} → (𝓥 ⁺) ⊔ (𝓤 ⁺) ⊔ (𝓦 ⁺) ̇
Replacement'' {𝓤} {𝓦} = {A : 𝓤 ̇ } {X : 𝓦 ̇ } {f : A → X}
                      → A is 𝓥 small
                      → X is 1 locally-small
                      → f is −1 connected-map
                      → X is 𝓥 small

Replacement'-to-Replacement'' : {𝓤 𝓦 : Universe}
                              → Replacement' {𝓥} {𝓤} {𝓦} → Replacement'' {𝓤} {𝓦}
Replacement'-to-Replacement'' rep' {_} {_} {f} A-sm X-ls f-con
 = rep' f A-sm X-ls (−1-connected-maps-are-surjections f-con)

Replacement''-to-Replacement' : {𝓤 𝓦 : Universe}
                              → Replacement'' {𝓤} {𝓦} → Replacement' {𝓥} {𝓤} {𝓦}
Replacement''-to-Replacement' rep'' {_} {_} f A-sm X-ls f-surj
 = rep'' A-sm X-ls (surjections-are-−1-connected f-surj)

\end{code}

We will now begin proving some of the results from [1]. We avoid any unnecessary
use of propositional resizing. Theorem numbers will be provided for easy
reference.

Prop 2.2 of [1]

\begin{code}

open PropositionalTruncation pt

module _ (ua : Univalence)
         (rep : {𝓤 𝓦 : Universe} → Replacement'' {𝓤} {𝓦})
       where

 Prop-2-2[locally-small-type-with-connected-map-from-small-type-is-small]
  : {𝓤 𝓦 : Universe} {A : 𝓤 ̇ } {X : 𝓦 ̇ } {f : A → X} {n : ℕ₋₂}
  → f is n connected-map
  → A is 𝓥 small
  → X is ι (n + 2) locally-small
  → X is 𝓥 small
 Prop-2-2[locally-small-type-with-connected-map-from-small-type-is-small]
  {_} {_} {_} {_} {_} {−2} f-con A-small X-small = X-small
 Prop-2-2[locally-small-type-with-connected-map-from-small-type-is-small]
  {𝓤} {𝓦} {A} {X} {f} {succ n} f-con A-small X-is-loc-small
  = rep A-small (III (−1-connected-maps-are-surjections I)) I
  where
   I : f is −1 connected-map
   I = map-connectedness-is-lower-closed ⋆ f-con
   II : (x x' : X)
      → Σ a ꞉ A , f a ＝ x
      → Σ a ꞉ A , f a ＝ x'
      → (x ＝ x') is 𝓥 small
   II .(f a) .(f a') (a , refl) (a' , refl)
    = Prop-2-2[locally-small-type-with-connected-map-from-small-type-is-small]
       (ap-is-less-connected (ua (𝓤 ⊔ 𝓦)) f f-con)
        (small-implies-locally-small A 𝓥 A-small a a')
         (X-is-loc-small (f a) (f a'))
   III : is-surjection f
       → (x x' : X)
       → (x ＝ x') is 𝓥 small
   III f-is-surj x x' = ∥∥-rec₂ (being-small-is-prop ua (x ＝ x') 𝓥)
                         (II x x') (f-is-surj x) (f-is-surj x')

 locally-small-type-with-connected-map-from-small-type-is-small =
  Prop-2-2[locally-small-type-with-connected-map-from-small-type-is-small]

\end{code}

Lemma 2.3 of [1]

\begin{code}

Lemma-2-3[truncated-types-are-locally-small] : {X : 𝓤 ̇ } {n : ℕ₋₂}
                                             → Propositional-Resizing
                                             → X is (n + 1) truncated
                                             → X is ι (n + 2) locally-small
Lemma-2-3[truncated-types-are-locally-small] {_} {X} {−2} pr X-prop
 = pr X (is-prop'-implies-is-prop X-prop)
Lemma-2-3[truncated-types-are-locally-small] {_} {_} {succ n} pr X-trunc x x'
 = Lemma-2-3[truncated-types-are-locally-small] pr (X-trunc x x')

truncated-types-are-locally-small = Lemma-2-3[truncated-types-are-locally-small]

\end{code}

We note that Lemma 2.3 provides one side of a bimplication involving
propositional resizing. We will now record the other direction.

\begin{code}

truncated-types-are-locally-small-gives-propositional-resizing
 : ({X : 𝓤 ̇ } {n : ℕ₋₂} → X is (n + 1) truncated → X is ι (n + 2) locally-small)
 → propositional-resizing 𝓤 𝓥
truncated-types-are-locally-small-gives-propositional-resizing
 trunc-gives-loc-small P P-prop
 = trunc-gives-loc-small {P} {−2} (is-prop-implies-is-prop' P-prop)

\end{code}

Lemma 2.4 of [1]

\begin{code}

Lemma-2-4[type-with-truncated-map-to-locally-small-type-is-locally-small]
 : {X : 𝓤 ̇ } {Y : 𝓦 ̇ } {f : X → Y} {n : ℕ₋₂}
 → Propositional-Resizing
 → f is (n + 1) truncated-map
 → Y is ι (n + 2) locally-small
 → X is ι (n + 2) locally-small
Lemma-2-4[type-with-truncated-map-to-locally-small-type-is-locally-small]
 {_} {_} {_} {_} {f} {_} pr f-trunc Y-loc-small
 = local-smallness-is-closed-under-≃ (total-fiber-is-domain f)
    (local-smallness-is-closed-under-Σ Y-loc-small
     (λ y → Lemma-2-3[truncated-types-are-locally-small] pr (f-trunc y)))

type-with-truncated-map-to-locally-small-type-is-locally-small
 = Lemma-2-4[type-with-truncated-map-to-locally-small-type-is-locally-small]

\end{code}

Lemma 2.5 of [1]

\begin{code}

module _ (ua : Univalence)
         (rep : {𝓤 𝓦 : Universe} → Replacement'' {𝓤} {𝓦})
       where

 Lemma-2-5[connected-type-with-truncated-map-to-locally-small-type-is-small]
  : {X : 𝓤 ̇ } {Y : 𝓦 ̇ } {f : X → Y} {n : ℕ₋₂}
  → Propositional-Resizing
  → f is (n + 1) truncated-map
  → Y is ι (n + 2) locally-small
  → X is (n + 1) connected
  → X is 𝓥 small
 Lemma-2-5[connected-type-with-truncated-map-to-locally-small-type-is-small]
  {𝓤} {_} {X} {_} {_} {n} pr f-trunc Y-loc-small X-conn
  = ∥∥-rec (being-small-is-prop ua X 𝓥) VI (center II)
  where
   I : X is ι (n + 2) locally-small
   I = Lemma-2-4[type-with-truncated-map-to-locally-small-type-is-locally-small]
        pr f-trunc Y-loc-small
   II : X is −1 connected
   II = connectedness-is-lower-closed' ⋆ X-conn
   III : X → 𝟙 {𝓤} → X
   III x ⋆ = x
   IV : (x : X) → (III x) is n connected-map
   IV x = basepoint-map-is-less-connected (ua _) (III x) X-conn
   V : 𝟙 {𝓤} is 𝓥 small
   V = pr 𝟙 𝟙-is-prop
   VI : X → X is 𝓥 small
   VI x
    = Prop-2-2[locally-small-type-with-connected-map-from-small-type-is-small]
       ua rep (IV x) V I

 connected-type-with-truncated-map-to-locally-small-type-is-small
  = Lemma-2-5[connected-type-with-truncated-map-to-locally-small-type-is-small]

\end{code}

In [1] Christensen proves Theorem 2.6 with propositional resizing and without.
In the presence of resizing Theorem 2.6 follows from previous results, but as
we are interested in avoiding unnecessary use of propositional resizing, we
choose to record the latter proof. It is a bit more involved, so we will first
need to prove a few lemmas.

\begin{code}

 small-path-space-from-locally-small-type-and-small-truncation
  : {X : 𝓤 ̇ } {n : ℕ₋₂}
  → X is ι (n + 2) locally-small
   × ∥ X ∥[ n + 1 ] is 𝓥 small
  → (Σ y ꞉ ∥ X ∥[ n + 1 ] , Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ y) is 𝓥 small
 small-path-space-from-locally-small-type-and-small-truncation
  {𝓤} {X} {n} (X-loc-small , trunc-X-small) = Σ-is-small trunc-X-small IX
  where
   I : (x' : X) → (Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ ∣ x' ∣[ n + 1 ]) is 𝓥 small
   I x'
    = Prop-2-2[locally-small-type-with-connected-map-from-small-type-is-small]
       ua rep IV V VI
    where
     II : 𝟙 {𝓤} → Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ ∣ x' ∣[ n + 1 ]
     II ⋆ = (x' , refl)
     III : (Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ ∣ x' ∣[ n + 1 ]) is (n + 1) connected
     III = trunc-map-is-connected ∣ x' ∣[ n + 1 ]
     IV : II is n connected-map
     IV = basepoint-map-is-less-connected (ua _) II III
     V : 𝟙 {𝓤} is 𝓥 small
     V = (𝟙 {𝓥} , one-𝟙-only)
     VI : (Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ ∣ x' ∣[ n + 1 ])
           is ι (n + 2) locally-small
     VI = local-smallness-is-closed-under-Σ X-loc-small VII
      where
       VII : (x : X)
           → (∣ x ∣[ succ n ] ＝ ∣ x' ∣[ succ n ]) is ι (n + 2) locally-small
       VII x = local-smallness-is-closed-under-≃
                (eliminated-trunc-identity-char (ua _)) VIII
        where
         VIII : ∥ x ＝ x' ∥[ n ] is ι (n + 2) locally-small
         VIII = local-smallness-is-closed-under-truncation
                 ua (being-locally-small-is-upper-closed X-loc-small x x')
   IX : (y : ∥ X ∥[ n + 1 ]) → (Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ y) is 𝓥 small
   IX = ∥∥ₙ-ind (λ - → props-are-truncated pt
         (being-small-is-prop ua (Σ x ꞉ X , ∣ x ∣[ n + 1 ] ＝ -) 𝓥)) I

 locally-small-type-with-small-truncation-is-small
  : {X : 𝓤 ̇ } {n : ℕ₋₂}
  → X is ι (n + 2) locally-small
    × ∥ X ∥[ n + 1 ] is 𝓥 small
  → X is 𝓥 small
 locally-small-type-with-small-truncation-is-small {_} {X} {n} small-hyp
  = smallness-closed-under-≃'
     (small-path-space-from-locally-small-type-and-small-truncation small-hyp)
      (domain-is-total-fiber ∣_∣[ succ n ])

\end{code}

Theorem 2.6 of [1]

\begin{code}

 Theorem-2-6[type-is-small-iff-type-is-locally-small-and-has-small-truncation]
  : {X : 𝓤 ̇ } {n : ℕ₋₂}
  → X is 𝓥 small
  ↔ X is ι (n + 2) locally-small × ∥ X ∥[ n + 1 ] is 𝓥 small
 Theorem-2-6[type-is-small-iff-type-is-locally-small-and-has-small-truncation]
  {_} {X} {n}
  = (I , locally-small-type-with-small-truncation-is-small)
  where
   I : X is 𝓥 small
     → X is ι (n + 2) locally-small × ∥ X ∥[ n + 1 ] is 𝓥 small
   I X-small = (locally-small-types-are-small X-small ,
                truncations-of-small-types-are-small X-small)

 type-is-small-iff-type-is-locally-small-and-has-small-truncation =
  Theorem-2-6[type-is-small-iff-type-is-locally-small-and-has-small-truncation]

\end{code}

We will record the following corollary of Theorem 2.6 from [1]:
 The set truncation of a universe is large (i.e. not small).

\begin{code}

 set-truncation-of-universe-is-large : is-large ∥ 𝓥 ̇ ∥[ 0 ]
 set-truncation-of-universe-is-large = contrapositive I universes-are-large
  where
   I : is-small ∥ 𝓥 ̇ ∥[ 0 ] → is-small (𝓥 ̇ )
   I small-trunc = locally-small-type-with-small-truncation-is-small
                    (universes-are-locally-small (ua 𝓥) , small-trunc)

\end{code}

Corollary 2.7 of [1]

\begin{code}

 Corollary-2-7[type-with-small-truncation-truncated-map-to-locally-small-is-small]
  : {X : 𝓤 ̇ } {Y : 𝓦 ̇ } {f : X → Y} {n : ℕ₋₂}
  → Propositional-Resizing
  → f is (n + 1) truncated-map
  → Y is ι (n + 2) locally-small
  → ∥ X ∥[ n + 1 ] is 𝓥 small
  → X is 𝓥 small
 Corollary-2-7[type-with-small-truncation-truncated-map-to-locally-small-is-small]
  pr f-trunc Y-loc-small trunc-X-small
  = locally-small-type-with-small-truncation-is-small
     (Lemma-2-4[type-with-truncated-map-to-locally-small-type-is-locally-small]
      pr f-trunc Y-loc-small , trunc-X-small)

 type-with-small-truncation-and-truncated-map-to-locally-small-type-is-small
  = Corollary-2-7[type-with-small-truncation-truncated-map-to-locally-small-is-small]

\end{code}

TODO. Proposition 2.8 requires the concept of Homotopy Groups.

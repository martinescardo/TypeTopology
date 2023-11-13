Tom de Jong and Ayberk Tosun, 4 & 5 October 2023


Given an algebraic dcpo 𝓓, the subset K of compact elements forms a basis for 𝓓.
In our predicative context, we consider *small* bases, however, and a priori
there is no reason for K to be a small type.

However, if 𝓓 comes equipped with what we call a small compact basis, then set
replacement¹ implies that K is small.

If we moreover assume univalence, then the relevant small condition is a
property, which means that having an unspecified small compact basis is
sufficient.

In particular, with set replacement and univalence, we can show:
  ∥ has-specified-small-compact-basis 𝓓 ∥ → has-specified-small-compact-basis 𝓓.
In other words, the type (has-specified-small-compact-basis 𝓓) has split support.

Having a specified small compact basis is useful as we can use the small basis
to replace large quantifications by small ones for example, for example to show
that exponentials are locally small.

The split support observation is due to Ayberk Tosun (23 September 2023) and was
formalised, with the addition of many explanatory comments, by Tom de Jong.
Ayberk previously formalised the result for spectrality in the context of locale
theory in Locales.SmallBasis (truncated-spectralᴰ-implies-spectral).

Towards the end, we also clarify how the fact that K is the unique basis (as a
subset) consisting of compact elements fits in to our framework.


¹ Set replacement says: if f : X → Y is a map from a small type to a locally
  small set, then the image of f is small.
  It is equivalent to having small set quotients, see Quotient.index.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.BasesAndContinuity.CompactBasis
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Sets-Properties
open import UF.Size hiding (is-small ; is-locally-small)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥

\end{code}

As announced above, we start by establishing as many as properties of K as
possible without considering that K needs to be small.

For this, we only assume that our dcpo is algebraic (in the truncated sense).

\begin{code}

module basis-of-compact-elements
        (𝓓 : DCPO {𝓤} {𝓣})
        (is-alg : is-algebraic-dcpo 𝓓)
       where

 K : 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 K = Σ x ꞉ ⟨ 𝓓 ⟩ , is-compact 𝓓 x

 ι : K → ⟨ 𝓓 ⟩
 ι = pr₁

 ι-is-compact : (c : K) → is-compact 𝓓 (ι c)
 ι-is-compact = pr₂

 ↓ᴷ : ⟨ 𝓓 ⟩ → 𝓥 ⁺ ⊔ 𝓤 ⊔ 𝓣 ̇
 ↓ᴷ x = Σ k ꞉ K , ι k ⊑⟨ 𝓓 ⟩ x

 ↓ᴷ-inclusion : (x : ⟨ 𝓓 ⟩) → ↓ᴷ x → ⟨ 𝓓 ⟩
 ↓ᴷ-inclusion x = ι ∘ pr₁

\end{code}

We show that every element x of 𝓓 is the *directed* supremum of the inclusion
  (Σ k ꞉ K , k ⊑⟨ 𝓓 ⟩ x) → ⟨ 𝓓 ⟩.

\begin{code}

 ↓ᴷ-is-inhabited : (x : ⟨ 𝓓 ⟩) → ∥ ↓ᴷ x ∥
 ↓ᴷ-is-inhabited x = ∥∥-rec ∥∥-is-prop γ is-alg
  where
   γ : structurally-algebraic 𝓓
     → ∥ ↓ᴷ x ∥
   γ str-alg = ∥∥-functor f inh
    where
     open structurally-algebraic str-alg
     inh : ∥ index-of-compact-family x ∥
     inh = inhabited-if-Directed 𝓓 (compact-family x)
                                   (compact-family-is-directed x)
     f : index-of-compact-family x → ↓ᴷ x
     f i = (compact-family x i , compact-family-is-compact x i)
           , compact-family-is-upperbound x i

 ↓ᴷ-is-semidirected : (x : ⟨ 𝓓 ⟩) → is-Semidirected 𝓓 (↓ᴷ-inclusion x)
 ↓ᴷ-is-semidirected x =
  ∥∥-rec (being-semidirected-is-prop (underlying-order 𝓓) (↓ᴷ-inclusion x))
         γ is-alg
   where
    γ : structurally-algebraic 𝓓
      → is-Semidirected 𝓓 (↓ᴷ-inclusion x)
    γ str-alg ((c₁ , c₁-compact) , c₁-below-x)
              ((c₂ , c₂-compact) , c₂-below-x) =
     ∥∥-rec₂ ∃-is-prop sd ⦅1⦆ ⦅2⦆
      where
       open structurally-algebraic str-alg
       I = index-of-compact-family x
       κ = compact-family x
       δ = compact-family-is-directed x
       ⦅1⦆ : ∃ i₁ ꞉ I , c₁ ⊑⟨ 𝓓 ⟩ compact-family x i₁
       ⦅1⦆ = c₁-compact I κ δ
                        (c₁     ⊑⟨ 𝓓 ⟩[ c₁-below-x ]
                         x      ⊑⟨ 𝓓 ⟩[ ＝-to-⊒ 𝓓 (compact-family-∐-＝ x) ]
                         ∐ 𝓓 δ ∎⟨ 𝓓 ⟩)
       ⦅2⦆ : ∃ i₂ ꞉ I , c₂ ⊑⟨ 𝓓 ⟩ compact-family x i₂
       ⦅2⦆ = c₂-compact I κ δ
                        (c₂     ⊑⟨ 𝓓 ⟩[ c₂-below-x ]
                         x      ⊑⟨ 𝓓 ⟩[ ＝-to-⊒ 𝓓 (compact-family-∐-＝ x) ]
                         ∐ 𝓓 δ ∎⟨ 𝓓 ⟩)
       sd : (Σ i₁ ꞉ I , c₁ ⊑⟨ 𝓓 ⟩ κ i₁)
          → (Σ i₂ ꞉ I , c₂ ⊑⟨ 𝓓 ⟩ κ i₂)
          → ∃ c ꞉ ↓ᴷ x , (c₁ ⊑⟨ 𝓓 ⟩ ↓ᴷ-inclusion x c)
                       × (c₂ ⊑⟨ 𝓓 ⟩ ↓ᴷ-inclusion x c)
       sd (i₁ , c₁-below-i₁) (i₂ , c₂-below-i₂) = ∥∥-functor f semidir
        where
         semidir : ∃ i ꞉ I , (κ i₁ ⊑⟨ 𝓓 ⟩ κ i) × (κ i₂ ⊑⟨ 𝓓 ⟩ κ i)
         semidir = semidirected-if-Directed 𝓓 κ δ i₁ i₂
         f : (Σ i ꞉ I , (κ i₁ ⊑⟨ 𝓓 ⟩ κ i) × (κ i₂ ⊑⟨ 𝓓 ⟩ κ i))
           → Σ c ꞉ ↓ᴷ x , (c₁ ⊑⟨ 𝓓 ⟩ ↓ᴷ-inclusion x c)
                        × (c₂ ⊑⟨ 𝓓 ⟩ ↓ᴷ-inclusion x c)
         f (i , i₁-below-i , i₂-below-i) = ((κ i , compact-family-is-compact x i)
                                           , compact-family-is-upperbound x i)
                                           , (c₁   ⊑⟨ 𝓓 ⟩[ c₁-below-i₁ ]
                                              κ i₁ ⊑⟨ 𝓓 ⟩[ i₁-below-i ]
                                              κ i  ∎⟨ 𝓓 ⟩)
                                           , (c₂   ⊑⟨ 𝓓 ⟩[ c₂-below-i₂ ]
                                              κ i₂ ⊑⟨ 𝓓 ⟩[ i₂-below-i ]
                                              κ i  ∎⟨ 𝓓 ⟩)

 ↓ᴷ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↓ᴷ-inclusion x)
 ↓ᴷ-is-directed x = ↓ᴷ-is-inhabited x , ↓ᴷ-is-semidirected x

 ↓ᴷ-is-upperbound : (x : ⟨ 𝓓 ⟩)
                  → is-upperbound (underlying-order 𝓓) x (↓ᴷ-inclusion x)
 ↓ᴷ-is-upperbound x c = pr₂ c

 ↓ᴷ-is-sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (↓ᴷ-inclusion x)
 ↓ᴷ-is-sup x =
  ∥∥-rec (is-sup-is-prop (underlying-order 𝓓) (pr₁ (axioms-of-dcpo 𝓓))
                         x (↓ᴷ-inclusion x))
         γ is-alg
   where
    γ : structurally-algebraic 𝓓
      → is-sup (underlying-order 𝓓) x (↓ᴷ-inclusion x)
    γ str-alg = ↓ᴷ-is-upperbound x , lb-of-ubs
     where
      open structurally-algebraic str-alg
      lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓓) x
                                               (↓ᴷ-inclusion x)
      lb-of-ubs y y-is-ub =
       transport (λ - → - ⊑⟨ 𝓓 ⟩ y)
                 (compact-family-∐-＝ x)
                 (∐-is-lowerbound-of-upperbounds 𝓓
                   (compact-family-is-directed x) y lb-of-ubs')
        where
         lb-of-ubs' : (i : index-of-compact-family x)
                    → compact-family x i ⊑⟨ 𝓓 ⟩ y
         lb-of-ubs' i = y-is-ub ((compact-family x i
                                , compact-family-is-compact x i)
                                , compact-family-is-upperbound x i)

\end{code}

Assuming set replacement and a *specified* small compact basis, we deduce that K
is a small type.

\begin{code}

module resize-using-specified-small-compact-basis
        (sr : Set-Replacement pt)
        (𝓓 : DCPO {𝓤} {𝓣})
        ((B , β , scb) : has-specified-small-compact-basis 𝓓)
       where

 open basis-of-compact-elements
       𝓓 (is-algebraic-dcpo-if-unspecified-small-compact-basis 𝓓 ∣ B , β , scb ∣)

 open is-small-compact-basis scb
 open is-locally-small (locally-small-if-small-compact-basis 𝓓 β scb)

 K-is-small' : is-small K
 K-is-small' = ≃-size-contravariance K-is-image image-is-small
  where
   β' : B → K
   β' b = β b , basis-is-compact b
   β'-is-surjection : is-surjection β'
   β'-is-surjection (x , x-compact) =
    ∥∥-functor
     (λ {(b , refl) → b , to-subtype-＝ (being-compact-is-prop 𝓓) refl})
     (small-compact-basis-contains-all-compact-elements
      𝓓 β scb x x-compact)
   K-is-image : K ≃ image β'
   K-is-image = ≃-sym (surjection-≃-image β' β'-is-surjection)
   K-is-set : is-set K
   K-is-set = subtypes-of-sets-are-sets' ι
               (pr₁-lc (λ {x} → being-compact-is-prop 𝓓 x)) (sethood 𝓓)
   K-is-locally-small : K is-locally 𝓥 small
   K-is-locally-small (x , x-compact) (y , y-compact) =
      ((x ⊑ₛ y) × (y ⊑ₛ x))
    , logically-equivalent-props-are-equivalent
       (×-is-prop (⊑ₛ-is-prop-valued x y) (⊑ₛ-is-prop-valued y x))
       K-is-set
       (λ (l , k) → to-subtype-＝ (being-compact-is-prop 𝓓)
                                  (antisymmetry 𝓓 x y (⊑ₛ-to-⊑ l)
                                                      (⊑ₛ-to-⊑ k)))
       λ {refl → reflexivityₛ x , reflexivityₛ x}
   image-is-small : is-small (image β')
   image-is-small = sr β' (B , ≃-refl B) K-is-locally-small K-is-set

 ι-⊑-is-small' : (x : ⟨ 𝓓 ⟩) (c : K) → is-small (ι c ⊑⟨ 𝓓 ⟩ x)
 ι-⊑-is-small' x c =
  ⌜ local-smallness-equivalent-definitions 𝓓 ⌝ loc-small (ι c) x
   where
    loc-small : is-locally-small 𝓓
    loc-small = locally-small-if-small-compact-basis 𝓓 β scb

\end{code}

If we additionally assume univalence, then we can prove that K is small from
assuming an *unspecified* small compact basis.

The need for univalence lies in the fact that it implies that smallness is a
property (being-small-is-prop).
(In fact, univalence is equivalent to this, in some precise sense, see UF.Size.)

\begin{code}

open import UF.Univalence

module resize-using-unspecified-small-compact-basis
        (ua : Univalence)
        (sr : Set-Replacement pt)
        (𝓓 : DCPO {𝓤} {𝓣})
        (uscb : has-unspecified-small-compact-basis 𝓓)
       where

 open basis-of-compact-elements
       𝓓 (is-algebraic-dcpo-if-unspecified-small-compact-basis 𝓓 uscb)

 K-is-small : is-small K
 K-is-small = ∥∥-rec (being-small-is-prop ua K 𝓥) γ uscb
  where
   γ : has-specified-small-compact-basis 𝓓
     → is-small K
   γ scb = K-is-small'
    where
     open resize-using-specified-small-compact-basis sr 𝓓 scb

 ι-⊑-is-small : (x : ⟨ 𝓓 ⟩) (c : K) → is-small (ι c ⊑⟨ 𝓓 ⟩ x)
 ι-⊑-is-small = ∥∥-rec (Π₂-is-prop fe (λ x c → being-small-is-prop
                                                ua (ι c ⊑⟨ 𝓓 ⟩ x) 𝓥))
                       γ uscb
  where
   γ : has-specified-small-compact-basis 𝓓
     → (x : ⟨ 𝓓 ⟩) (c : K) → is-small (ι c ⊑⟨ 𝓓 ⟩ x)
   γ scb = ι-⊑-is-small'
    where
     open resize-using-specified-small-compact-basis sr 𝓓 scb

\end{code}

We now package things up, using the small copy Kₛ of K and a reindexing along
the equivalence Kₛ ≃ K, to produce a small compact basis.

\begin{code}

 Kₛ : 𝓥 ̇
 Kₛ = resized K K-is-small

 ιₛ : Kₛ → ⟨ 𝓓 ⟩
 ιₛ = ι ∘ ⌜ resizing-condition K-is-small ⌝

 ↓-resizing : (x : ⟨ 𝓓 ⟩) → ↓ᴷ x ≃ ↓ᴮ 𝓓 ιₛ x
 ↓-resizing x =
  ≃-sym (Σ-change-of-variable _ ⌜ resizing-condition K-is-small ⌝
                              (⌜⌝-is-equiv (resizing-condition K-is-small)))

 ↓ᴷₛ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↓-inclusion 𝓓 ιₛ x)
 ↓ᴷₛ-is-directed x =
  reindexed-family-is-directed 𝓓 (↓-resizing x) (↓ᴷ-inclusion x) (↓ᴷ-is-directed x)

 ιₛ-is-small-compact-basis : is-small-compact-basis 𝓓 ιₛ
 ιₛ-is-small-compact-basis =
  record
   { basis-is-compact = λ k → ι-is-compact (⌜ resizing-condition K-is-small ⌝ k)
   ; ⊑ᴮ-is-small = λ x k → ι-⊑-is-small x (⌜ resizing-condition K-is-small ⌝ k)
   ; ↓ᴮ-is-directed = ↓ᴷₛ-is-directed
   ; ↓ᴮ-is-sup = λ x → reindexed-family-sup 𝓓 (↓-resizing x)
                                              (↓ᴷ-inclusion x) x (↓ᴷ-is-sup x)
   }

\end{code}

Finally, we arrive at the result announced at the top of this file: the type
(has-specified-small-compact-basis 𝓓) has split support.

\begin{code}

open import UF.KrausLemma
open split-support-and-collapsibility pt

module _
        (ua : Univalence)
        (sr : Set-Replacement pt)
        (𝓓 : DCPO {𝓤} {𝓣})
       where

 specified-small-compact-basis-has-split-support :
  has-split-support (has-specified-small-compact-basis 𝓓)
 specified-small-compact-basis-has-split-support uscb =
  Kₛ , ιₛ , ιₛ-is-small-compact-basis
   where
    open basis-of-compact-elements 𝓓
          (is-algebraic-dcpo-if-unspecified-small-compact-basis 𝓓 uscb)
    open resize-using-unspecified-small-compact-basis ua sr 𝓓 uscb

\end{code}

In particular, we can extract algebraicity structure from an unspecified small
compact basis.

\begin{code}

 structurally-algebraic-if-unspecified-small-compact-basis :
    has-unspecified-small-compact-basis 𝓓
  → structurally-algebraic 𝓓
 structurally-algebraic-if-unspecified-small-compact-basis =
  structurally-algebraic-if-specified-small-compact-basis 𝓓
   ∘ specified-small-compact-basis-has-split-support

\end{code}

Another formulation is that we have the following logical equivalence:

\begin{code}

 specified-unspecified-equivalence :
  has-specified-small-compact-basis 𝓓 ↔ has-unspecified-small-compact-basis 𝓓
 specified-unspecified-equivalence =
    ∣_∣
  , specified-small-compact-basis-has-split-support

\end{code}

We note that the above cannot be promoted to an equivalence of types, because
the left-hand side, the type (has-specified-small-compact-basis 𝓓), is not a
proposition. This may seem puzzling, especially to domain theorists, as there is
a unique basis (as a subset) which consists of compact elements, so we stop to
explain this here.

Recall that
  has-specified-small-compact-basis 𝓓 :=
    Σ B ꞉ 𝓥 ̇ , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , (1) × (2) × (3)
with (1)─(3) expressing that:
  (1) all elements β b are compact,
  (2) (β b ⊑⟨ 𝓓 ⟩ x) is a small type for all elements x, and
  (3) the family (Σ b ꞉ B , β b ⊑⟨ 𝓓 ⟩) → ⟨ 𝓓 ⟩ is directed with sup x.

If we drop smallness condition (2) and allow for B to live in larger universes
than 𝓥, then K, the subset of compact elements with its inclusion K → ⟨ 𝓓 ⟩,
will fit the specification.

If we now add the condition that β is an embedding (as it is for K), then we get
the type
    Σ B ꞉ _ ̇̇ , Σ β ꞉ (B → ⟨ 𝓓 ⟩) , (1) × (3) × (β is an embedding)
which *is* a proposition: it has a unique element in case 𝓓 is algebraic, given
by the *subset* of compact elements of 𝓓. (This is true because any basis must
contain all compact elements.)

This raises a question: why don't we require β to be an embedding in our
definition of a small compact basis to obtain a property instead of truncating
the type has-specified-small-compact-basis?

The reason is that it could be useful, as we illustrate now:

  The canonical map from lists into the powerset of a set X,
    β : List X → 𝓟 X
  is a small compact basis for the algebraic dcpo 𝓟 X. This map is not an
  embedding, as any permutation of a list will give rise to the same subset.

  If we insisted on having an embedding, we would instead have to use the
  inclusion of the Kuratowski finite subsets 𝓚 X into 𝓟 X.  However, 𝓚 X is not
  a small type without additional assumptions, such as HITs or more specifically,
  set replacement (as 𝓚 X is precisely the image of the map β : List X → 𝓟 X).

Returning to the main line of thought, we conclude that, in the presence of set
replacement and univalence, if there is some unspecified small compact basis,
then the subset K of compact elements is suitably small.

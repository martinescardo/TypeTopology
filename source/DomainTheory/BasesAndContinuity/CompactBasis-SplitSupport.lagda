Tom de Jong and Ayberk Tosun, 4 October 2023


RESULT
──────
Assuming set replacement¹ and univalence, we show that:
  if a dcpo has an *unspecified* small compact basis, then it has a *specified*
  small compact basis.

That is, for a dcpo 𝓓, we have:
  ∥ has-specified-small-compact-basis 𝓓 ∥ → has-specified-small-compact-basis 𝓓.

In other words, the type
  has-specified-small-compact-basis 𝓓
has split support.

Or, equivalently, we have a logical equivalence
  has-unspecified-small-compact-basis 𝓓 ⇔ has-specified-small-compact-basis 𝓓.

In particular, we get extract algebraicity structure from an unspecified small
compact basis:
  has-unspecified-small-compact-basis 𝓓 → structurally-algebraic 𝓓.

This result is due to Ayberk Tosun (19 September 2023) and was formalised here
on 4 October 2023 by Tom de Jong.


¹ Set replacement is equivalent to having small set quotients, see
  Quotient.index.


PROOF
─────
The construction is perhaps somewhat lengthy, but the core idea is quite simple
and so we pause to explain it here.

If a dcpo 𝓓 has a small compact basis β : B → 𝓓, then it must contain all
compact elements, as shown in the Bases file.

Given a dcpo 𝓓, we consider the subset ι : K ↪ 𝓓 of compact elements of 𝓓.
Knowing that 𝓓 has an unspecified small compact basis is sufficient for proving
that K (almost) gives a small compact basis of 𝓓, since the required properties
are mostly propositions.
For example, if 𝓓 has an unspecified small compact basis, then, for any x : 𝓓,
the family
  (Σ k ꞉ K , ι k ⊑⟨ 𝓓 ⟩ x) → 𝓓,
given by projecting first and then applying ι, is directed with supremum x.

All these properties are proved at the start of this file.


Two obstacles remain, however:
(1) the type K is (a priori) not small as it quantifies over all elements of 𝓓,
(2) the type (ι k ⊑⟨ 𝓓 ⟩ x) is (a priori) not small.

This is where univalence comes in: being a small type is a property if
univalence is assumed, which means we can try to prove (1) (and also (2), but
for truth values univalence is not strictly needed) by untruncating our
assumption of an unspecified small compact basis.

So we assume a small compact basis β : B → 𝓓 and we consider the map
  β' : B → K
which is given by β and the witness that β maps to compact elements.
Since any small compact basis must contain K, the map β' is surjective, and
hence the image of β' is equivalent to K.

This is where set replacement comes in: it says that if f : X → Y is a map from
a small type to a locally small set, then the image of f is small.
Our type B is small by assumption and K can be shown to be locally small by
using antisymmetry and the small basis. Hence, image β' and therefore K is
small.

Our specified small compact basis is then given by a small copy (up to
equivalence) of K.


\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module DomainTheory.BasesAndContinuity.CompactBasis-SplitSupport
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (𝓥 : Universe) -- where the index types for directed completeness live
       where

open PropositionalTruncation pt

open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Size hiding (is-small ; is-locally-small)
open import UF.Subsingletons

open import DomainTheory.Basics.Dcpo pt fe 𝓥
open import DomainTheory.Basics.Miscelanea pt fe 𝓥
open import DomainTheory.Basics.WayBelow pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Bases pt fe 𝓥
open import DomainTheory.BasesAndContinuity.Continuity pt fe 𝓥

\end{code}

As announced above, we start by establishing as many as properties of K as
possible without considering that K needs to be small.

\begin{code}

module basis-of-compact-elements-preliminaries
        (𝓓 : DCPO {𝓤} {𝓣})
        (uscb : has-unspecified-small-compact-basis 𝓓)
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

 ↓ᴷ-is-inhabited : (x : ⟨ 𝓓 ⟩) → ∥ ↓ᴷ x ∥
 ↓ᴷ-is-inhabited x = ∥∥-rec ∥∥-is-prop γ uscb
  where
   γ : has-specified-small-compact-basis 𝓓
     → ∥ ↓ᴷ x ∥
   γ (B , β , scb) = ∥∥-functor (λ (b , l) → (β b , basis-is-compact b) , l) inh
    where
     open is-small-compact-basis scb
     inh : ∥ ↓ᴮ 𝓓 β x ∥
     inh = inhabited-if-Directed 𝓓 (↓-inclusion 𝓓 β x) (↓ᴮ-is-directed x)

 ↓ᴷ-is-semidirected : (x : ⟨ 𝓓 ⟩) → is-Semidirected 𝓓 (↓ᴷ-inclusion x)
 ↓ᴷ-is-semidirected x =
  ∥∥-rec (being-semidirected-is-prop (underlying-order 𝓓) (↓ᴷ-inclusion x))
         γ uscb
   where
    γ : has-specified-small-compact-basis 𝓓
      → is-Semidirected 𝓓 (↓ᴷ-inclusion x)
    γ (B , β , scb) ((c₁ , c₁-compact) , c₁-below-x)
                    ((c₂ , c₂-compact) , c₂-below-x) =
     ∥∥-rec₂ ∃-is-prop sd ⦅1⦆ ⦅2⦆
      where
       open is-small-compact-basis scb
       sd : (Σ b₁ ꞉ B , β b₁ ＝ c₁)
          → (Σ b₂ ꞉ B , β b₂ ＝ c₂)
          → ∃ c ꞉ ↓ᴷ x , (c₁ ⊑⟨ 𝓓 ⟩ ↓ᴷ-inclusion x c)
                       × (c₂ ⊑⟨ 𝓓 ⟩ ↓ᴷ-inclusion x c)
       sd (b₁ , refl) (b₂ , refl) = ∥∥-functor β' semidir
        where
         β' : (Σ b ꞉ ↓ᴮ 𝓓 β x , (β b₁ ⊑⟨ 𝓓 ⟩ ↓-inclusion 𝓓 β x b)
                              × (β b₂ ⊑⟨ 𝓓 ⟩ ↓-inclusion 𝓓 β x b))
            → (Σ k ꞉ ↓ᴷ x , (β b₁ ⊑⟨ 𝓓 ⟩ ↓ᴷ-inclusion x k)
                          × (β b₂ ⊑⟨ 𝓓 ⟩ ↓ᴷ-inclusion x k))
         β' ((b , b-below-x) , l₁ , l₂) = ((β b , basis-is-compact b)
                                          , b-below-x) , l₁ , l₂
         semidir : ∃ b ꞉ ↓ᴮ 𝓓 β x , (β b₁ ⊑⟨ 𝓓 ⟩ ↓-inclusion 𝓓 β x b)
                                  × (β b₂ ⊑⟨ 𝓓 ⟩ ↓-inclusion 𝓓 β x b)
         semidir = semidirected-if-Directed 𝓓
                    (↓-inclusion 𝓓 β x) (↓ᴮ-is-directed x)
                    (b₁ , c₁-below-x) (b₂ , c₂-below-x)
       ⦅1⦆ : ∃ b₁ ꞉ B , β b₁ ＝ c₁
       ⦅1⦆ = small-compact-basis-contains-all-compact-elements
              𝓓 β scb c₁ c₁-compact
       ⦅2⦆ : ∃ b₂ ꞉ B , β b₂ ＝ c₂
       ⦅2⦆ = small-compact-basis-contains-all-compact-elements
              𝓓 β scb c₂ c₂-compact

 ↓ᴷ-is-directed : (x : ⟨ 𝓓 ⟩) → is-Directed 𝓓 (↓ᴷ-inclusion x)
 ↓ᴷ-is-directed x = ↓ᴷ-is-inhabited x , ↓ᴷ-is-semidirected x

 ↓ᴷ-is-upperbound : (x : ⟨ 𝓓 ⟩)
                  → is-upperbound (underlying-order 𝓓) x (↓ᴷ-inclusion x)
 ↓ᴷ-is-upperbound x c = pr₂ c

 ↓ᴷ-is-sup : (x : ⟨ 𝓓 ⟩) → is-sup (underlying-order 𝓓) x (↓ᴷ-inclusion x)
 ↓ᴷ-is-sup x =
  ∥∥-rec (is-sup-is-prop (underlying-order 𝓓) (pr₁ (axioms-of-dcpo 𝓓))
                         x (↓ᴷ-inclusion x))
         γ uscb
   where
    γ : has-specified-small-compact-basis 𝓓
      → is-sup (underlying-order 𝓓) x (↓ᴷ-inclusion x)
    γ (B , β , scb) = ↓ᴷ-is-upperbound x , lb-of-ubs
     where
      open is-small-compact-basis scb
      lb-of-ubs : is-lowerbound-of-upperbounds (underlying-order 𝓓) x
                                               (↓ᴷ-inclusion x)
      lb-of-ubs y y-is-ub =
       transport (λ - → - ⊑⟨ 𝓓 ⟩ y)
                 (↓ᴮₛ-∐-＝ x)
                 (∐-is-lowerbound-of-upperbounds 𝓓
                  (↓ᴮₛ-is-directed x) y lb-of-ubs')
        where
         lb-of-ubs' : (b : ↓ᴮₛ x) → ↓-inclusionₛ x b ⊑⟨ 𝓓 ⟩ y
         lb-of-ubs' (b , l) = y-is-ub ((β b , basis-is-compact b) , ⊑ᴮₛ-to-⊑ᴮ l)

\end{code}

Only now do we use univalence and set replacement to show that K is small.

\begin{code}

open import UF.Univalence

module basis-of-compact-elements
        (ua : Univalence)
        (sr : Set-Replacement pt)
        (𝓓 : DCPO {𝓤} {𝓣})
        (uscb : has-unspecified-small-compact-basis 𝓓)
       where

 open import UF.ImageAndSurjection pt
 open import UF.Sets
 open import UF.Sets-Properties

 open basis-of-compact-elements-preliminaries 𝓓 uscb

 K-is-small : is-small K
 K-is-small = ∥∥-rec (being-small-is-prop ua K 𝓥) γ uscb
  where
   γ : has-specified-small-compact-basis 𝓓
     → is-small K
   γ (B , β , scb) = ≃-size-contravariance K-is-image image-is-small
    where
     open is-small-compact-basis scb
     open is-locally-small (locally-small-if-small-compact-basis 𝓓 β scb)
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

 ι-⊑-is-small : (x : ⟨ 𝓓 ⟩) (c : K) → is-small (ι c ⊑⟨ 𝓓 ⟩ x)
 ι-⊑-is-small x c = ∥∥-rec (being-small-is-prop ua (ι c ⊑⟨ 𝓓 ⟩ x) 𝓥)
                           γ uscb
  where
   γ : has-specified-small-compact-basis 𝓓
     → is-small (ι c ⊑⟨ 𝓓 ⟩ x)
   γ (B , β , scb) =
    ⌜ local-smallness-equivalent-definitions 𝓓 ⌝ loc-small (ι c) x
     where
      loc-small : is-locally-small 𝓓
      loc-small = locally-small-if-small-compact-basis 𝓓 β scb

\end{code}

We then use a resized version of K and ι to get our small compact basis.

The results about directedness and suprema of ↓ᴷ-inclusion apply almost directly
as we are merely reindexing the family along an equivalence to a small type.

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

We summarise the main results of this file below.

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
    open basis-of-compact-elements-preliminaries 𝓓 uscb
    open basis-of-compact-elements ua sr 𝓓 uscb

 specified-unspecified-equivalence :
  has-specified-small-compact-basis 𝓓 ⇔ has-unspecified-small-compact-basis 𝓓
 specified-unspecified-equivalence =
    ∣_∣
  , specified-small-compact-basis-has-split-support

\end{code}

We stress that the above cannot be promoted to an equivalence of types as there
could be several small compact bases for 𝓓. In a sense, the above says that
there is a canonical one though (which is given by all compact elements).


In particular, we get extract algebraicity structure from an unspecified small
compact basis.

\begin{code}

 structurally-algebraic-if-unspecified-small-compact-basis :
    has-unspecified-small-compact-basis 𝓓
  → structurally-algebraic 𝓓
 structurally-algebraic-if-unspecified-small-compact-basis =
  structurally-algebraic-if-specified-small-compact-basis 𝓓
   ∘ specified-small-compact-basis-has-split-support

\end{code}

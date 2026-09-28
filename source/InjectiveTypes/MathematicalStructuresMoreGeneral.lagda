Martin Escardo, 16th August 2023, with more improvements 18th June 2025.

Injectivity of types of mathematical structures, such as pointed
types, ∞-magmas, magmas, monoids, groups etc.

We give a sufficient condition for types of mathematical structures to
be injective, and we apply it to examples such as the above.

This file generalizes InjectiveTypes.MathematicalStructures at the
cost of perhaps being harder to understand. It relies on the file
InjectiveTypes.Sigma, which also arises as a generalization of the
above original file.

Added 5 November 2025 by Tom de Jong: The type of metric spaces is
injective and this relies on the generalizations developed here. This
is the first example that make uses of the added generality of this file.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

import InjectiveTypes.MathematicalStructures -- For comparison only.

open import UF.Univalence

\end{code}

We assume univalence (and hence function extensionality, which,
follows from it), but no other HoTT/UF extensions, not even
propositional truncations.

\begin{code}

module InjectiveTypes.MathematicalStructuresMoreGeneral
        (ua : Univalence)
       where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import InjectiveTypes.Blackboard fe
open import InjectiveTypes.Sigma fe
open import MLTT.Spartan
open import Taboos.Decomposability fe
open import UF.Base
open import UF.Equiv
open import UF.ClassicalLogic
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier

\end{code}

It is convenient to work with the following definition of (algebraic)
flabbiness of a universe, which uses equivalence of types rather than
equality.

\begin{code}

Flabby : (𝓤 : Universe) → 𝓤 ⁺ ̇
Flabby 𝓤 = Σ ⨆ ꞉ ((p : Ω 𝓤) → (p holds → 𝓤 ̇ ) → 𝓤 ̇ )
                , ((p : Ω 𝓤) (A : p holds → 𝓤 ̇) (h : p holds) → ⨆ p A ≃ A h)

\end{code}

In the presence of univalence we can convert to the usual definition,
and we can always convert in the other direction, but in this file we
need the first one only.

\begin{code}

to-aflabby : Flabby 𝓤 → aflabby (𝓤 ̇ ) 𝓤
to-aflabby {𝓤} (⨆ , e) P i A =
 ⨆ (P , i) A , (λ h → eqtoid (ua 𝓤) _ _ (e (P , i) A h))

from-afabbly : aflabby (𝓤 ̇ ) 𝓤 → Flabby 𝓤
from-afabbly {𝓤} aflab =
 aflabby-extension aflab ,
 (λ p A h → idtoeq _ _ (aflabby-extension-property aflab p A h))

\end{code}

We already know that universes are flabby in two ways, using ⨆ := Π
and ⨆ := Σ, but we give constructions that they are Flabby without
univalence, and hence have better computational behaviour, which will
simplify the applications we have in mind.

If the index type is a proposition, then the projection out of a
Π-type is an equivalence.

\begin{code}

Π-𝕡𝕣𝕠𝕛 : (p : Ω 𝓤) {A : p holds → 𝓤 ̇ } (h : p holds)
      → Π A ≃ A h
Π-𝕡𝕣𝕠𝕛 p h = Π-proj h , Π-proj-is-equiv h fe' (holds-is-prop p)

universes-are-Flabby-Π : Flabby 𝓤
universes-are-Flabby-Π = (λ p A → Π A) ,
                         (λ p A → Π-𝕡𝕣𝕠𝕛 p)

universes-are-flabby-Π : aflabby (𝓤  ̇) 𝓤
universes-are-flabby-Π = to-aflabby universes-are-Flabby-Π

Σ-𝕚𝕟 : (p : Ω 𝓤) {A : p holds → 𝓤 ̇ } (h : p holds)
    → A h ≃ Σ A
Σ-𝕚𝕟 p h = Σ-in h , Σ-in-is-equiv h (holds-is-prop p)

universes-are-Flabby-Σ : Flabby 𝓤
universes-are-Flabby-Σ = (λ p A → Σ A) ,
                         (λ p A h → ≃-sym (Σ-𝕚𝕟 p h))

universes-are-flabby-Σ : aflabby (𝓤  ̇) 𝓤
universes-are-flabby-Σ = to-aflabby universes-are-Flabby-Σ

\end{code}

We now work with an arbitrary notion S of structure on 𝓤. E.g. for
monoids we will take S X := X → X → X, the type of the multiplication
operation.

\begin{code}

module _ (S : 𝓤 ̇ → 𝓥 ̇ ) where

\end{code}

By the results of InjectiveTypes.Sigma, we get that Σ S is aflabby in
two ways, assuming the compatibility condition for the flabbiness
data.

\begin{code}

 module _ (ϕ : aflabby (𝓤 ̇ ) 𝓤) where

  aflabbiness-of-type-of-structured-types : compatibility-data S ϕ
                                          → aflabby (Σ S) 𝓤
  aflabbiness-of-type-of-structured-types = Σ-is-aflabby S ϕ

  ainjectivity-of-type-of-structures : compatibility-data S ϕ
                                     → ainjective-type (Σ S) 𝓤 𝓤
  ainjectivity-of-type-of-structures = aflabby-types-are-ainjective (Σ S)
                                       ∘ aflabbiness-of-type-of-structured-types

\end{code}

We will apply this to get our desired examples with ϕ taken to be the
above canonical Π-flabby structure on the universe in most cases, and
at least one with the canonical Σ-flabby structure.

Next we want to simplify working with compatibility data (as defined
in the module InjectiveTypes.Sigma), where we avoid transports by
working with the following function treq and suitable choices of T and
T-refl in the examples below. Notice that the definition of treq uses
univalence. The point of T and T-refl below is that they won't use
univalence in our examples of interest, so that they will have a
better computational behaviour than treq.

\begin{code}

 treq : {X Y : 𝓤 ̇ } → X ≃ Y → S X → S Y
 treq {X} {Y} 𝕗 = transport S (eqtoid (ua 𝓤) X Y 𝕗)

\end{code}

The main additional work in this file on top of InjectiveTypes.Sigma
is to make it easier to work with the compatibility condition for the
purpose of injectivity of types of mathematical structures.

We work with hypothetical T and T-refl with the following types.

\begin{code}

 module _ (T      : {X Y : 𝓤 ̇ } → X ≃ Y → S X → S Y)
          (T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id)
        where

\end{code}

The point is that any such T can be equivalently expressed as a
transport and hence we may apply the theorems of the imported file
InjectiveTypes.Sigma, but it may be easier to check the compatibility
condition using T rather than transport (see examples below).

\begin{code}

  T-is-treq : {X Y : 𝓤 ̇ } (𝕗 : X ≃ Y)
            → T 𝕗 ∼ treq 𝕗
  T-is-treq {X} {Y} 𝕗 s = JEq (ua 𝓤) X A I Y 𝕗
   where
    A : (Y : 𝓤 ̇ ) (𝕗 : X ≃ Y) → 𝓥 ̇
    A Y 𝕗 = T 𝕗 s ＝ treq 𝕗 s

    I : A X (≃-refl X)
    I = T (≃-refl X) s                                ＝⟨ T-refl s ⟩
        s                                             ＝⟨refl⟩
        transport S refl s                            ＝⟨ II ⟩
        transport S (eqtoid (ua 𝓤) X X (≃-refl X)) s  ＝⟨refl⟩
        treq (≃-refl X) s                             ∎
      where
       II = (ap (λ - → transport S - s) (eqtoid-refl (ua 𝓤) X))⁻¹

\end{code}

In order to be able to apply the results of InjectiveTypes.Sigma, we
perform the following construction. That file requires compatibility
data of a certain kind, which we reduce to compatibility of another
kind, which will be easier to produce in our sample applications.

\begin{code}

  module compatibility-data-construction (ϕ@(⨆ , ε) : Flabby 𝓤) where

   derived-ρ : (p : Ω 𝓤)
               (A : p holds → 𝓤 ̇ )
             → S (⨆ p A) → ((h : p holds) → S (A h))
   derived-ρ p A s h = T (ε p A h) s

   compatibility-data-for-derived-ρ : 𝓤 ⁺ ⊔ 𝓥 ̇
   compatibility-data-for-derived-ρ = (p : Ω 𝓤)
                                      (A : p holds → 𝓤 ̇ )
                                    → has-section (derived-ρ p A)

   construction : compatibility-data-for-derived-ρ
                → compatibility-data S (to-aflabby ϕ)
   construction t p A = III
    where

     II : derived-ρ p A ∼ ρ S (to-aflabby ϕ) p A
     II s =
      derived-ρ p A s                                     ＝⟨refl⟩
      (λ h → T (ε p A h) s)                               ＝⟨ I₀ ⟩
      (λ h → treq (ε p A h) s)                            ＝⟨refl⟩
      (λ h → transport S (eqtoid (ua 𝓤) _ _ (ε p A h)) s) ＝⟨refl⟩
      ρ S (to-aflabby ϕ) p A s                           ∎
      where
       I₀ = dfunext fe' (λ h → T-is-treq (ε p A h) s)

     III : has-section (ρ S (to-aflabby ϕ) p A)
     III = has-section-closed-under-∼ (derived-ρ p A) _ (t p A) (∼-sym II)

\end{code}

This completes the construction, but we record that the section map of
the above construction is literally the same as that of the
hypothesis t.

\begin{code}

     _ = section-map (ρ S (to-aflabby ϕ) p A) III  ＝⟨refl⟩
         section-map (derived-ρ p A) (t p A)        ∎

\end{code}

What is necessarily different is the proof that this map is a
section. In fact, it is different in the strong sense that the
comparison for equality doesn't even make sense - it wouldn't even
typecheck.

A way to verify this in Agda is to try to supply the following naive
definition.

   construction' : compatibility-data-for-derived-ρ
                 → compatibility-data S (to-aflabby ϕ)
   construction' t = t -- Doesn't type check (of course).

We can sensibly have only that the *section map* of the construction
agrees with the given section map, which is what we have already
observed in the above proof, but record again with full type
information, outside the above proof.

\begin{code}

   construction-fact : (p : Ω 𝓤)
                       (A : p holds → 𝓤 ̇)
                       (t : compatibility-data-for-derived-ρ)
                     → section-map (ρ S (to-aflabby ϕ) p A) (construction t p A)
                     ＝ section-map (derived-ρ p A)         (t p A)
   construction-fact p A t = refl

\end{code}

This fact about the construction will be rather useful in practice,
for the applications we have in mind.

We can specialize this to the Π and Σ flabbiness structures discussed
above, to get the following.

\begin{code}

  module _ where

   open compatibility-data-construction universes-are-Flabby-Π

   ρΠ : (p : Ω 𝓤)
        (A : p holds → 𝓤 ̇ )
      → S (Π A) → ((h : p holds) → S (A h))
   ρΠ = derived-ρ

   compatibility-data-Π : 𝓤 ⁺ ⊔ 𝓥 ̇
   compatibility-data-Π = (p : Ω 𝓤)
                          (A : p holds → 𝓤 ̇ )
                        → has-section (ρΠ p A)

   Π-construction : compatibility-data-Π
                  → compatibility-data S universes-are-flabby-Π
   Π-construction = construction

\end{code}

We use the following definitional equality a number of times (and we
try to record this explicitly when we do so).

\begin{code}

   _ : ρΠ ＝ λ p A s h → T (Π-𝕡𝕣𝕠𝕛 p h) s
   _ = refl

\end{code}

For most examples below, we only need the above functions ρΠ,
compatibility-data-Π and Π-construction, but at least one of them uses
their Σ versions defined below.

\begin{code}

  module _ where

   open compatibility-data-construction universes-are-Flabby-Σ

   ρΣ : (p : Ω 𝓤)
        (A : p holds → 𝓤 ̇ )
      → S (Σ A) → ((h : p holds) → S (A h))
   ρΣ = derived-ρ

   compatibility-data-Σ : 𝓤 ⁺ ⊔ 𝓥 ̇
   compatibility-data-Σ = (p : Ω 𝓤)
                          (A : p holds → 𝓤 ̇ )
                        → has-section (ρΣ p A)

   Σ-construction : compatibility-data-Σ
                  → compatibility-data S universes-are-flabby-Σ
   Σ-construction = construction

\end{code}

Example. The type of pointed types is algebraically injective. We use
the Π-flabbiness of the universe.

\begin{code}

Pointed-type : (𝓤 : Universe) → 𝓤 ⁺ ̇
Pointed-type 𝓤 = Σ X ꞉ 𝓤 ̇ , X

Pointed : 𝓤 ̇ → 𝓤 ̇
Pointed X = X

Pointed-Π-data : compatibility-data (Pointed {𝓤}) universes-are-flabby-Π
Pointed-Π-data {𝓤} = Π-construction Pointed T T-refl c
 where
  S = Pointed

  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → X → Y
  T = ⌜_⌝

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl x = refl

  _ : (p : Ω 𝓤) (A : p holds → 𝓤 ̇) → ρΠ S T T-refl p A ＝ 𝑖𝑑 (S (Π A))
  _ = λ p A → refl

  c : compatibility-data-Π S T T-refl
  c p A = equivs-have-sections id (id-is-equiv (Π A))

\end{code}

Hence we conclude that the type of pointed types is ainjective.

\begin{code}

ainjectivity-of-type-of-pointed-types : ainjective-type (Pointed-type 𝓤) 𝓤 𝓤
ainjectivity-of-type-of-pointed-types =
 ainjectivity-of-type-of-structures
  Pointed
  universes-are-flabby-Π
  Pointed-Π-data

\end{code}

Example. The type of ∞-magmas is algebraically injective. The proof is
an entirely routine application of the above general theorem after we
guess what T should be.

\begin{code}

∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → X)

∞-magma-structure : 𝓤 ̇ → 𝓤 ̇
∞-magma-structure = λ X → X → X → X

∞-Magma-structure-Π-data : compatibility-data
                            (∞-magma-structure {𝓤})
                            universes-are-flabby-Π
∞-Magma-structure-Π-data {𝓤} =
 Π-construction S T T-refl ρΠ-has-section
 where
  S = ∞-magma-structure

  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → S X → S Y
  T 𝕗 _·_ = λ y y' → ⌜ 𝕗 ⌝ (⌜ 𝕗 ⌝⁻¹ y · ⌜ 𝕗 ⌝⁻¹ y')

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl _·_ = refl

  module _ (p : Ω 𝓤)
           (A : p holds → 𝓤 ̇ )
         where

   π : (h : p holds) → Π A ≃ A h
   π = Π-𝕡𝕣𝕠𝕛 p

   r : S (Π A) → ((h : p holds) → S (A h))
   r _·_ h a b = ⌜ π h ⌝ (⌜ π h ⌝⁻¹ a · ⌜ π h ⌝⁻¹ b)

   _ : r ＝ ρΠ S T T-refl p A
   _ = refl -- Which is crucial for the proof below to work.

   σ : ((h : p holds) → S (A h)) → S (Π A)
   σ g α β h = g h (⌜ π h ⌝ α) (⌜ π h ⌝ β)

   rσ : r ∘ σ ∼ id
   rσ g =
    r (σ g)                                                         ＝⟨refl⟩
    (λ h a b → g h (⌜ π h ⌝ (⌜ π h ⌝⁻¹ a)) (⌜ π h ⌝ (⌜ π h ⌝⁻¹ b))) ＝⟨ II ⟩
    (λ h a b → g h a b)                                             ＝⟨refl⟩
    g                                                               ∎
     where
      II = dfunext fe' (λ h →
           dfunext fe' (λ a →
           dfunext fe' (λ b →
            ap₂ (g h)
             (inverses-are-sections' (π h) a)
             (inverses-are-sections' (π h) b))))

   ρΠ-has-section : has-section (ρΠ S T T-refl p A)
   ρΠ-has-section = σ , rσ

ainjectivity-of-∞-Magma : ainjective-type (∞-Magma 𝓤) 𝓤 𝓤
ainjectivity-of-∞-Magma =
 ainjectivity-of-type-of-structures
  ∞-magma-structure
  universes-are-flabby-Π
  ∞-Magma-structure-Π-data

\end{code}

A corollary is that the type ∞-Magma 𝓤 doesn't have any non-trivial
decidable property unless weak excluded middle holds.

\begin{code}

decomposition-of-∞-Magma-gives-WEM : decomposition (∞-Magma 𝓤) → typal-WEM 𝓤
decomposition-of-∞-Magma-gives-WEM {𝓤} =
 decomposition-of-ainjective-type-gives-WEM
  (univalence-gives-propext (ua 𝓤))
  (∞-Magma 𝓤)
  ainjectivity-of-∞-Magma

\end{code}

The same is true for the type of pointed types, of course, and for any
injective type.

Example. The type of pointed ∞-magmas is injective.

\begin{code}

open import UF.SIP-Examples
open monoid

∞-Magma∙ : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma∙ 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → X) × X

∞-Magma∙-structure : 𝓤 ̇ → 𝓤 ̇
∞-Magma∙-structure = monoid-structure

∞-Magma∙-structure-Π-data : compatibility-data
                             (∞-Magma∙-structure {𝓤})
                             universes-are-flabby-Π
∞-Magma∙-structure-Π-data =
 compatibility-data-×
  universes-are-flabby-Π
  ∞-Magma-structure-Π-data
  Pointed-Π-data

ainjectivity-of-∞-Magma∙ : ainjective-type (∞-Magma∙ 𝓤) 𝓤 𝓤
ainjectivity-of-∞-Magma∙ =
 ainjectivity-of-type-of-structures
  ∞-Magma∙-structure
  universes-are-flabby-Π
  ∞-Magma∙-structure-Π-data

\end{code}

Example. The type of monoids is injective. We just have to check that
the monoid axioms are closed under Π.

\begin{code}

Monoid-Π-data : compatibility-data {𝓤 ⁺}
                 (λ X → Σ s ꞉ monoid-structure X , monoid-axioms X s)
                 universes-are-flabby-Π
Monoid-Π-data {𝓤} =
 compatibility-data-with-axioms
  universes-are-flabby-Π
  monoid-structure
  ∞-Magma∙-structure-Π-data
  monoid-axioms
  (monoid-axioms-is-prop fe')
  axioms-Π-data
 where
  σ : (p : Ω 𝓤) (A : p holds → 𝓤 ̇ )
    → ((h : p holds) → monoid-structure (A h)) → monoid-structure (Π A)
  σ p A = section-map
           (ρ monoid-structure universes-are-flabby-Π p A)
           (∞-Magma∙-structure-Π-data p A)

  axioms-Π-data
   : (p : Ω 𝓤)
     (A : p holds → 𝓤 ̇ )
     (α : (h : p holds) → monoid-structure (A h))
     (F : (h : p holds) → monoid-axioms (A h) (α h))
   → monoid-axioms (Π A) (σ p A α)
  axioms-Π-data p A α F = I , II , III , IV
   where
    _*_ : {h : p holds} → A h → A h → A h
    _*_ {h} = pr₁ (α h)

    _·_ : Π A → Π A → Π A
    (f · g) h = f h * g h

    e : Π A
    e h = pr₂ (α h)

    _ : σ p A α ＝ (_·_ , e)
    _ = refl -- Which is crucial for the proof below to work.

    I : is-set (Π A)
    I = Π-is-set fe' (λ h →
         case F h of
          λ (Ah-is-set , ln , rn , assoc) → Ah-is-set)

    II : left-neutral e _·_
    II f = dfunext fe' (λ h →
            case F h of
             λ (Ah-is-set , ln , rn , assoc) → ln (f h))

    III : right-neutral e _·_
    III g = dfunext fe' (λ h →
             case F h of
              λ (Ah-is-set , ln , rn , assoc) → rn (g h))

    IV : associative _·_
    IV f g k = dfunext fe' (λ h →
                case F h of
                 λ (Ah-is-set , ln , rn , assoc) → assoc (f h) (g h) (k h))

ainjectivity-of-Monoid : ainjective-type (Monoid {𝓤}) 𝓤 𝓤
ainjectivity-of-Monoid {𝓤} =
 ainjectivity-of-type-of-structures
  (λ X → Σ s ꞉ monoid-structure X , monoid-axioms X s)
  universes-are-flabby-Π
  Monoid-Π-data

\end{code}

It is easy to add further axioms to monoids to get groups, and then
show that the type of groups is injective using the above
technique. This is just as routine as the example of monoids. All one
needs to do is to show that the group axioms are closed under
prop-indexed products.

TODO. Maybe implement this.

NB. The type Ordinal 𝓤 of well-ordered sets in 𝓤 is also injective,
but for different reasons, two of them given in two different modules.

Added 20th June 2025. The type of all families in a universe is
injective.

\begin{code}

Fam : (𝓤 : Universe) → 𝓤 ⁺ ̇
Fam 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → 𝓤 ̇)

Fam-structure : 𝓤 ̇ → 𝓤 ⁺ ̇
Fam-structure {𝓤} X = X → 𝓤 ̇

open import UF.EquivalenceExamples
open import UF.Subsingletons

Fam-Π-data : compatibility-data (Fam-structure {𝓤}) universes-are-flabby-Π
Fam-Π-data {𝓤} = Π-construction Fam-structure T T-refl c
 where
  S = Fam-structure

  T : {X Y : 𝓤 ̇} → X ≃ Y → (X → 𝓣 ̇ ) → (Y → 𝓣 ̇ )
  T 𝕗 R = λ y → R (⌜ 𝕗 ⌝⁻¹ y)

  T-refl : {X : 𝓤 ̇} → T (≃-refl X) ∼ id
  T-refl R = refl

  module _ (p : Ω 𝓤) (A : p holds → 𝓤 ̇) where

   r :  S (Π A) → ((h : p holds) → S (A h))
   r s h a = s (⌜ Π-𝕡𝕣𝕠𝕛 p h ⌝⁻¹ a)

   _ : ρΠ S T T-refl p A ＝ r
   _ = refl

   σ : ((h : p holds) → S (A h)) → S (Π A)
   σ g f = (h : p holds) → g h (f h)

   rσ : r ∘ σ ∼ id
   rσ g = dfunext fe' (λ h → dfunext fe' (II h))
    where
     module _ (h : p holds) (a : A h) where

      π : Π A ≃ A h
      π = Π-𝕡𝕣𝕠𝕛 p h

      I = ((h' : p holds) → g h' (⌜ π ⌝⁻¹ a h')) ≃⟨ I₀ ⟩
          (p holds → g h (⌜ π ⌝⁻¹ a h))          ≃⟨ I₁ ⟩
          (𝟙 → g h (⌜ π ⌝⁻¹ a h))                ≃⟨ I₂ ⟩
          g h (⌜ π ⌝⁻¹ a h)                      ■
        where
         I₀ = Π-cong fe' fe'
               (λ h' → transport (λ - → g - (⌜ π ⌝⁻¹ a -))
                                 (holds-is-prop p h' h) ,
                       transports-are-equivs (holds-is-prop p h' h))
         I₁ = Π-change-of-variable-≃ {𝓤} {𝓤} fe
               (λ _ → g h (⌜ π ⌝⁻¹ a h))
               (logically-equivalent-props-are-equivalent
                 (holds-is-prop p) 𝟙-is-prop unique-to-𝟙 (λ _ → h))
         I₂ = ≃-sym (𝟙→ fe')

      II = r (σ g) h a                            ＝⟨refl⟩
           σ g (⌜ π ⌝⁻¹ a)                        ＝⟨refl⟩
           ((h' : p holds) → g h' (⌜ π ⌝⁻¹ a h')) ＝⟨ II₀ ⟩
           g h (⌜ π ⌝⁻¹ a h)                      ＝⟨refl⟩
           g h (⌜ π ⌝ (⌜ π ⌝⁻¹ a))                ＝⟨ II₁ ⟩
           g h a                                  ∎
            where
             II₀  = eqtoid (ua 𝓤) _ _ I
             II₁ = ap (g h) (inverses-are-sections' π a)

  c :  compatibility-data-Π Fam-structure T T-refl
  c p A = σ p A , rσ p A

ainjectivity-of-Fam : ainjective-type (Fam 𝓤) 𝓤 𝓤
ainjectivity-of-Fam =
 ainjectivity-of-type-of-structures
  Fam-structure
  universes-are-flabby-Π
  Fam-Π-data

\end{code}

A corollary is that the type of all functions in a universe is injective.

\begin{code}

open import UF.Classifiers

ainjectivity-of-type-of-all-functions
 : ainjective-type (Σ X ꞉ 𝓤 ̇ , Σ Y ꞉ 𝓤 ̇ , (X → Y)) 𝓤 𝓤
ainjectivity-of-type-of-all-functions {𝓤}
 = transport
    (λ - → ainjective-type - 𝓤 𝓤)
    (eqtoid (ua (𝓤 ⁺)) _ _ (≃-sym I))
    ainjectivity-of-Fam
 where
  open classifier-single-universe 𝓤

  I = (Σ X ꞉ 𝓤 ̇ , Σ Y ꞉ 𝓤 ̇ , (X → Y)) ≃⟨ Σ-flip ⟩
      (Σ Y ꞉ 𝓤 ̇ , Σ X ꞉ 𝓤 ̇ , (X → Y)) ≃⟨ Σ-cong (classification (ua 𝓤) fe') ⟩
      (Σ Y ꞉ 𝓤 ̇ , (Y → 𝓤 ̇))           ≃⟨by-definition⟩
      Fam 𝓤                           ■

\end{code}

The type of all type-valued relations, or multigraphs, in a universe
is injective. The proof is the binary version of the above unary proof.

\begin{code}

Graph : (𝓤 : Universe) → 𝓤 ⁺ ̇
Graph 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → 𝓤 ̇)

graph-structure : 𝓤 ̇ → 𝓤 ⁺ ̇
graph-structure {𝓤} X = X → X → 𝓤 ̇


Graph-Π-data : compatibility-data (graph-structure {𝓤}) universes-are-flabby-Π
Graph-Π-data {𝓤} =
 Π-construction graph-structure T T-refl c
 where
  S = graph-structure

  T : {X Y : 𝓤 ̇} → X ≃ Y → (X → X → 𝓣 ̇ ) → (Y → Y → 𝓣 ̇ )
  T 𝕗 R y y' = R (⌜ 𝕗 ⌝⁻¹ y) (⌜ 𝕗 ⌝⁻¹ y')

  T-refl : {X : 𝓤 ̇} → T (≃-refl X) ∼ id
  T-refl R = refl

  module _ (p : Ω 𝓤) (A : p holds → 𝓤 ̇) where

   r :  S (Π A) → ((h : p holds) → S (A h))
   r s h a a' = s (⌜ Π-𝕡𝕣𝕠𝕛 p h ⌝⁻¹ a) (⌜ Π-𝕡𝕣𝕠𝕛 p h ⌝⁻¹ a')

   _ : r ＝ ρΠ S T T-refl p A
   _ = refl

   σ : ((h : p holds) → S (A h)) → S (Π A)
   σ g f f' = (h : p holds) → g h (f h) (f' h)

   rσ : r ∘ σ ∼ id
   rσ g = dfunext fe' (λ h →
          dfunext fe' (λ a →
          dfunext fe' (λ a' → II h a a')))
    where
     module _ (h : p holds) (a a' : A h) where

      π : Π A ≃ A h
      π = Π-𝕡𝕣𝕠𝕛 p h

      I = ((h' : p holds) → g h' (⌜ π ⌝⁻¹ a h') (⌜ π ⌝⁻¹ a' h')) ≃⟨ I₀ ⟩
          (p holds → g h (⌜ π ⌝⁻¹ a h) (⌜ π ⌝⁻¹ a' h))           ≃⟨ I₁ ⟩
          (𝟙 → g h (⌜ π ⌝⁻¹ a h) (⌜ π ⌝⁻¹ a' h))                 ≃⟨ I₂ ⟩
          g h (⌜ π ⌝⁻¹ a h) (⌜ π ⌝⁻¹ a' h)                       ■
        where
         I₀ = Π-cong fe' fe'
               (λ h' → transport (λ - → g - (⌜ π ⌝⁻¹ a -) (⌜ π ⌝⁻¹ a' -))
                                 (holds-is-prop p h' h) ,
                       transports-are-equivs (holds-is-prop p h' h))
         I₁ = Π-change-of-variable-≃ {𝓤} {𝓤} fe
               (λ _ → g h (⌜ π ⌝⁻¹ a h) (⌜ π ⌝⁻¹ a' h))
               (logically-equivalent-props-are-equivalent
                 (holds-is-prop p) 𝟙-is-prop unique-to-𝟙 (λ _ → h))
         I₂ = ≃-sym (𝟙→ fe')

      II = r (σ g) h a a'                                         ＝⟨refl⟩
           σ g (⌜ π ⌝⁻¹ a) (⌜ π ⌝⁻¹ a')                           ＝⟨refl⟩
           ((h' : p holds) → g h' (⌜ π ⌝⁻¹ a h') (⌜ π ⌝⁻¹ a' h')) ＝⟨ II₀ ⟩
           g h (⌜ π ⌝⁻¹ a h) (⌜ π ⌝⁻¹ a' h)                       ＝⟨refl⟩
           g h (⌜ π ⌝ (⌜ π ⌝⁻¹ a)) (⌜ π ⌝ (⌜ π ⌝⁻¹ a'))           ＝⟨ II₁ ⟩
           g h a a'                                               ∎
            where
             II₀  = eqtoid (ua 𝓤) _ _ I
             II₁ = ap₂ (g h)
                       (inverses-are-sections' π a)
                       (inverses-are-sections' π a')

  c :  compatibility-data-Π graph-structure T T-refl
  c p A = σ p A , rσ p A

ainjectivity-of-Graph : ainjective-type (Graph 𝓤) 𝓤 𝓤
ainjectivity-of-Graph =
 ainjectivity-of-type-of-structures
  graph-structure
  universes-are-flabby-Π
  Graph-Π-data

\end{code}

As a consequence, we get the injectivity of the type of posets.

\begin{code}

poset-axioms : (X : 𝓤 ̇ ) → graph-structure X → 𝓤 ̇
poset-axioms X _≤_ = is-set X
                   × ((x y : X) → is-prop (x ≤ y))
                   × reflexive     _≤_
                   × transitive    _≤_
                   × antisymmetric _≤_

Poset : (𝓤 : Universe) → 𝓤 ⁺ ̇
Poset 𝓤 = Σ X ꞉ 𝓤 ̇ , Σ s ꞉ graph-structure X , poset-axioms X s

open import UF.Subsingletons-FunExt

poset-axioms-is-prop : (X : 𝓤 ̇ ) (s : graph-structure X)
                     → is-prop (poset-axioms X s)
poset-axioms-is-prop X _≤_ = prop-criterion I
 where
  I : poset-axioms X _≤_ → is-prop (poset-axioms X _≤_)
  I (s , pv , r , t , a) =
   ×₅-is-prop
    (being-set-is-prop fe')
    (Π₂-is-prop fe' (λ x y → being-prop-is-prop fe'))
    (Π-is-prop fe' (λ x → pv x x))
    (Π₅-is-prop fe' (λ x _ z _ _ → pv x z))
    (Π₄-is-prop fe' (λ _ _ _ _ → s))

Poset-Π-data : compatibility-data {𝓤 ⁺}
                 (λ X → Σ s ꞉ graph-structure X , poset-axioms X s)
                 universes-are-flabby-Π
Poset-Π-data {𝓤} =
 compatibility-data-with-axioms
  universes-are-flabby-Π
  graph-structure
  Graph-Π-data
  poset-axioms
  poset-axioms-is-prop
  axioms-Π-data
 where
  σ : (p : Ω 𝓤) (A : p holds → 𝓤 ̇ )
    → ((h : p holds) → graph-structure (A h)) → graph-structure (Π A)
  σ p A = section-map
           (ρ graph-structure universes-are-flabby-Π p A)
           (Graph-Π-data p A)

  axioms-Π-data
   : (p : Ω 𝓤)
     (A : p holds → 𝓤 ̇ )
     (α : (h : p holds) → graph-structure (A h))
     (F : (h : p holds) → poset-axioms (A h) (α h))
   → poset-axioms (Π A) (σ p A α)
  axioms-Π-data p A α F = I , II , III , IV , V
   where
    _⊑_ : {h : p holds} → A h → A h → 𝓤 ̇
    _⊑_ {h} = α h

    _≤_ : Π A → Π A → 𝓤 ̇
    f ≤ g = (h : p holds) → f h ⊑ g h

    _ : σ p A α ＝ _≤_
    _ = refl -- Which is crucial for the proof below to work.

    I : is-set (Π A)
    I = Π-is-set fe' (λ h →
         case F h of
          λ (s , pv , r , t , a) → s)

    II : (f g : Π A) → is-prop (f ≤ g)
    II f g = Π-is-prop fe' (λ h →
              case F h of
               λ (s , pv , r , t , a) → pv (f h) (g h))

    III : reflexive _≤_
    III f h =
     case F h of
      λ (s , pv , r , t , a) → r (f h)

    IV : transitive _≤_
    IV f₀ f₁ f₂ l m h =
     case F h of
      λ (s , pv , r , t , a) → t (f₀ h) (f₁ h) (f₂ h) (l h) (m h)

    V : antisymmetric _≤_
    V f₀ f₁ l m = dfunext fe' (λ h →
                   case F h of
                    λ (s , pv , r , t , a) → a (f₀ h) (f₁ h) (l h) (m h))

ainjectivity-of-Poset : ainjective-type (Poset 𝓤) 𝓤 𝓤
ainjectivity-of-Poset {𝓤} =
 ainjectivity-of-type-of-structures
  (λ X → Σ s ꞉ graph-structure X , poset-axioms X s)
  universes-are-flabby-Π
  Poset-Π-data

\end{code}

Notice that, just as in the case for monoids, the proof amounts to
showing that posets are closed under prop-indexed products. Using the
same idea, it is straightforward to show that the types of dcpos,
continuous dcpos, suplattices, frames etc. are all injective. (Notice
that this is different from e.g. saying that the underlying type of a dcpos is
injective, which is also true and is proved in InjectiveTypes.PointedDcpos.)

TODO. Maybe implement (some of) these examples.

TODO. More techniques are needed to show that the type of 1-categories
would be injective. A category can be seen as a graph equipped with
operations (identity and composition) satisfying properties (identity
laws, associativity, univalence).

Added 24 July 2025 by Tom de Jong.

In InjectiveTypes.InhabitedTypesTaboo we showed that the type of nonempty types
is injective by exhibiting it as a retract of the universe. In line with the
condition from InjectiveTypes.Subtypes, the argument there shows that a type is
nonempty if and only if it is a fixed point of the map X ↦ (¬¬ X → X).

Here is an alternative proof, using that
   (Π (p : P) , ¬¬ A p)   →   ¬¬ Π (p : P) , A p
holds when P is a proposition.

\begin{code}

Nonempty-Π-data : compatibility-data (is-nonempty {𝓤}) universes-are-flabby-Π
Nonempty-Π-data {𝓤} = Π-construction is-nonempty T T-refl c
 where
  S = is-nonempty

  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → S X → S Y
  T e = ¬¬-functor ⌜ e ⌝

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl x = refl

  σ : (p : Ω 𝓤) (A : p holds → 𝓤 ̇ )
    → ((h : p holds) → S (A h)) → S (Π A)
  σ p A φ ν = III
   where
    I : (h : p holds) → ¬ A h
    I h a = ν (λ h' → transport A (holds-is-prop p h h') a)

    II : ¬ (p holds)
    II h = φ h (I h)

    III : 𝟘
    III = ν (λ h → 𝟘-elim (II h))

  c : compatibility-data-Π S T T-refl
  c p A = σ p A , (λ φ → dfunext fe' (λ h → negations-are-props fe' _ _))

ainjectivity-of-type-of-nonempty-types
 : ainjective-type (Σ X ꞉ 𝓤 ̇ , is-nonempty X) 𝓤 𝓤
ainjectivity-of-type-of-nonempty-types =
 ainjectivity-of-type-of-structures
  is-nonempty
  universes-are-flabby-Π
  Nonempty-Π-data

\end{code}

Added 5 November 2025 by Tom de Jong.

All previous examples used the Π-flabbiness structure on the universe. In what
follows we put the extra generality of our machinery to good use by instead
employing the Σ-flabbiness structure to prove that the type of metric spaces is
injective.

As a first step we show that the collection of types with an R-valued relation
(for an arbitrary type R, later taken to be ℝ) to be injective.
We denote this type by Graph' as it generalizes the type Graph of graphs defined
above. Indeed, the injectivity proof mirrors the above construction for Graph.

\begin{code}

open import UF.Subsingletons-Properties

module _ (R : 𝓥 ̇ ) where

 Graph' : (𝓤 : Universe) → 𝓤 ⁺ ⊔ 𝓥 ̇
 Graph' 𝓤 = Σ X ꞉ 𝓤 ̇  , (X → X → R)

 graph'-structure : 𝓤 ̇  → 𝓥 ⊔ 𝓤 ̇
 graph'-structure X = (X → X → R)

 Graph'-Σ-data
  : compatibility-data (graph'-structure {𝓤}) universes-are-flabby-Σ
 Graph'-Σ-data {𝓤} =
  Σ-construction S T T-refl c
   where
    S = graph'-structure

    T : {X Y : 𝓤 ̇ } → X ≃ Y → S X → S Y
    T 𝕗 μ y y' = μ (⌜ 𝕗 ⌝⁻¹ y) (⌜ 𝕗 ⌝⁻¹ y')

    T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
    T-refl R = refl

    module _ (p : Ω 𝓤) (A : p holds → 𝓤 ̇) where

     r :  S (Σ A) → ((h : p holds) → S (A h))
     r μ h a a' = μ (h , a) (h , a')

     _ : r ＝ ρΣ S T T-refl p A
     _ = refl

     σ : ((h : p holds) → S (A h)) → S (Σ A)
     σ g (h , a) (h' , a') =
      g h (⌜ Σ-𝕚𝕟 p {A} h ⌝⁻¹ (h , a)) (⌜ Σ-𝕚𝕟 p h ⌝⁻¹ (h' , a'))

     rσ : r ∘ σ ∼ id
     rσ g = dfunext fe' (λ h →
            dfunext fe' (λ a →
            dfunext fe' (λ a' →
            ap₂ (g h) (transport-over-prop (holds-is-prop p))
                      (transport-over-prop (holds-is-prop p)))))

    c : compatibility-data-Σ S T T-refl
    c p A = σ p A , rσ p A

 ainjectivity-of-Graph'
  : ainjective-type (Graph' 𝓤) 𝓤 𝓤
 ainjectivity-of-Graph' =
  ainjectivity-of-type-of-structures
   graph'-structure
   universes-are-flabby-Σ
   Graph'-Σ-data

\end{code}

We now take R = ℝ, the type of Dedekind reals, and additionally impose the
axioms of a metric space.

This mirrors the above construction for the type of posets.

\begin{code}

open import UF.PropTrunc

module _
        (pt : propositional-truncations-exist)
       where

 open PropositionalTruncation pt

 private
  pe : PropExt
  pe = Univalence-gives-PropExt ua

  pe' : Prop-Ext
  pe' {𝓤} = pe 𝓤

 open import DedekindReals.Addition fe' pe' pt
  renaming (_+_ to _+ℝ_) hiding (_-_)
 open import DedekindReals.Order fe' pe' pt
 open import DedekindReals.Type fe' pe' pt
 open import MetricSpaces.StandardDefinition fe' pe' pt

 Metric-Space-Σ-data : compatibility-data {(𝓤 ⊔ 𝓤₁) ⁺}
                        (λ M → Σ d ꞉ (M → M → ℝ) , metric-axioms M d)
                        universes-are-flabby-Σ
 Metric-Space-Σ-data =
  compatibility-data-with-axioms
   universes-are-flabby-Σ
   (graph'-structure ℝ)
   (Graph'-Σ-data ℝ)
   metric-axioms
   metric-axioms-is-prop
   axioms-Σ-data
  where
   σ : (p : Ω 𝓤) (A : p holds → 𝓤 ̇ )
     → ((h : p holds) → graph'-structure ℝ (A h))
     → graph'-structure ℝ (Σ A)
   σ p A = section-map
            (ρ (graph'-structure ℝ) universes-are-flabby-Σ p A)
            (Graph'-Σ-data ℝ p A)

   axioms-Σ-data
    : (p : Ω 𝓤)
      (A : p holds → 𝓤 ̇ )
      (α : (h : p holds) → graph'-structure ℝ (A h))
      (F : (h : p holds) → metric-axioms (A h) (α h))
    → metric-axioms (Σ A) (σ p A α)
   axioms-Σ-data p A α F = I , II , III
    where
     dₚ : {h : p holds} → A h → A h → ℝ
     dₚ {h} = α h

     dₚ-reflexive : {h : p holds} → reflexivity (A h) dₚ
     dₚ-reflexive {h} = pr₁ (F h)

     dₚ-symmetric : {h : p holds} → symmetry (A h) dₚ
     dₚ-symmetric {h} = pr₁ (pr₂ (F h))

     dₚ-triangle-inequality : {h : p holds} → triangle-inequality (A h) dₚ
     dₚ-triangle-inequality {h} = pr₂ (pr₂ (F h))

     i : {h h' : p holds} → h ＝ h'
     i = holds-is-prop p _ _

     τ : {h h' : p holds} → A h → A h'
     τ = transport A i

     d : Σ A → Σ A → ℝ
     d (h₁ , a₁) (h₂ , a₂) = α h₁ (τ a₁) (τ a₂)

     lemma : {h₁ h₂ : p holds} {a₁ : A h₁} {a₂ : A h₂}
             (e₁ : h₂ ＝ h₁) (e₂ : h₁ ＝ h₁)
             (e₃ : h₂ ＝ h₂) (e₄ : h₁ ＝ h₂)
           → α h₁ (transport A e₁ a₂) (transport A e₂ a₁)
             ＝ α h₂ (transport A e₃ a₂) (transport A e₄ a₁)
     lemma {h₁} {h₂} {a₁} {a₂} refl e₂ e₃ e₄ =
      ap₂ (α h₂)
          ((transport-over-prop' (holds-is-prop p) e₃) ⁻¹)
          (ap (λ - → transport A - a₁)
              (props-are-sets (holds-is-prop p) e₂ e₄))

     dₚ-equals-d : {h₁ h₂ : p holds} {a₁ : A h₁} {a₂ : A h₂}
                 → dₚ (τ a₁) (τ a₂) ＝ d (h₁ , a₁) (h₂ , a₂)
     dₚ-equals-d = refl

     dₚ-equals-d-left : {h₁ h₂ : p holds} {a₁ : A h₁} {a₂ : A h₂}
                      → dₚ (τ a₁) a₂ ＝ d (h₁ , a₁) (h₂ , a₂)
     dₚ-equals-d-left = lemma i refl i i

     dₚ-equals-d-right : {h₁ h₂ : p holds} {a₁ : A h₁} {a₂ : A h₂}
                       → dₚ a₁ (τ a₂) ＝ d (h₁ , a₁) (h₂ , a₂)
     dₚ-equals-d-right = lemma refl refl i refl

     _ : σ p A α ＝ d
     _ = refl -- Which is crucial for the proof below to work.

     I : reflexivity (Σ A) (σ p A α)
     I x@(h₁ , a) y@(h₂ , a') = I₁ , I₂
      where
       I₁ : d x y ＝ 0ℝ → x ＝ y
       I₁ e = to-Σ-＝ (i , lr-implication (dₚ-reflexive (τ a) a')
                                          (dₚ-equals-d-left ∙ e))
       I₂ : x ＝ y → d x y ＝ 0ℝ
       I₂ refl = rl-implication (dₚ-reflexive (τ a) (τ a)) refl

     II : symmetry (Σ A) d
     II (h₁ , a₁) (h₂ , a₂) =
      dₚ {h₁} (τ a₁) (τ a₂) ＝⟨ dₚ-symmetric (τ a₁) (τ a₂) ⟩
      dₚ {h₁} (τ a₂) (τ a₁) ＝⟨ lemma i i i i ⟩
      dₚ {h₂} (τ a₂) (τ a₁) ∎

     III : triangle-inequality (Σ A) (σ p A α)
     III x@(h₁ , a₁) y@(h₂ , a₂) z@(h₃ , a₃) = III₂
      where
       III₁ : dₚ {h₂} (τ a₁) a₂ +ℝ dₚ {h₂} a₂ (τ a₃) ≤ℝ dₚ {h₂} (τ a₁) (τ a₃)
       III₁ = dₚ-triangle-inequality (τ a₁) a₂ (τ a₃)
       III₂ : d x y +ℝ d y z ≤ℝ d x z
       III₂ = transport₃ (λ r₁ r₂ r₃ → r₁ +ℝ r₂ ≤ℝ r₃)
              dₚ-equals-d-left dₚ-equals-d-right (lem i i) III₁
        where
         lem : (e₁ : h₁ ＝ h₂) (e₂ : h₃ ＝ h₂)
             → dₚ {h₂} (transport A e₁ a₁) (transport A e₂ a₃)
               ＝ d (h₁ , a₁) (h₃ , a₃)
         lem refl refl = lemma refl refl i i

 ainjectivity-of-Metric-Space
  : ainjective-type (Metric-Space (𝓤₁ ⊔ 𝓤)) (𝓤₁ ⊔ 𝓤) (𝓤₁ ⊔ 𝓤)
 ainjectivity-of-Metric-Space {𝓤} =
  ainjectivity-of-type-of-structures
   (λ M → Σ d ꞉ (M → M → ℝ) , metric-axioms M d)
   universes-are-flabby-Σ
   (Metric-Space-Σ-data {𝓤})

\end{code}

Martin Escardo, 16th August 2023

This file improves InjectiveTypes.MathematicalStructuresMoreGeneral at
the cost of being harder to understand, with the benefit of at the
same time being more general and allowing shorter proofs. It relies on
the file InjectiveTypes.Sigma.

We give a sufficient condition for types of mathematical structures,
such as pointed types, ∞-magmas, monoids, groups, etc. to be
algebraically injective. We use algebraic flabbiness as our main tool.

There is already enough discussion in the files
InjectiveTypes.MathematicalStructure and InjectiveTypes.Sigma, which
we will not repeat here. But we still add some remarks.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

module InjectiveTypes.MathematicalStructuresMoreGeneral (ua : Univalence) where

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
open import Taboos.Decomposability ua
open import UF.Base
open import UF.Equiv
open import UF.ExcludedMiddle
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Sets
open import UF.Sets-Properties
open import UF.SubtypeClassifier

\end{code}

We already know the following, but here is a short direct proof.

\begin{code}

universes-are-aflabby-Π : aflabby (𝓤 ̇ ) 𝓤
universes-are-aflabby-Π {𝓤} P P-is-prop A = Π A , I
 where
  X : 𝓤  ̇
  X = Π A

  I : (p : P) → Π A ＝ A p
  I = λ p → eqtoid (ua 𝓤) (Π A) (A p) (prop-indexed-product fe' P-is-prop p)

universes-are-injective-Π : ainjective-type (𝓤 ̇ ) 𝓤 𝓤
universes-are-injective-Π {𝓤} = aflabby-types-are-ainjective (𝓤 ̇ )
                                  universes-are-aflabby-Π

universes-are-aflabby-Σ : aflabby (𝓤 ̇ ) 𝓤
universes-are-aflabby-Σ {𝓤} P P-is-prop A = Σ A , I
 where
  X : 𝓤  ̇
  X = Σ A

  I : (p : P) → Σ A ＝ A p
  I = λ p → eqtoid (ua 𝓤) (Σ A) (A p) (prop-indexed-sum P-is-prop p)

module _ (S : 𝓤 ̇ → 𝓥 ̇ ) where

 treq : {X Y : 𝓤 ̇ } → X ≃ Y → S X → S Y
 treq {X} {Y} 𝕗 = transport S (eqtoid (ua 𝓤) X Y 𝕗)

\end{code}

We don't need this fact explicitly, but it is worth keeping it in
mind:

\begin{code}

 treq-is-equiv : {X Y : 𝓤 ̇ } (𝕗 : X ≃ Y) → is-equiv (treq 𝕗)
 treq-is-equiv {X} {Y} 𝕗 = transports-are-equivs (eqtoid (ua 𝓤) X Y 𝕗)

\end{code}

We now assume flabbiness data for the universe 𝓤, which later will
choose to be e.g. one of the above two, we record something proved in
InjectiveTypes.Sigma specialized to our situation.

\begin{code}

 module _ (ϕ : aflabby (𝓤 ̇ ) 𝓤) where

  aflabbiness-of-type-of-structured-types : technical-condition S ϕ
                                          → aflabby (Σ S) 𝓤
  aflabbiness-of-type-of-structured-types = Σ-is-aflabby S ϕ


  ainjectivity-of-type-of-structures : technical-condition S ϕ
                                       → ainjective-type (Σ S) 𝓤 𝓤
  ainjectivity-of-type-of-structures = aflabby-types-are-ainjective (Σ S)
                                       ∘ aflabbiness-of-type-of-structured-types

\end{code}

The main additional work in this file on top of InjectiveTypes.Sigma
is to make it easier to work with the technical condition for the
purpose of injectivity of types of mathematical structures.

We work with hypothetical T and T-refl with the following types.

\begin{code}

 module _ (T      : {X Y : 𝓤 ̇ } → (X ≃ Y) → S X → S Y)
          (T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id)
        where

\end{code}

The point is that any such T can be equivalently expressed as a
transport and hence we may apply the above theorem, but it may be
easier to check the technical condition using T rather than transport
(see examples below).

\begin{code}

  T-is-treq : {X Y : 𝓤 ̇ } (𝕗 : X ≃ Y)
            → T 𝕗 ∼ treq 𝕗
  T-is-treq {X} {Y} 𝕗 s = JEq (ua 𝓤) X A I Y 𝕗
   where
    A : (Y : 𝓤 ̇) (𝕗 : X ≃ Y) → 𝓥 ̇
    A Y 𝕗 = T 𝕗 s ＝ treq 𝕗 s

    I : A X (≃-refl X)
    I = T (≃-refl X) s                                ＝⟨ T-refl s ⟩
        s                                             ＝⟨ refl ⟩
        transport S refl s                            ＝⟨ II ⟩
        transport S (eqtoid (ua 𝓤) X X (≃-refl X)) s  ＝⟨ refl ⟩
        treq (≃-refl X) s                             ∎
      where
       II = (ap (λ - → transport S - s) (eqtoid-refl (ua 𝓤) X))⁻¹

\end{code}

We introduce names for the canonical maps induced by Π- and
Σ-flabbiness structure on 𝓤.

\begin{code}

  ρΠ : (p : Ω 𝓤)
       (A : p holds → 𝓤 ̇)
     → S (Π A) → ((h : p holds) → S (A h))
  ρΠ p A s h = T (prop-indexed-product fe' (holds-is-prop p) h) s

  ρΣ : (p : Ω 𝓤)
       (A : p holds → 𝓤 ̇)
     → S (Σ A) → ((h : p holds) → S (A h))
  ρΣ p A s h = T (prop-indexed-sum (holds-is-prop p) h) s

\end{code}

In our applications, we will apply Π-flabbiness structure, and it will
be easier to check technical-condition-Π than technical-condition S
universes-are-aflabby-Π

\begin{code}

  technical-condition-Π : 𝓤 ⁺ ⊔ 𝓥 ̇
  technical-condition-Π = (p : Ω 𝓤)
                          (A : p holds → 𝓤 ̇)
                        → has-section (ρΠ p A)

  Π-lemma : technical-condition-Π
          → technical-condition S universes-are-aflabby-Π
  Π-lemma t p A = II
   where
    π : (p : Ω 𝓤) (A : p holds → 𝓤 ̇) (h : p holds) → Π A ≃ A h
    π p A = prop-indexed-product fe' (holds-is-prop p)

    I : ρΠ p A ∼ ρ S universes-are-aflabby-Π p A
    I s =
     ρΠ p A s                                                    ＝⟨ refl ⟩
     (λ h → T (π p A h) s)                                       ＝⟨ I₀ ⟩
     (λ h → transport S (eqtoid (ua 𝓤) (Π A) (A h) (π p A h)) s) ＝⟨ refl ⟩
          ρ S universes-are-aflabby-Π p A s                      ∎
     where
      I₀ = dfunext fe' (λ h → T-is-treq (π p A h) s)

    II : has-section (ρ S universes-are-aflabby-Π p A)
    II = has-section-closed-under-∼ (ρΠ p A) _ (t p A) (∼-sym I)

\end{code}

We could have proved Π-lemma as follows, but then it wouldn't "compute
enough" for the purposes of e.g. Monoid-Π-condition.

\begin{code}

  Π-lemma' : technical-condition-Π
           → technical-condition S universes-are-aflabby-Π
  Π-lemma' t p A = transport has-section I II
   where
    I : ρΠ p A ＝ ρ S universes-are-aflabby-Π p A
    I = dfunext fe' (λ s →
        dfunext fe' (λ h →
          ap (λ - → - (prop-indexed-product fe' (holds-is-prop p) h) s)
             (dfunext fe' (λ 𝕗 → dfunext fe' (T-is-treq 𝕗)))))

    II : has-section (ρΠ p A)
    II = t p A

  technical-condition-Σ : 𝓤 ⁺ ⊔ 𝓥 ̇
  technical-condition-Σ = (p : Ω 𝓤)
                          (A : p holds → 𝓤 ̇)
                        → has-section (ρΣ p A)

  Σ-lemma : technical-condition-Σ
          → technical-condition S universes-are-aflabby-Σ
  Σ-lemma t p A = transport has-section I II
   where
    I : ρΣ p A ＝ ρ S universes-are-aflabby-Σ p A
    I = dfunext fe' (λ s →
        dfunext fe' (λ h →
          ap (λ - → - (prop-indexed-sum (holds-is-prop p) h) s)
             (dfunext fe' (λ 𝕗 → dfunext fe' (T-is-treq 𝕗)))))

    II : has-section (ρΣ p A)
    II = t p A

\end{code}

Because at the moment we are not applying the Σ-flabbiness structure
of the universe, we haven't bothered to produce a version of Σ-lemma
with better computational properties, but this may be needed in the
future (TODO).

Example. The type of pointed types is algebraically injective. We use
the Π-flabbiness of the universe.

\begin{code}

Pointed-type : (𝓤 : Universe) → 𝓤 ⁺ ̇
Pointed-type 𝓤 = Σ X ꞉ 𝓤 ̇ , X

Pointed : 𝓤 ̇ → 𝓤 ̇
Pointed X = X

Pointed-Π-condition : technical-condition
                       (Pointed {𝓤})
                        universes-are-aflabby-Π
Pointed-Π-condition {𝓤} = Π-lemma Pointed T T-refl c
 where
  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → X → Y
  T = ⌜_⌝

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl x = refl

  c : technical-condition-Π (λ X → X) T T-refl
  c p A = equivs-have-sections id (id-is-equiv (Π A))

ainjectivity-of-type-of-pointed-types : ainjective-type (Pointed-type 𝓤) 𝓤 𝓤
ainjectivity-of-type-of-pointed-types {𝓤} =
 ainjectivity-of-type-of-structures
  Pointed
  universes-are-aflabby-Π
  Pointed-Π-condition

\end{code}

Example. The type of ∞-magmas is algebraically injective. The proof is
an entirely routine application of the above general theorem after we
guess what T should be.

\begin{code}

∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → X)

∞-Magma-structure : 𝓤 ̇ → 𝓤 ̇
∞-Magma-structure = λ X → X → X → X

∞-Magma-structure-Π-condition : technical-condition
                                 (∞-Magma-structure {𝓤})
                                 universes-are-aflabby-Π
∞-Magma-structure-Π-condition {𝓤} =
 Π-lemma S T T-refl ρΠ-has-section
 where
  S = ∞-Magma-structure

  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → S X → S Y
  T 𝕗 _·_ = λ y y' → ⌜ 𝕗 ⌝ (⌜ 𝕗 ⌝⁻¹ y · ⌜ 𝕗 ⌝⁻¹ y')

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl _·_ = dfunext fe' (λ x → dfunext fe' (λ x' → refl))

  module _ (p : Ω 𝓤)
           (A : p holds → 𝓤 ̇)
         where

   π : (h : p holds) → Π A ≃ A h
   π = prop-indexed-product fe' (holds-is-prop p)

   σ : ((h : p holds) → S (A h)) → S (Π A)
   σ g α β h = g h (⌜ π h ⌝ α) (⌜ π h ⌝ β)

   r : S (Π A) → ((h : p holds) → S (A h))
   r = ρΠ S T T-refl p A

   ρσ : r ∘ σ ∼ id
   ρσ g =
    r (σ g)                                                         ＝⟨ refl ⟩
    (λ h a b → g h (⌜ π h ⌝ (⌜ π h ⌝⁻¹ a)) (⌜ π h ⌝ (⌜ π h ⌝⁻¹ b))) ＝⟨ I ⟩
    (λ h a b → g h a b)                                             ＝⟨ refl ⟩
    g                                                               ∎
     where
      I = dfunext fe' (λ h → dfunext fe' (λ a → dfunext fe' (λ b →
           ap₂ (g h)
               (inverses-are-sections' (π h) a)
               (inverses-are-sections' (π h) b))))

   ρΠ-has-section : has-section (ρΠ S T T-refl p A)
   ρΠ-has-section = σ , ρσ

ainjectivity-of-∞-Magma : ainjective-type (∞-Magma 𝓤) 𝓤 𝓤
ainjectivity-of-∞-Magma {𝓤} =
 ainjectivity-of-type-of-structures
  ∞-Magma-structure
  universes-are-aflabby-Π
  ∞-Magma-structure-Π-condition

\end{code}

A corollary is that the type ∞-Magma 𝓤 doesn't have any non-trivial
decidable property unless weak excluded middle holds.

\begin{code}

decomposition-of-∞-Magma-gives-WEM : decomposition (∞-Magma 𝓤) → WEM 𝓤
decomposition-of-∞-Magma-gives-WEM {𝓤} =
 decomposition-of-ainjective-type-gives-WEM
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

∞-Magma∙-structure-Π-condition : technical-condition
                                  (∞-Magma∙-structure {𝓤})
                                  universes-are-aflabby-Π
∞-Magma∙-structure-Π-condition =
 technical-condition-×
  universes-are-aflabby-Π
  ∞-Magma-structure-Π-condition
  Pointed-Π-condition

ainjectivity-of-∞-Magma∙ : ainjective-type (∞-Magma∙ 𝓤) 𝓤 𝓤
ainjectivity-of-∞-Magma∙ {𝓤} =
 ainjectivity-of-type-of-structures
  ∞-Magma∙-structure
  universes-are-aflabby-Π
  ∞-Magma∙-structure-Π-condition

\end{code}

Example. The type of monoids is injective. We just have to check that
the monoid axioms are closed under Π.

\begin{code}

Monoid-Π-condition : technical-condition {𝓤 ⁺}
                      (λ X → Σ s ꞉ monoid-structure X , monoid-axioms X s)
                      universes-are-aflabby-Π
Monoid-Π-condition {𝓤} =
 technical-condition-with-axioms
  universes-are-aflabby-Π
  monoid-structure
  ∞-Magma∙-structure-Π-condition
  monoid-axioms
  (monoid-axioms-is-prop fe')
  axioms-Π-condition
 where
  σ : (p : Ω 𝓤) (A : p holds → 𝓤 ̇)
    → ((h : p holds) → monoid-structure (A h)) → monoid-structure (Π A)
  σ p A = section-of
           (ρ monoid-structure universes-are-aflabby-Π p A)
           (∞-Magma∙-structure-Π-condition p A)

  axioms-Π-condition
    : (p : Ω 𝓤)
      (A : p holds → 𝓤 ̇)
      (α : (h : p holds) → monoid-structure (A h))
      (F : (h : p holds) → monoid-axioms (A h) (α h))
    → monoid-axioms (Π A) (σ p A α)
  axioms-Π-condition p A α F = I , II , III , IV
   where
    _·_ : Π A → Π A → Π A
    f · g = λ h → pr₁ (α h) (f h) (g h)

    e : Π A
    e h = pr₂ (α h)

    σ-remark : σ p A α ＝ (_·_ , e)
    σ-remark = refl

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
  universes-are-aflabby-Π
  Monoid-Π-condition

\end{code}

TODO. It is easy to add further axioms to monoids to get groups, and
then show that the type of groups is injective using the above
technique. I expect this to be entirely routine as the example of
monoids.

TODO. More techniques are needed to show that the type of 1-categories
would be injective. This is more interesting.

NB. The type Ordinal 𝓤 of well-ordered sets in 𝓤 is also injective,
but for a different reason.

TODO. The type of posets should be injective, but with a different
proof. Maybe the proof for the type of ordinals can be adapted (check).

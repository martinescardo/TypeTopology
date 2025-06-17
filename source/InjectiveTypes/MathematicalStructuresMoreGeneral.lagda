Martin Escardo, 16th August 2023

This file improves InjectiveTypes.MathematicalStructures at the cost
of being harder to understand, with the benefit of at the same time
being more general and allowing shorter proofs. It relies on the file
InjectiveTypes.Sigma, which also arises as a generalization of the
original file InjectiveTypes.MathematicalStructures.

We give a sufficient condition for types of mathematical structures,
such as pointed types, ∞-magmas, monoids, groups, etc. to be
algebraically injective. We use algebraic flabbiness as our main tool.

There is already enough discussion in the files
InjectiveTypes.MathematicalStructures and InjectiveTypes.Sigma, which
we will not repeat here. But we include some further remarks.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import UF.Univalence

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

We already know the following, but here is a short direct proof.

\begin{code}

universes-are-aflabby-Π : aflabby (𝓤 ̇ ) 𝓤
universes-are-aflabby-Π {𝓤} P P-is-prop A = Π A , I
 where
  X : 𝓤 ̇
  X = Π A

  I : (p : P) → Π A ＝ A p
  I p = eqtoid (ua 𝓤) (Π A) (A p) (prop-indexed-product p fe' P-is-prop)

universes-are-injective-Π : ainjective-type (𝓤 ̇ ) 𝓤 𝓤
universes-are-injective-Π {𝓤} = aflabby-types-are-ainjective (𝓤 ̇ )
                                  universes-are-aflabby-Π

universes-are-aflabby-Σ : aflabby (𝓤 ̇ ) 𝓤
universes-are-aflabby-Σ {𝓤} P P-is-prop A = Σ A , I
 where
  X : 𝓤 ̇
  X = Σ A

  I : (p : P) → Σ A ＝ A p
  I p = eqtoid (ua 𝓤) (Σ A) (A p) (prop-indexed-sum p P-is-prop)

\end{code}

We now work with an arbitrary notion of structure on 𝓤.

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

We apply this with ϕ taken to be the above canonical Π-flabby
structure on the universe/

Next we want to simplify working with compatibility data, where we
avoid transports by working with the following function treq and
suitable choices of T and T-refl below.

\begin{code}

 treq : {X Y : 𝓤 ̇ } → X ≃ Y → S X → S Y
 treq {X} {Y} 𝕗 = transport S (eqtoid (ua 𝓤) X Y 𝕗)

\end{code}

We don't need the following fact explicitly, but it is worth keeping
it in mind:

\begin{code}

 _ : {X Y : 𝓤 ̇ } (𝕗 : X ≃ Y) → is-equiv (treq 𝕗)
 _ = λ 𝕗 → transports-are-equivs (eqtoid (ua 𝓤) _ _ 𝕗)

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
transport and hence we may apply the theorems of the import file
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
        s                                             ＝⟨ refl ⟩
        transport S refl s                            ＝⟨ II ⟩
        transport S (eqtoid (ua 𝓤) X X (≃-refl X)) s  ＝⟨ refl ⟩
        treq (≃-refl X) s                             ∎
      where
       II = (ap (λ - → transport S - s) (eqtoid-refl (ua 𝓤) X))⁻¹

\end{code}

The following is for the sake of discussion only.

\begin{code}

  module discussion (ϕ : aflabby (𝓤 ̇ ) 𝓤) where

   ⨆ : (p : Ω 𝓤) → (p holds → 𝓤 ̇) → 𝓤 ̇
   ⨆ = aflabby-extension ϕ

   ε : (p : Ω 𝓤)
       (A : p holds → 𝓤 ̇)
       (h : p holds)
     → ⨆ p A ＝ A h
   ε p A h = aflabby-extension-property ϕ p A h

   ρϕ : (p : Ω 𝓤)
        (A : p holds → 𝓤 ̇ )
      → S (⨆ p A) → ((h : p holds) → S (A h))
   ρϕ p A s h = T (idtoeq _ _ (ε p A h)) s

   compatibility-data-ϕ : 𝓤 ⁺ ⊔ 𝓥 ̇
   compatibility-data-ϕ = (p : Ω 𝓤)
                          (A : p holds → 𝓤 ̇ )
                        → has-section (ρϕ p A)

   ϕ-construction : compatibility-data-ϕ
                   → compatibility-data S ϕ
   ϕ-construction t p A = III
    where
     I : (h : p holds) → ⨆ p A ≃ A h
     I h = idtoeq _ _ (ε p A h)

     II : ρϕ p A ∼ ρ S ϕ p A
     II s =
      ρϕ p A s                                        ＝⟨ refl ⟩
      (λ h → T (I h) s)                               ＝⟨ I₀ ⟩
      (λ h → treq (I h) s)                            ＝⟨ refl ⟩
      (λ h → transport S (eqtoid (ua 𝓤) _ _ (I h)) s) ＝⟨ I₁ ⟩
      (λ h → transport S (ε p A h) s)                 ＝⟨ refl ⟩
      ρ S ϕ p A s                                     ∎
      where
       I₀ = dfunext fe' (λ h → T-is-treq (I h) s)
       I₁ = dfunext fe'
              (λ h → ap (λ - → transport S - s)
                        (eqtoid-idtoeq (ua 𝓤) _ _ (ε p A h)))

     III : has-section (ρ S ϕ p A)
     III = has-section-closed-under-∼ (ρϕ p A) _ (t p A) (∼-sym II)

\end{code}

This completes the construction, but we record that the section map



of
the conclusion is literally the same as that of the hypothesis.

\begin{code}

     _ = section-of (ρ S ϕ p A) III  ＝⟨ refl ⟩
         section-of (ρϕ p A) (t p A) ＝⟨ refl ⟩
         pr₁ (t p A)                 ∎

\end{code}

But notice that the above remark is only saying that the section map
is literally the same. It is definitely not saying that the proof that
it is a section is also the same (literally or otherwise).

We can specialize this to the Π and Σ flabbiness structures discussed
above, to get

\begin{code}

  module discussion-Π where

   open discussion universes-are-aflabby-Π

   ρΠ : (p : Ω 𝓤)
        (A : p holds → 𝓤 ̇ )
      → S (Π A) → ((h : p holds) → S (A h))
   ρΠ = ρϕ

   compatibility-data-Π : 𝓤 ⁺ ⊔ 𝓥 ̇
   compatibility-data-Π = (p : Ω 𝓤)
                          (A : p holds → 𝓤 ̇ )
                        → has-section (ρΠ p A)

   Π-construction : compatibility-data-Π
                  → compatibility-data S universes-are-aflabby-Π
   Π-construction = ϕ-construction

  module discussion-Σ where

   open discussion universes-are-aflabby-Σ

   ρΣ : (p : Ω 𝓤)
        (A : p holds → 𝓤 ̇ )
      → S (Σ A) → ((h : p holds) → S (A h))
   ρΣ = ρϕ

   compatibility-data-Σ : 𝓤 ⁺ ⊔ 𝓥 ̇
   compatibility-data-Σ = (p : Ω 𝓤)
                          (A : p holds → 𝓤 ̇ )
                        → has-section (ρΣ p A)

   Σ-construction : compatibility-data-Σ
                  → compatibility-data S universes-are-aflabby-Σ
   Σ-construction = ϕ-construction

\end{code}

However, it is difficult, in practice, work with the above
constructions, as they don't have some further definitional properties
which are useful in practice when constructing examples. For that
purpose, we are interested in ρΠ, which we redefine as follows.

\begin{code}

  ρΠ : (p : Ω 𝓤)
       (A : p holds → 𝓤 ̇ )
     → S (Π A) → ((h : p holds) → S (A h))
  ρΠ p A s h = T I s
   where
    I : Π A ≃ A h
    I = prop-indexed-product h fe' (holds-is-prop p)

  compatibility-data-Π : 𝓤 ⁺ ⊔ 𝓥 ̇
  compatibility-data-Π = (p : Ω 𝓤)
                         (A : p holds → 𝓤 ̇ )
                       → has-section (ρΠ p A)

  Π-construction : compatibility-data-Π
                 → compatibility-data S universes-are-aflabby-Π
  Π-construction t p A = II
   where
    π : (p : Ω 𝓤) (A : p holds → 𝓤 ̇ ) (h : p holds) → Π A ≃ A h
    π p A h = prop-indexed-product h fe' (holds-is-prop p)

    I : ρΠ p A ∼ ρ S universes-are-aflabby-Π p A
    I s =
     ρΠ p A s                                                    ＝⟨ refl ⟩
     (λ h → T (π p A h) s)                                       ＝⟨ I₀ ⟩
     (λ h → transport S (eqtoid (ua 𝓤) (Π A) (A h) (π p A h)) s) ＝⟨ refl ⟩
     ρ S universes-are-aflabby-Π p A s                            ∎
     where
      I₀ = dfunext fe' (λ h → T-is-treq (π p A h) s)

    II : has-section (ρ S universes-are-aflabby-Π p A)
    II = has-section-closed-under-∼ (ρΠ p A) _ (t p A) (∼-sym I)

\end{code}

This completes the construction, and we again remark that we have that
the section of the map

  ρ S universes-are-aflabby-Π p

in the above construction is literally the same as that of the given
section of the map

  ρΠ p A

(although the equation that prove that they are sections may be
different), which is crucial for the examples below.

\begin{code}
{-
    _ : section-of (ρ S universes-are-aflabby-Π p A) II
      ＝ section-of (ρΠ p A) (t p A)
    _ = refl

    _ = ((h : p holds) → S (A h)) → S (Π A)
    _ = section-of (ρΠ p A) (t p A)
-}
\end{code}

But, compared to the above general definition, for examples of S , T
and T-refl of interest, we have two additional definitional
equalities, namely

  remark₁ : ρΠ S T T-refl p A ＝ 𝑖𝑑 (S (Π A))
  remark₁ = refl

  remark₂ : compatibility-data-Π
          ＝ ((p : Ω 𝓤) (A : p holds → 𝓤 ̇ ) → has-section (𝑖𝑑 (S (Π A))))
  remark₂ = refl

which don't hold in general.

Example. The type of pointed types is algebraically injective. We use
the Π-flabbiness of the universe.

\begin{code}

Pointed-type : (𝓤 : Universe) → 𝓤 ⁺ ̇
Pointed-type 𝓤 = Σ X ꞉ 𝓤 ̇ , X

Pointed : 𝓤 ̇ → 𝓤 ̇
Pointed X = X

Pointed-Π-data : compatibility-data (Pointed {𝓤}) universes-are-aflabby-Π
Pointed-Π-data {𝓤} = Π-construction Pointed T T-refl c
 where
  S : 𝓤 ̇ → 𝓤 ̇
  S X = X

  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → X → Y
  T = ⌜_⌝

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl x = refl

  remark₁ : (p : Ω 𝓤) (A : p holds → 𝓤 ̇ ) → ρΠ S T T-refl p A ＝ 𝑖𝑑 (S (Π A))
  remark₁ p A = refl -- (*)

  remark₂ : compatibility-data-Π S T T-refl
          ＝ ((p : Ω 𝓤) (A : p holds → 𝓤 ̇ ) → has-section (𝑖𝑑 (S (Π A))))
  remark₂ = refl -- (*)

  c : compatibility-data-Π S T T-refl
  c p A = equivs-have-sections id (id-is-equiv (Π A))

\end{code}

(*) The above proofs "refl" in the remarks, and hence in c, don't work
    with the alternative Π-construction.

\begin{code}

ainjectivity-of-type-of-pointed-types : ainjective-type (Pointed-type 𝓤) 𝓤 𝓤
ainjectivity-of-type-of-pointed-types {𝓤} =
 ainjectivity-of-type-of-structures
  Pointed
  universes-are-aflabby-Π
  Pointed-Π-data

\end{code}

Example. The type of ∞-magmas is algebraically injective. The proof is
an entirely routine application of the above general theorem after we
guess what T should be.

\begin{code}

∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → X)

∞-Magma-structure : 𝓤 ̇ → 𝓤 ̇
∞-Magma-structure = λ X → X → X → X

∞-Magma-structure-Π-data : compatibility-data
                            (∞-Magma-structure {𝓤})
                            universes-are-aflabby-Π
∞-Magma-structure-Π-data {𝓤} =
 Π-construction S T T-refl ρΠ-has-section
 where
  S = ∞-Magma-structure

  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → S X → S Y
  T 𝕗 _·_ = λ y y' → ⌜ 𝕗 ⌝ (⌜ 𝕗 ⌝⁻¹ y · ⌜ 𝕗 ⌝⁻¹ y')

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl _·_ = dfunext fe' (λ x → dfunext fe' (λ x' → refl))

  module _ (p : Ω 𝓤)
           (A : p holds → 𝓤 ̇ )
         where

   π : (h : p holds) → Π A ≃ A h
   π h = prop-indexed-product h fe' (holds-is-prop p)

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
                                  universes-are-aflabby-Π
∞-Magma∙-structure-Π-data =
 compatibility-data-×
  universes-are-aflabby-Π
  ∞-Magma-structure-Π-data
  Pointed-Π-data

ainjectivity-of-∞-Magma∙ : ainjective-type (∞-Magma∙ 𝓤) 𝓤 𝓤
ainjectivity-of-∞-Magma∙ {𝓤} =
 ainjectivity-of-type-of-structures
  ∞-Magma∙-structure
  universes-are-aflabby-Π
  ∞-Magma∙-structure-Π-data

\end{code}

Example. The type of monoids is injective. We just have to check that
the monoid axioms are closed under Π.

\begin{code}

Monoid-Π-data : compatibility-data {𝓤 ⁺}
                 (λ X → Σ s ꞉ monoid-structure X , monoid-axioms X s)
                 universes-are-aflabby-Π
Monoid-Π-data {𝓤} =
 compatibility-data-with-axioms
  universes-are-aflabby-Π
  monoid-structure
  ∞-Magma∙-structure-Π-data
  monoid-axioms
  (monoid-axioms-is-prop fe')
  axioms-Π-data
 where
  σ : (p : Ω 𝓤) (A : p holds → 𝓤 ̇ )
    → ((h : p holds) → monoid-structure (A h)) → monoid-structure (Π A)
  σ p A = section-of
           (ρ monoid-structure universes-are-aflabby-Π p A)
           (∞-Magma∙-structure-Π-data p A)

  axioms-Π-data
    : (p : Ω 𝓤)
      (A : p holds → 𝓤 ̇ )
      (α : (h : p holds) → monoid-structure (A h))
      (F : (h : p holds) → monoid-axioms (A h) (α h))
    → monoid-axioms (Π A) (σ p A α)
  axioms-Π-data p A α F = I , II , III , IV
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
  Monoid-Π-data

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
proof. Maybe the proof for the type of ordinals can be adapted
(check). What about metric spaces? Notice that both posets and metric
spaces have structure of the form X → X → R where R is
respectively Ω 𝓤 and ℝ.

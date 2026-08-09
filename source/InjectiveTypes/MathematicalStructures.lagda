Martin Escardo, 16th August 2023

We give a sufficient condition for types of mathematical structures,
such as pointed types, ∞-magmas, monoids, groups, etc. to be
algebraically injective. We use algebraic flabbiness as our main tool.

This file is generalized in [1] and [2], but it is still important for
both the sake of motivation and the fact that it includes useful
discussion, which probably should be read before reading [1] and [2].

[1] InjectiveTypes.Sigma
[2] InjectiveTypes.MathematicalStructures

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.Univalence

module InjectiveTypes.MathematicalStructures
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
open import MLTT.Spartan
open import Taboos.Decomposability fe
open import UF.Base
open import UF.Equiv
open import UF.ClassicalLogic
open import UF.PropIndexedPiSigma
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
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
  I p = eqtoid (ua 𝓤) (Π A) (A p) (prop-indexed-product p fe' P-is-prop )

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

We now want to show that several types of mathematical structures are
(algebraically) injective, or, equivalently, (algebraically) flabby.

We work with an arbitrary S : 𝓤 ̇ → 𝓥 ̇ and want to show that Σ S is
flabby. E.g. for ∞-magmas in a universe 𝓤, we will have 𝓥 the same as 𝓤
and S X = X → X → X, specifying that we have a binary operation on the
type X, subject to no axioms, and the type of ∞-magmas will be Σ S.
Similarly, the type of groups will again be of the form Σ S for a
different choice of S.

Let f : P → Σ S be a "partial element" where P is a proposition. Then
f is of the form

 f h = A h , g h

with A : P → 𝓤 ̇ and g : (h : P) → S (A h).

We need to construct a (total) element (X , s) of Σ S, with s : S X ,
such that for all h : P we have that (X , s) = (A h , g h).

In particular, X = A h for any h : P. Because P is a
proposition, we have a fiberwise equivalence

 π : (h : P) → Π A ≃ A h.

By univalence, π induces a fiberwise identification

 ϕ : (h : P) → Π A ＝ A h.

Hence we can take X to be Π A.

To construct s, we need an assumption on S.

Roughly, our assumption is that S is closed under proposition-indexed
products, in the sense that from an element of the type
(h : P) → S (A h) we can get an element of the type S (Π A).

More precisely, we always have a map

 ρ : S (Π A) → ((h : P) → S (A h))

in the opposite direction, and we stipulate that it is an equivalence
for any proposition P and any type family A of types indexed by P.

With this assumption, we can let the element s be the inverse of ρ
applied to B.

Remark. Regarding the discussion in the introduction of this file, it
is actually enough to require that ρ is has a section.

\begin{code}

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

We now define "canonical maps" π, ϕ and ρ parametrized by a
proposition p and family A indexed by p.

\begin{code}

 module canonical-map
         (p : Ω 𝓤)
         (A : p holds → 𝓤 ̇ )
         where

  hp : is-prop (p holds)
  hp = holds-is-prop p

  π : (h : p holds) → Π A ≃ A h
  π h = prop-indexed-product h fe' hp

  remark-π : (h : p holds) (α : Π A)
           → ⌜ π h ⌝ α ＝ α h
  remark-π h α = refl

  remark-π⁻¹ : (h : p holds) (a : A h)
             → ⌜ π h ⌝⁻¹ a ＝ λ h' → transport A (hp h h') a
  remark-π⁻¹ h a = refl

  ϕ : (h : p holds) → Π A ＝ A h
  ϕ h = eqtoid (ua 𝓤) (Π A) (A h) (π h)

  ρ : S (Π A) → ((h : p holds) → S (A h))
  ρ s h = treq (π h) s

  remark-ρ : (s : S (Π A)) (h : p holds)
           → ρ s h ＝ transport S (eqtoid (ua 𝓤) (Π A) (A h) (π h)) s
  remark-ρ s h = refl

\end{code}

Our assumption on S is that the map

  ρ p A : S (Π A) → ((h : p holds) → S (A h))

is an equivalence for every p and A.

\begin{code}

 closed-under-prop-Π : 𝓤 ⁺ ⊔ 𝓥 ̇
 closed-under-prop-Π = (p : Ω 𝓤)
                       (A : p holds → 𝓤 ̇ )
                     → is-equiv (ρ p A)
  where
   open canonical-map

\end{code}

And the main lemma, under this assumption, is that Ρ S is algebraically
flabby with with respect to the universe 𝓤.

\begin{code}

 aflabbiness-of-type-of-structured-types : closed-under-prop-Π
                                         → aflabby (Σ S) 𝓤
 aflabbiness-of-type-of-structured-types ρ-is-equiv = I
  where
   I : aflabby (Σ S) 𝓤
   I P P-is-prop f = (Π A , s) , II
    where
     p : Ω 𝓤
     p = (P , P-is-prop)

     have-f : p holds → Σ S
     have-f = f

     A : p holds → 𝓤 ̇
     A = pr₁ ∘ f

     open canonical-map p A

     e : S (Π A) ≃ ((h : p holds) → S (A h))
     e = ρ , ρ-is-equiv p A

     g : (h : P) → S (A h)
     g = pr₂ ∘ f

     s : S (Π A)
     s = ⌜ e ⌝⁻¹ g

     II : (h : p holds) → Π A , s ＝ f h
     II h = Π A , s   ＝⟨ to-Σ-＝ (ϕ h , III) ⟩
            A h , g h ＝⟨refl⟩
            f h       ∎
      where
       III = transport S (ϕ h) s ＝⟨refl⟩
             ⌜ e ⌝ s h           ＝⟨refl⟩
             ⌜ e ⌝ (⌜ e ⌝⁻¹ g) h ＝⟨ IV ⟩
             g h                 ∎
        where
         IV = ap (λ - → - h) (inverses-are-sections' e g)

\end{code}

It follows that the type Σ S is algebraically injective if S is closed
under proposition-indexed products, which is our main theorem.

\begin{code}

 ainjectivity-of-type-of-structures : closed-under-prop-Π
                                    → ainjective-type (Σ S) 𝓤 𝓤
 ainjectivity-of-type-of-structures = aflabby-types-are-ainjective (Σ S)
                                      ∘ aflabbiness-of-type-of-structured-types

\end{code}

Our assumption of closure under proposition-indexed products may be
difficult to check directly, because it involves transport along an
identification induced by an equivalence by univalence.

In practice, however, we are often able to construct T and T-refl
below, for S of interest, without using transport.

\begin{code}

 module _ (T      : {X Y : 𝓤 ̇ } → (X ≃ Y) → S X → S Y)
          (T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id)
        where

\end{code}

The point is that any such T can be equivalently expressed as a
transport and hence we may apply the above theorem, but it may be
easier to check closure under products using T rather than transport
(see examples below).

\begin{code}

  transport-eqtoid : {X Y : 𝓤 ̇ } (𝕗 : X ≃ Y)
                   → T 𝕗 ∼ treq 𝕗
  transport-eqtoid {X} {Y} 𝕗 s = JEq (ua 𝓤) X A I Y 𝕗
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

Hence our condition on S formulated with transports can be
equivalently formulated with T:

\begin{code}

  module canonical-map'
          (p : Ω 𝓤)
          (A : p holds → 𝓤 ̇ )
          where

   open canonical-map p A public

   τ : S (Π A) → (h : p holds) → S (A h)
   τ s h = T (π h) s

   ρ-and-τ-agree : ρ ∼ τ
   ρ-and-τ-agree s =
    ρ s                                                     ＝⟨refl⟩
    (λ h → transport S (eqtoid (ua 𝓤) (Π A) (A h) (π h)) s) ＝⟨ I ⟩
    (λ h → T (π h) s)                                       ＝⟨refl⟩
    τ s                                                     ∎
    where
     I = dfunext fe' (λ h → (transport-eqtoid (π h) s)⁻¹)

  closed-under-prop-Π' : 𝓤 ⁺ ⊔ 𝓥 ̇
  closed-under-prop-Π' = (p : Ω 𝓤)
                         (A : p holds → 𝓤 ̇ )
                       → is-equiv (τ p A)
   where
    open canonical-map'

  Π-closure-criterion : closed-under-prop-Π'
                      → closed-under-prop-Π
  Π-closure-criterion τ-is-equiv p A =
   equiv-closed-under-∼ τ ρ (τ-is-equiv p A) ρ-and-τ-agree
   where
    open canonical-map' p A

  Π-closure-criterion-converse : closed-under-prop-Π
                               → closed-under-prop-Π'
  Π-closure-criterion-converse ρ-is-equiv p A =
   equiv-closed-under-∼ ρ τ (ρ-is-equiv p A) (∼-sym ρ-and-τ-agree)
   where
    open canonical-map' p A

\end{code}

Example. The type of pointed types is algebraically injective.

\begin{code}

Pointed-type : (𝓤 : Universe) → 𝓤 ⁺ ̇
Pointed-type 𝓤 = Σ X ꞉ 𝓤 ̇ , X

Pointed : 𝓤 ̇ → 𝓤 ̇
Pointed X = X

Pointed-is-closed-under-prop-Π : closed-under-prop-Π (Pointed {𝓤})
Pointed-is-closed-under-prop-Π {𝓤} =
  Π-closure-criterion Pointed T T-refl c
 where
  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → X → Y
  T = ⌜_⌝

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl x = refl

  c : closed-under-prop-Π' Pointed T T-refl
  c p A = id-is-equiv (Π A)

ainjectivity-of-type-of-pointed-types : ainjective-type (Pointed-type 𝓤) 𝓤 𝓤
ainjectivity-of-type-of-pointed-types {𝓤} =
 ainjectivity-of-type-of-structures Pointed Pointed-is-closed-under-prop-Π

\end{code}

Example. The type of ∞-magmas is algebraically injective. The proof is
an entirely routine application of the above general theorem after we
guess what T should be.

\begin{code}

∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → X)

∞-Magma-structure : 𝓤 ̇ → 𝓤 ̇
∞-Magma-structure = λ X → X → X → X

∞-Magma-structure-is-closed-under-prop-Π : closed-under-prop-Π
                                            (∞-Magma-structure {𝓤})
∞-Magma-structure-is-closed-under-prop-Π {𝓤} =
 Π-closure-criterion S T T-refl τ-is-equiv
 where
  S = ∞-Magma-structure

  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → S X → S Y
  T 𝕗 _·_ = λ y y' → ⌜ 𝕗 ⌝ (⌜ 𝕗 ⌝⁻¹ y · ⌜ 𝕗 ⌝⁻¹ y')

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl _·_ = refl

  module _ (p : Ω 𝓤)
           (A : p holds → 𝓤 ̇ )
         where

   open canonical-map' S T T-refl p A

   τ⁻¹ : ((h : p holds) → S (A h)) → S (Π A)
   τ⁻¹ g α β h = g h (⌜ π h ⌝ α) (⌜ π h ⌝ β)

   η : τ⁻¹ ∘ τ ∼ id
   η _·_ = dfunext fe' (λ α → dfunext fe' (I α))
    where
     I : ∀ α β → τ⁻¹ (τ _·_) α β ＝ α · β
     I α β =
      (τ⁻¹ ∘ τ) _·_ α β                                                ＝⟨refl⟩
      (λ h → ⌜ π h ⌝  (⌜ π h ⌝⁻¹ (⌜ π h ⌝ α) · ⌜ π h ⌝⁻¹ (⌜ π h ⌝ β))) ＝⟨ II ⟩
      (λ h → ⌜ π h ⌝ (α · β))                                          ＝⟨refl⟩
      (λ h → (α · β) h)                                                ＝⟨refl⟩
      α · β                                                            ∎
      where
       II = dfunext fe' (λ h →
             ap₂ (λ -₁ -₂ → (-₁ · -₂) h)
                 (inverses-are-retractions' (π h) α)
                 (inverses-are-retractions' (π h) β))

   ε : τ ∘ τ⁻¹ ∼ id
   ε g =
    τ (τ⁻¹ g)                                                       ＝⟨refl⟩
    (λ h a b → g h (⌜ π h ⌝ (⌜ π h ⌝⁻¹ a)) (⌜ π h ⌝ (⌜ π h ⌝⁻¹ b))) ＝⟨ I ⟩
    (λ h a b → g h a b)                                             ＝⟨refl⟩
    g                                                               ∎
     where
      I = dfunext fe' (λ h → dfunext fe' (λ a → dfunext fe' (λ b →
           ap₂ (g h)
               (inverses-are-sections' (π h) a)
               (inverses-are-sections' (π h) b))))

   τ-is-equiv : is-equiv τ
   τ-is-equiv = qinvs-are-equivs τ (τ⁻¹ , η , ε)

ainjectivity-of-∞-Magma : ainjective-type (∞-Magma 𝓤) 𝓤 𝓤
ainjectivity-of-∞-Magma {𝓤} =
 ainjectivity-of-type-of-structures
  ∞-Magma-structure
  ∞-Magma-structure-is-closed-under-prop-Π

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

We now want to consider more examples, such as monoids and groups. For
that purpose, we write combinators, like in UF.SIP, to show that
mathematical structures constructed from standard building blocks,
such as the above, form injective types.

\begin{code}

closure-under-prop-Π-× :
      {𝓤 𝓥₁ 𝓥₂ : Universe}
      {S₁ : 𝓤 ̇ → 𝓥₁ ̇ } {S₂ : 𝓤 ̇ → 𝓥₂ ̇ }
    → closed-under-prop-Π S₁
    → closed-under-prop-Π S₂
    → closed-under-prop-Π (λ X → S₁ X × S₂ X)

closure-under-prop-Π-× {𝓤} {𝓥₁} {𝓥₂} {S₁} {S₂}
                       ρ₁-is-equiv ρ₂-is-equiv = ρ-is-equiv
 where
  S : 𝓤 ̇ → 𝓥₁ ⊔ 𝓥₂ ̇
  S X = S₁ X × S₂ X

  module _ (p : Ω 𝓤)
           (A : p holds → 𝓤 ̇ )
         where

   open canonical-map S  p A using (ρ ; ϕ)
   open canonical-map S₁ p A renaming (ρ to ρ₁) using ()
   open canonical-map S₂ p A renaming (ρ to ρ₂) using ()

   ρ₁⁻¹ : ((h : p holds) → S₁ (A h)) → S₁ (Π A)
   ρ₁⁻¹ = inverse ρ₁ (ρ₁-is-equiv p A)

   ρ₂⁻¹ : ((h : p holds) → S₂ (A h)) → S₂ (Π A)
   ρ₂⁻¹ = inverse ρ₂ (ρ₂-is-equiv p A)

   ρ⁻¹ : ((h : p holds) → S (A h)) → S (Π A)
   ρ⁻¹ α = ρ₁⁻¹ (λ h → pr₁ (α h)) , ρ₂⁻¹ (λ h → pr₂ (α h))

   η : ρ⁻¹ ∘ ρ ∼ id
   η (s₁ , s₂) =
    ρ⁻¹ (ρ (s₁ , s₂))                                         ＝⟨refl⟩
    ρ⁻¹ (λ h → transport S (ϕ h) (s₁ , s₂))                   ＝⟨ I ⟩
    ρ⁻¹ (λ h → transport S₁ (ϕ h) s₁ , transport S₂ (ϕ h) s₂) ＝⟨refl⟩
    ρ₁⁻¹ (ρ₁ s₁) , ρ₂⁻¹ (ρ₂ s₂)                               ＝⟨ II ⟩
    (s₁ , s₂)                                                 ∎
     where
      I  = ap ρ⁻¹ (dfunext fe' (λ h → transport-× S₁ S₂ (ϕ h)))
      II = ap₂ _,_
              (inverses-are-retractions ρ₁ (ρ₁-is-equiv p A) s₁)
              (inverses-are-retractions ρ₂ (ρ₂-is-equiv p A) s₂)

   ε : ρ ∘ ρ⁻¹ ∼ id
   ε α = dfunext fe' I
    where
     α₁ = λ h → pr₁ (α h)
     α₂ = λ h → pr₂ (α h)

     I : ρ (ρ⁻¹ α) ∼ α
     I h =
      ρ (ρ⁻¹ α) h                                                 ＝⟨refl⟩
      transport S (ϕ h) (ρ₁⁻¹ α₁ , ρ₂⁻¹ α₂)                       ＝⟨ II ⟩
      transport S₁ (ϕ h) (ρ₁⁻¹ α₁) , transport S₂ (ϕ h) (ρ₂⁻¹ α₂) ＝⟨refl⟩
      ρ₁ (ρ₁⁻¹ α₁) h , ρ₂ (ρ₂⁻¹ α₂) h                             ＝⟨ III ⟩
      α₁ h , α₂ h                                                 ＝⟨refl⟩
      α h                                                         ∎
       where
        II  = transport-× S₁ S₂ (ϕ h)
        III = ap₂ _,_
                 (ap (λ - → - h)
                     (inverses-are-sections ρ₁ (ρ₁-is-equiv p A) α₁))
                 (ap (λ - → - h)
                     (inverses-are-sections ρ₂ (ρ₂-is-equiv p A) α₂))

   ρ-is-equiv : is-equiv ρ
   ρ-is-equiv = qinvs-are-equivs ρ (ρ⁻¹ , η , ε)

\end{code}

Example. The type of pointed ∞-magmas is injective.

\begin{code}

open import UF.SIP-Examples
open monoid

∞-Magma∙ : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma∙ 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → X) × X

∞-Magma∙-structure : 𝓤 ̇ → 𝓤 ̇
∞-Magma∙-structure = monoid-structure

∞-Magma∙-structure-closed-under-Π : closed-under-prop-Π (∞-Magma∙-structure {𝓤})
∞-Magma∙-structure-closed-under-Π =
 closure-under-prop-Π-×
  ∞-Magma-structure-is-closed-under-prop-Π
  Pointed-is-closed-under-prop-Π

ainjectivity-of-∞-Magma∙ : ainjective-type (∞-Magma∙ 𝓤) 𝓤 𝓤
ainjectivity-of-∞-Magma∙ {𝓤} =
 ainjectivity-of-type-of-structures
  ∞-Magma∙-structure
  ∞-Magma∙-structure-closed-under-Π

\end{code}

We now want to add axioms to e.g. pointed ∞-magmas to get monoids and
conclude that the type of monoids is injective. We use the letter 𝔞 to
range over arbitrary axioms.

\begin{code}

closure-under-prop-Π-with-axioms
 : (S : 𝓤 ̇ → 𝓥 ̇ )
   (ρ-is-equiv : closed-under-prop-Π S)
   (𝔞 : (X : 𝓤 ̇ ) → S X → 𝓦 ̇ )
   (𝔞-is-prop-valued : (X : 𝓤 ̇ ) (s : S X) → is-prop (𝔞 X s))
   (𝔞Π : (p : Ω 𝓤 )
         (A : p holds → 𝓤 ̇ )
       → (α : (h : p holds) → S (A h))
       → ((h : p holds) → 𝔞 (A h) (α h))
       → 𝔞 (Π A) (inverse (canonical-map.ρ S p A) (ρ-is-equiv p A) α))
 → closed-under-prop-Π (λ X → Σ s ꞉ S X , 𝔞 X s)
closure-under-prop-Π-with-axioms
 {𝓤} {𝓥} {𝓦} S ρ-is-equiv 𝔞 𝔞-is-prop-valued 𝔞Π = ρₐ-is-equiv
 where
  Sₐ : 𝓤 ̇ → 𝓥 ⊔ 𝓦 ̇
  Sₐ X = Σ s ꞉ S X , 𝔞 X s

  module _ (p : Ω 𝓤)
           (A : p holds → 𝓤 ̇ )
         where

   open canonical-map S  p A using (ρ ; ϕ)
   open canonical-map Sₐ p A renaming (ρ to ρₐ) using ()

   ρ⁻¹ : ((h : p holds) → S (A h)) → S (Π A)
   ρ⁻¹ = inverse ρ (ρ-is-equiv p A)

   ρₐ⁻¹ : ((h : p holds) → Sₐ (A h)) → Sₐ (Π A)
   ρₐ⁻¹ α = ρ⁻¹ (pr₁ ⊚ α) , 𝔞Π p A (pr₁ ⊚ α) (pr₂ ⊚ α)

   η : ρₐ⁻¹ ∘ ρₐ ∼ id
   η (s , a) =
    ρₐ⁻¹ (ρₐ (s , a))                       ＝⟨refl⟩
    ρₐ⁻¹ (λ h → transport Sₐ (ϕ h) (s , _)) ＝⟨ I ⟩
    ρₐ⁻¹ (λ h → transport S (ϕ h) s , _)    ＝⟨refl⟩
    ρ⁻¹ (λ h → transport S (ϕ h) s) , _     ＝⟨refl⟩
    ρ⁻¹ (ρ s) , _                           ＝⟨ II ⟩
    (s , a)                                 ∎
     where
      I = ap ρₐ⁻¹ (dfunext fe' (λ h → transport-Σ S 𝔞 (A h) (ϕ h) s))
      II = to-subtype-＝
            (𝔞-is-prop-valued (Π A))
            (inverses-are-retractions ρ (ρ-is-equiv p A) s)

   ε : ρₐ ∘ ρₐ⁻¹ ∼ id
   ε α = dfunext fe' I
    where
     α₁ = λ h → pr₁ (α h)
     α₂ = λ (h : p holds) → pr₂ (α h)

     I : ρₐ (ρₐ⁻¹ α) ∼ α
     I h =
      ρₐ (ρₐ⁻¹ α) h                    ＝⟨refl⟩
      ρₐ (ρ⁻¹ α₁ , _) h                ＝⟨refl⟩
      transport Sₐ (ϕ h) (ρ⁻¹ α₁ , _)  ＝⟨ II ⟩
      (transport S (ϕ h) (ρ⁻¹ α₁) , _) ＝⟨refl⟩
      (ρ (ρ⁻¹ α₁) h , _)               ＝⟨ III ⟩
      (α₁ h , α₂ h)                    ＝⟨refl⟩
      α h                              ∎
       where
        II  = transport-Σ S 𝔞 (A h) (ϕ h) (ρ⁻¹ α₁)
        III = to-subtype-＝
               (𝔞-is-prop-valued (A h))
               (ap (λ - → - h) (inverses-are-sections ρ (ρ-is-equiv p A) α₁))

   ρₐ-is-equiv : is-equiv ρₐ
   ρₐ-is-equiv = qinvs-are-equivs ρₐ (ρₐ⁻¹ , η , ε)

\end{code}

The above requires that the structures are closed under
proposition-indexed products with the pointwise operations (where the
operations are specified very abstractly by a structure operator S).
But in many cases of interest, of course, such as monoids and groups,
we have closure under arbitrary products under the pointwise
operations. By the above, the type of any mathematical structure that
is closed under arbitrary products is injective.

Example. The type of monoids is injective. We just have to check that
the monoid axioms are closed under Π.

\begin{code}

Monoid-is-closed-under-prop-Π
 : closed-under-prop-Π {𝓤} (λ X → Σ s ꞉ monoid-structure X , monoid-axioms X s)
Monoid-is-closed-under-prop-Π {𝓤} = V
 where
  open canonical-map monoid-structure

  ρ⁻¹ : (p : Ω 𝓤) (A : p holds → 𝓤 ̇ )
      → ((h : p holds) → monoid-structure (A h)) → monoid-structure (Π A)
  ρ⁻¹ p A = inverse (ρ p A) (∞-Magma∙-structure-closed-under-Π p A)

  axioms-closed-under-prop-Π
    : (p : Ω 𝓤)
      (A : p holds → 𝓤 ̇ )
      (α : (h : p holds) → monoid-structure (A h))
      (F : (h : p holds) → monoid-axioms (A h) (α h))
    → monoid-axioms (Π A) (ρ⁻¹ p A α)
  axioms-closed-under-prop-Π p A α F = I , II , III , IV
   where
    _*_ : {h : p holds} → A h → A h → A h
    _*_ {h} = pr₁ (α h)

    _·_ : Π A → Π A → Π A
    (f · g) h = f h * g h

    e : Π A
    e h = pr₂ (α h)

    ρ⁻¹-remark : ρ⁻¹ p A α ＝ (_·_ , e)
    ρ⁻¹-remark = refl

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

  V : closed-under-prop-Π {𝓤} (λ X → Σ s ꞉ monoid-structure X , monoid-axioms X s)
  V =  closure-under-prop-Π-with-axioms
        monoid-structure
        ∞-Magma∙-structure-closed-under-Π
        monoid-axioms
        (monoid-axioms-is-prop fe')
        axioms-closed-under-prop-Π

ainjectivity-of-Monoid : ainjective-type (Monoid {𝓤}) 𝓤 𝓤
ainjectivity-of-Monoid {𝓤} =
 ainjectivity-of-type-of-structures
  (λ X → Σ s ꞉ monoid-structure X , monoid-axioms X s)
  Monoid-is-closed-under-prop-Π

\end{code}

TODO. It is easy to add further axioms to monoids to get groups, and
then show that the type of groups is injective using the above
technique. I expect this to be entirely routine as the example of
monoids.

This example is implemented by Tom de Jong on 12 January 2026.

\begin{code}

open group

Group-is-closed-under-prop-Π
 : closed-under-prop-Π {𝓤}
    (λ X → Σ ((_·_ , e) , a) ꞉ group-structure X , group-axiom X (_·_ , e))
Group-is-closed-under-prop-Π {𝓤} = III
 where
  open canonical-map group-structure
  ι : {X : 𝓤 ̇ } → group-structure X → monoid-structure X
  ι ((_·_ , e) , a) = (_·_ , e)

  ρ⁻¹ : (p : Ω 𝓤) (A : p holds → 𝓤 ̇ )
      → ((h : p holds) → group-structure (A h)) → group-structure (Π A)
  ρ⁻¹ p A = inverse (ρ p A) (Monoid-is-closed-under-prop-Π p A)

  axiom-closed-under-prop-Π
    : (p : Ω 𝓤)
      (A : p holds → 𝓤 ̇ )
      (α : (h : p holds) → group-structure (A h))
      (F : (h : p holds) → group-axiom (A h) (ι (α h)))
    → group-axiom (Π A) (ι (ρ⁻¹ p A α))
  axiom-closed-under-prop-Π p A α F f = f⁻¹ , I , II
   where
    _∗_ : {h : p holds} → A h → A h → A h
    _∗_ {h} = pr₁ (ι (α h))

    _·_ : Π A → Π A → Π A
    (f · g) h = f h ∗ g h

    e : {h : p holds} → A h
    e {h} = pr₂ (ι (α h))

    𝕖 : Π A
    𝕖 h = e

    inver : {h : p holds} → A h → A h
    inver {h} x = pr₁ (F h x)

    right-inver : {h : p holds} (x : A h) → x ∗ inver x ＝ e
    right-inver {h} x = pr₁ (pr₂ (F h x))

    left-inver : {h : p holds} (x : A h) → inver x ∗ x ＝ e
    left-inver {h} x = pr₂ (pr₂ (F h x))

    f⁻¹ : Π A
    f⁻¹ h = inver (f h)

    I : f · f⁻¹ ＝ 𝕖
    I = dfunext fe' (λ h → right-inver (f h))

    II : f⁻¹ · f ＝ 𝕖
    II = dfunext fe' (λ h → left-inver (f h))

  III : closed-under-prop-Π {𝓤} (λ X → Σ s ꞉ group-structure X , group-axiom X (ι s))
  III =  closure-under-prop-Π-with-axioms
          group-structure
          Monoid-is-closed-under-prop-Π
          (λ X s → group-axiom X (ι s))
          (group-axiom-is-prop fe')
          axiom-closed-under-prop-Π

ainjectivity-of-Group : ainjective-type (Group {𝓤}) 𝓤 𝓤
ainjectivity-of-Group =
 ainjectivity-of-type-of-structures
  (λ X → Σ ((_·_ , e) , a) ꞉ group-structure X , group-axiom X ((_·_ , e)))
  Group-is-closed-under-prop-Π

\end{code}

TODO. More techniques are needed to show that the type of 1-categories
would be injective. This is more interesting.

NB. The type Ordinal 𝓤 of well-ordered sets in 𝓤 is also injective,
but for a different reason.

TODO. The type of posets should be injective, but with a different
proof. Maybe the proof for the type of ordinals can be adapted
(check). This is solved in the file MathematicalStructuresMoreGeneral.

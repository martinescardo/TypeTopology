Martin Escardo, 16th August 2023

We give conditions for types of mathematical structures, such as
pointed types, ∞-magmas, monoids and groups to be algebraically
injective. We use algebraic flabbiness as our main tool.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --lossy-unification #-}

open import UF.Univalence

module InjectiveTypes.MathematicalStructures (ua : Univalence) where

open import UF.FunExt
open import UF.UA-FunExt

private
 fe : FunExt
 fe = Univalence-gives-FunExt ua

 fe' : Fun-Ext
 fe' {𝓤} {𝓥} = fe 𝓤 𝓥

open import InjectiveTypes.Blackboard fe
open import MLTT.Spartan
open import Taboos.Decomposability ua
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.ExcludedMiddle
open import UF.PropIndexedPiSigma
open import UF.Size
open import UF.Subsingletons

\end{code}

We already know the following, but here is a short direct proof.

\begin{code}

universes-are-flabby-Π : aflabby (𝓤 ̇ ) 𝓤
universes-are-flabby-Π {𝓤} P P-is-prop A = Π A , I
 where
  X : 𝓤  ̇
  X = Π A

  I : (p : P) → Π A ＝ A p
  I = λ p → eqtoid (ua 𝓤) (Π A) (A p) (prop-indexed-product fe' P-is-prop p)

universes-are-injective-Π : ainjective-type (𝓤 ̇ ) 𝓤 𝓤
universes-are-injective-Π {𝓤} = aflabby-types-are-ainjective (𝓤 ̇ )
                                  universes-are-flabby-Π

\end{code}

We now want to show that several types of mathematical structures are
(algebraically) injective, or, equivalently, (algebraically) flabby.

We work with an arbitrary S : 𝓤 ̇ → 𝓥 ̇ and want to show that Σ S is
flabby.

Let f : P → Σ S be a "partial element" where P is a proposition. Then
f is of the form

 f h = A h , g h

with A : P → 𝓤 ̇ and g : (h : P) → S (A h).

We need to construct a (total) element (X , s) of Σ S, with s : S X ,
such that for all h : P we have that (X , s) = (A h , g h).

This forces X = A h for any h : P. We have an equivalence

 π : (h : P) → Π A ≃ A h

By, univalence, π induces a fiberwise identification

 ϕ : (h : P) → Π A ＝ A h.

Hence we can take X to be Π A.

To construct s, we need an assumption on S.

Roughly, our assumption is that S is closed under prop-indexed
products, in the sense that from an element of the type
(h : P) → S (A h) we can get an element of the type S (Π A).

More precisely, we always have a map

 σ : S (Π A) → ((h : P) → S (A h))

in the opposite direction. We stipulate that it is an equivalence for
any proposition P and any type family A : P → 𝓤 ̇.

With this assumption, we can let s be the inverse of σ applied to g.

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

We now define auxiliary functions π, ϕ and σ parametrized by a
proposition p and family A indexed by p.

Because we deliberately use short, general purpose symbols, we place
these definitions in a module that needs to be opened when we want to
use this notation.

\begin{code}

 module notation
         (p : Ω 𝓤)
         (A : p holds → 𝓤 ̇)
         where

  hp : is-prop (p holds)
  hp = holds-is-prop p

  π : (h : p holds) → Π A ≃ A h
  π = prop-indexed-product fe' hp

  remark₀ : (h : p holds) (α : Π A) → ⌜ π h ⌝ α ＝ α h
  remark₀ h α = refl

  ϕ : (h : p holds) → Π A ＝ A h
  ϕ h = eqtoid (ua 𝓤) (Π A) (A h) (π h)

  σ : S (Π A) → ((h : p holds) → S (A h))
  σ s h = treq (π h) s

  remark₁ : (s : S (Π A)) (h : p holds)
          → σ s h ＝ transport S (eqtoid (ua 𝓤) (Π A) (A h) (π h)) s
  remark₁ s h = refl

\end{code}

Our assumption on S is that the map

  σ p A : S (Π A) → ((h : p holds) → S (A h))

is an equivalence for every p and A.

\begin{code}

 closed-under-prop-Π : 𝓤 ⁺ ⊔ 𝓥 ̇
 closed-under-prop-Π = (p : Ω 𝓤)
                       (A : p holds → 𝓤 ̇)
                      → is-equiv (σ p A)
  where
   open notation

\end{code}

And the main lemma, under this assumption, is that Σ S is algebraically
flabby with with respect to the universe 𝓤.

\begin{code}

 aflabbiness-of-type-of-structures : closed-under-prop-Π
                                   → aflabby (Σ S) 𝓤
 aflabbiness-of-type-of-structures σ-is-equiv = I
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

     open notation p A

     e : S (Π A) ≃ ((h : p holds) → S (A h))
     e = σ , σ-is-equiv p A

     g : (h : P) → S (A h)
     g = pr₂ ∘ f

     s : S (Π A)
     s = ⌜ e ⌝⁻¹ g

     II : (h : p holds) → Π A , s ＝ f h
     II h = Π A , s   ＝⟨ to-Σ-＝ (ϕ h , III) ⟩
            A h , g h ＝⟨ refl ⟩
            f h       ∎
      where
       III = transport S (ϕ h) s ＝⟨ refl ⟩
             ⌜ e ⌝ s h           ＝⟨ refl ⟩
             ⌜ e ⌝ (⌜ e ⌝⁻¹ g) h ＝⟨ IV ⟩
             g h ∎
        where
         IV = ap (λ - → - h) (inverses-are-sections ⌜ e ⌝ ⌜ e ⌝-is-equiv g)

\end{code}

It follows that the type Σ S is algebraically injective if S is closed
under prop-indexed products, which is our main theorem.

\begin{code}

 ainjectivity-of-type-of-structures : closed-under-prop-Π
                                    → ainjective-type (Σ S) 𝓤 𝓤
 ainjectivity-of-type-of-structures = aflabby-types-are-ainjective (Σ S)
                                      ∘ aflabbiness-of-type-of-structures

\end{code}

Our assumption of closure under prop-indexed products may be difficult
to check directly, because it involves transport along an
identification induced by an equivalence by univalence.

In practice, we are often able to construct T and T-refl below, for S
of interest, without using transport.

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
                   → T 𝕗 ∼ transport S (eqtoid (ua 𝓤) X Y 𝕗)
  transport-eqtoid {X} {Y} 𝕗 s = JEq (ua 𝓤) X A I Y 𝕗
   where
    A : (Y : 𝓤 ̇) (𝕗 : X ≃ Y) → 𝓥 ̇
    A Y 𝕗 = T 𝕗 s ＝ transport S (eqtoid (ua 𝓤) X Y 𝕗) s

    I : A X (≃-refl X)
    I = T (≃-refl X) s                                ＝⟨ II ⟩
        s                                             ＝⟨ refl ⟩
        transport S refl s                            ＝⟨ III ⟩
        transport S (eqtoid (ua 𝓤) X X (≃-refl X)) s  ∎
      where
       II   = T-refl s
       III  = (ap (λ - → transport S - s) (eqtoid-refl (ua 𝓤) X))⁻¹

\end{code}

Hence our condition on S formulated with transports can be
equivalently formulated with T:

\begin{code}

  module notation'
          (p : Ω 𝓤)
          (A : p holds → 𝓤 ̇)
          where

   open notation p A public

   τ : S (Π A) → (h : p holds) → S (A h)
   τ s h = T (π h) s

   σ-and-τ-agree : σ ∼ τ
   σ-and-τ-agree s =
    σ s                                                       ＝⟨ refl ⟩
    ((λ h → transport S (eqtoid (ua 𝓤) (Π A) (A h) (π h)) s)) ＝⟨ I ⟩
    (λ h → T (π h) s)                                         ＝⟨ refl ⟩
    τ s                                                       ∎
    where
     I = dfunext fe' (λ h → (transport-eqtoid (π h) s)⁻¹)

  closed-under-prop-Π' : 𝓤 ⁺ ⊔ 𝓥 ̇
  closed-under-prop-Π' = (p : Ω 𝓤)
                         (A : p holds → 𝓤 ̇)
                       → is-equiv (τ p A)
   where
    open notation'

  Π-closure-criterion : closed-under-prop-Π'
                      → closed-under-prop-Π
  Π-closure-criterion τ-is-equiv p A =
   equiv-closed-under-∼ (τ p A) (σ p A) (τ-is-equiv p A) (σ-and-τ-agree p A)
   where
    open notation'

  Π-closure-criterion-converse : closed-under-prop-Π
                               → closed-under-prop-Π'
  Π-closure-criterion-converse σ-is-equiv p A =
   equiv-closed-under-∼ (σ p A) (τ p A) (σ-is-equiv p A) (∼-sym (σ-and-τ-agree p A))
   where
    open notation'

\end{code}

Example: The type of pointed types is algebraically injective.

\begin{code}

Pointed-Type : (𝓤 : Universe) → 𝓤 ⁺ ̇
Pointed-Type 𝓤 = Σ X ꞉ 𝓤 ̇ , X

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

ainjectivity-of-type-of-pointed-types : ainjective-type (Pointed-Type 𝓤) 𝓤 𝓤
ainjectivity-of-type-of-pointed-types {𝓤} =
 ainjectivity-of-type-of-structures Pointed Pointed-is-closed-under-prop-Π

\end{code}

Example: The type of ∞-magmas is algebraically injective. The proof is
a bit long, but it is an entirely routine application of the above
general theorem.

\begin{code}

∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → X)

∞-Magma-structure : 𝓤 ̇ → 𝓤 ̇
∞-Magma-structure X = X → X → X

∞-Magma-structure-is-closed-under-prop-Π : closed-under-prop-Π (∞-Magma-structure {𝓤})
∞-Magma-structure-is-closed-under-prop-Π {𝓤} =
 Π-closure-criterion S T T-refl τ-is-equiv
 where
  S = ∞-Magma-structure

  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → S X → S Y
  T 𝕗 _·_ = λ y y' → ⌜ 𝕗 ⌝ (⌜ 𝕗 ⌝⁻¹ y · ⌜ 𝕗 ⌝⁻¹ y')

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl _·_ = dfunext fe' (λ x → dfunext fe' (λ x' → refl))

  module _ (p : Ω 𝓤)
           (A : p holds → 𝓤 ̇)
         where

   open notation' S T T-refl p A

   τ⁻¹ : ((h : p holds) → S (A h)) → S (Π A)
   τ⁻¹ g α β h = g h (⌜ π h ⌝ α) (⌜ π h ⌝ β)

   η : τ⁻¹ ∘ τ ∼ id
   η _·_ = dfunext fe' (λ α → dfunext fe' (I α))
    where
     I : ∀ α β → τ⁻¹ (τ _·_) α β ＝ α · β
     I α β =
      (τ⁻¹ ∘ τ) _·_ α β                                                ＝⟨ refl ⟩
      (λ h → ⌜ π h ⌝  (⌜ π h ⌝⁻¹ (⌜ π h ⌝ α) · ⌜ π h ⌝⁻¹ (⌜ π h ⌝ β))) ＝⟨ II ⟩
      (λ h → ⌜ π h ⌝ (α · β))                                          ＝⟨ refl ⟩
      (λ h → (α · β) h)                                                ＝⟨ refl ⟩
      α · β                                                            ∎
      where
       II = dfunext fe' (λ h →
             ap₂ (λ -₁ -₂ → (-₁ · -₂) h)
                 (inverses-are-retractions (⌜ π h ⌝) ⌜ π h ⌝-is-equiv α)
                 (inverses-are-retractions (⌜ π h ⌝) ⌜ π h ⌝-is-equiv β))

   ε : τ ∘ τ⁻¹ ∼ id
   ε g =
    τ (τ⁻¹ g)                                                     ＝⟨ refl ⟩
    (λ h a b → g h (⌜ π h ⌝ (⌜ π h ⌝⁻¹ a)) (⌜ π h ⌝ (⌜ π h ⌝⁻¹ b))) ＝⟨ I ⟩
    (λ h a b → g h a b)                                             ＝⟨ refl ⟩
    g                                                               ∎
     where
      I = dfunext fe' (λ h → dfunext fe' (λ a → dfunext fe' (λ b →
           ap₂ (g h)
               (inverses-are-sections (⌜ π h ⌝) ⌜ π h ⌝-is-equiv a)
               (inverses-are-sections (⌜ π h ⌝) ⌜ π h ⌝-is-equiv b))))

   τ-is-equiv : is-equiv τ
   τ-is-equiv = qinvs-are-equivs τ  (τ⁻¹ , η , ε)

ainjectivity-of-∞-Magma : ainjective-type (∞-Magma 𝓤) 𝓤 𝓤
ainjectivity-of-∞-Magma {𝓤} =
 ainjectivity-of-type-of-structures
  ∞-Magma-structure
  ∞-Magma-structure-is-closed-under-prop-Π

\end{code}

A corollary is that the type ∞-Magma 𝓤 doesn't have any decidable
property unless weak excluded middle holds.

\begin{code}

decomposition-of-∞-Magma-gives-WEM : decomposition (∞-Magma 𝓤) → WEM 𝓤
decomposition-of-∞-Magma-gives-WEM {𝓤} =
 decomposition-of-ainjective-type-gives-WEM
  (∞-Magma 𝓤)
  ainjectivity-of-∞-Magma

\end{code}

The same is true for the type of pointed types, of course.

We now want to consider more examples, such as monoids, groups and
1-categories. For that purpose, write combinators, like in UF.SIP, to
show that mathematical structures constructed from standard building
blocks, such as the above, form injective types.

\begin{code}

variable
 𝓥₁ 𝓥₂ : Universe

closed-under-prop-Π-× :
      {S₁ : 𝓤 ̇ → 𝓥₁ ̇ } {S₂ : 𝓤 ̇ → 𝓥₂ ̇ }
    → closed-under-prop-Π S₁
    → closed-under-prop-Π S₂
    → closed-under-prop-Π (λ X → S₁ X × S₂ X)

closed-under-prop-Π-× {𝓤} {𝓥₁} {𝓥₂} {S₁} {S₂} σ₁-is-equiv σ₂-is-equiv = σ-is-equiv
 where
  S : 𝓤 ̇ → 𝓥₁ ⊔ 𝓥₂ ̇
  S X = S₁ X × S₂ X

  module _ (p : Ω 𝓤)
           (A : p holds → 𝓤 ̇)
         where

   open notation S  p A using (σ ; ϕ)
   open notation S₁ p A renaming (σ to σ₁) using ()
   open notation S₂ p A renaming (σ to σ₂) using ()

   σ₁⁻¹ : ((h : p holds) → S₁ (A h)) → S₁ (Π A)
   σ₁⁻¹ = inverse σ₁ (σ₁-is-equiv p A)

   σ₂⁻¹ : ((h : p holds) → S₂ (A h)) → S₂ (Π A)
   σ₂⁻¹ = inverse σ₂ (σ₂-is-equiv p A)

   σ⁻¹ : ((h : p holds) → S (A h)) → S (Π A)
   σ⁻¹ α = σ₁⁻¹ (λ h → pr₁ (α h)) , σ₂⁻¹ (λ h → pr₂ (α h))

   η : σ⁻¹ ∘ σ ∼ id
   η (s₁ , s₂) =
    σ⁻¹ (σ (s₁ , s₂))                                         ＝⟨ refl ⟩
    σ⁻¹ (λ h → transport S (ϕ h) (s₁ , s₂))                   ＝⟨ I ⟩
    σ⁻¹ (λ h → transport S₁ (ϕ h) s₁ , transport S₂ (ϕ h) s₂) ＝⟨ refl ⟩
    σ₁⁻¹ (σ₁ s₁) , σ₂⁻¹ (σ₂ s₂)                               ＝⟨ II ⟩
    (s₁ , s₂)                                                 ∎
     where
      I  = ap σ⁻¹ (dfunext fe' (λ h → transport-× S₁ S₂ (ϕ h)))
      II = ap₂ _,_
              (inverses-are-retractions σ₁ (σ₁-is-equiv p A) s₁)
              (inverses-are-retractions σ₂ (σ₂-is-equiv p A) s₂)

   ε : σ ∘ σ⁻¹ ∼ id
   ε α = dfunext fe' I
    where
     α₁ = λ h → pr₁ (α h)
     α₂ = λ h → pr₂ (α h)

     I : σ (σ⁻¹ α) ∼ α
     I h =
      σ (σ⁻¹ α) h                                                 ＝⟨ refl ⟩
      transport S (ϕ h) (σ₁⁻¹ α₁ , σ₂⁻¹ α₂)                       ＝⟨ II ⟩
      transport S₁ (ϕ h) (σ₁⁻¹ α₁) , transport S₂ (ϕ h) (σ₂⁻¹ α₂) ＝⟨ refl ⟩
      σ₁ (σ₁⁻¹ α₁) h , σ₂ (σ₂⁻¹ α₂) h                             ＝⟨ III ⟩
      α₁ h , α₂ h                                                 ＝⟨ refl ⟩
      α h                                                         ∎
       where
        II  = transport-× S₁ S₂ (ϕ h)
        III = ap₂ _,_
                 (ap (λ - → - h)
                     (inverses-are-sections σ₁ (σ₁-is-equiv p A) α₁))
                 (ap (λ - → - h)
                     (inverses-are-sections σ₂ (σ₂-is-equiv p A) α₂))

   σ-is-equiv : is-equiv σ
   σ-is-equiv = qinvs-are-equivs σ (σ⁻¹ , η , ε)

\end{code}

Example. The type of pointed ∞-magmas is injective.

\begin{code}

∞-Magma∙ : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma∙ 𝓤 = Σ X ꞉ 𝓤 ̇ , X × (X → X → X)

ainjectivity-of-∞-Magma∙ : ainjective-type (∞-Magma∙ 𝓤) 𝓤 𝓤
ainjectivity-of-∞-Magma∙ {𝓤} =
 ainjectivity-of-type-of-structures
  (λ X → X × (X → X → X))
  (closed-under-prop-Π-×
    Pointed-is-closed-under-prop-Π
    ∞-Magma-structure-is-closed-under-prop-Π)

\end{code}

To to be continued with more "combinators" and examples.

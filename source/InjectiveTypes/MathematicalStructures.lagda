Martin Escardo, 16th August 2023

We give conditions for types of mathematical structures, such as
pointed types, ∞-magmas, monoids and groups to be algebraically
injective. We use algebraic flabbiness as our main tool.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split  #-}

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

 τ : S (Π A) → ((h : P) → S (A h))

in the opposite direction. We stipulate that it is an equivalence for
any proposition P and any type family A : P → 𝓤 ̇.

With this assumption, we can let s be the inverse of τ applied to g.

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

We now define auxiliary functions π, ϕ and τ parametrized by a
proposition p and family A indexed by p.

Because we deliberately use short, general purpose symbols, we place
these definitions in a module that needs to be opened when we want to
use this notation.

\begin{code}

 module notation₁
         (p : Ω 𝓤)
         (A : p holds → 𝓤 ̇)
         where

  hp : is-prop (p holds)
  hp = holds-is-prop p

  π : (h : p holds) → Π A ≃ A h
  π = prop-indexed-product fe' hp

  private
   remark : (h : p holds) (α : Π A) → ⌜ π h ⌝ α ＝ α h
   remark h α = refl

  ϕ : (h : p holds) → Π A ＝ A h
  ϕ h = eqtoid (ua 𝓤) (Π A) (A h) (π h)

  τ : S (Π A) → ((h : p holds) → S (A h))
  τ s h = treq (π h) s

\end{code}

Our assumption on S is that the map

  τ p A : S (Π A) → ((h : p holds) → S (A h))

is an equivalence for every p and A.

\begin{code}

 structure-closed-under-prop-indexed-products : 𝓤 ⁺ ⊔ 𝓥 ̇
 structure-closed-under-prop-indexed-products = (p : Ω 𝓤)
                                                 (A : p holds → 𝓤 ̇)
                                               → is-equiv (τ p A)
  where
   open notation₁

\end{code}

And the main lemma, under this assumption, is that Σ S is algebraically
flabby with with respect to the universe 𝓤.

\begin{code}

 aflabbiness-of-type-of-structures : structure-closed-under-prop-indexed-products
                                   → aflabby (Σ S) 𝓤
 aflabbiness-of-type-of-structures τ-is-equiv = I
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

     open notation₁ p A

     t : S (Π A) ≃ ((h : p holds) → S (A h))
     t = τ , τ-is-equiv p A

     g : (h : P) → S (A h)
     g = pr₂ ∘ f

     s : S (Π A)
     s = ⌜ t ⌝⁻¹ g

     II : (h : p holds) → Π A , s ＝ f h
     II h = Π A , s   ＝⟨ to-Σ-＝ (ϕ h , III) ⟩
            A h , g h ＝⟨ refl ⟩
            f h       ∎
      where
       III = transport S (ϕ h) s ＝⟨ refl ⟩
             ⌜ t ⌝ s h           ＝⟨ refl ⟩
             ⌜ t ⌝ (⌜ t ⌝⁻¹ g) h ＝⟨ IV ⟩
             g h ∎
        where
         IV = ap (λ - → - h) (inverses-are-sections ⌜ t ⌝ ⌜ t ⌝-is-equiv g)

\end{code}

It follows that the type Σ S is algebraically injective if S is closed
under prop-indexed products, which is our main theorem.

\begin{code}

 ainjectivity-of-type-of-structures : structure-closed-under-prop-indexed-products
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

 module _ (T : {X Y : 𝓤 ̇ } → (X ≃ Y) → S X → S Y)
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

Hence our condition on S formulated with transports can be formulated
with T instead:

\begin{code}

  module notation₂
          (p : Ω 𝓤)
          (A : p holds → 𝓤 ̇)
          where

   open notation₁ p A public

   τ' : S (Π A) → (h : p holds) → S (A h)
   τ' s h = T (π h) s

  structure-closed-under-prop-indexed-products' : 𝓤 ⁺ ⊔ 𝓥 ̇
  structure-closed-under-prop-indexed-products' = (p : Ω 𝓤)
                                                  (A : p holds → 𝓤 ̇)
                                                → is-equiv (τ' p A)
   where
    open notation₂

  aflabbiness-of-type-of-structures' : structure-closed-under-prop-indexed-products'
                                     → aflabby (Σ S) 𝓤
  aflabbiness-of-type-of-structures' τ'-is-equiv =
   aflabbiness-of-type-of-structures
    (λ p A → equiv-closed-under-∼ (τ' p A) (τ p A) (τ'-is-equiv p A) (I p A))
   where
    open notation₂

    I : (p : Ω 𝓤) (A : p holds → 𝓤 ̇) →  τ p A ∼ τ' p A
    I p A s =
     τ p A s                                                       ＝⟨ refl ⟩
     ((λ h → transport S (eqtoid (ua 𝓤) (Π A) (A h) (π p A h)) s)) ＝⟨ II ⟩
     (λ h → T (π p A h) s)                                         ＝⟨ refl ⟩
     τ' p A s                                                      ∎
     where
      II = dfunext fe' (λ h → (transport-eqtoid (π p A h) s)⁻¹)

  injectivity-of-type-of-structures' : structure-closed-under-prop-indexed-products'
                                     → ainjective-type (Σ S) 𝓤 𝓤
  injectivity-of-type-of-structures' = aflabby-types-are-ainjective (Σ S)
                                        ∘ aflabbiness-of-type-of-structures'

\end{code}

Example: The type of pointed types is algebraically injective.

\begin{code}

ainjectivity-of-type-of-pointed-types : ainjective-type (Σ X ꞉ 𝓤 ̇ , X) 𝓤 𝓤
ainjectivity-of-type-of-pointed-types {𝓤} =
 injectivity-of-type-of-structures'
   (λ X → X)
   ⌜_⌝
   (λ x → refl)
   (λ p A → id-is-equiv (Π A))

\end{code}

Example: The type of ∞-magmas is algebraically injective. The proof is
a bit long, but it is an entirely routine application of the above
general theorem.

\begin{code}

∞-Magma : (𝓤 : Universe) → 𝓤 ⁺ ̇
∞-Magma 𝓤 = Σ X ꞉ 𝓤 ̇ , (X → X → X)

ainjectivity-of-∞-Magma : ainjective-type (∞-Magma 𝓤) 𝓤 𝓤
ainjectivity-of-∞-Magma {𝓤} =
 injectivity-of-type-of-structures' S T T-refl τ'-is-equiv
 where
  S : 𝓤 ̇ → 𝓤 ̇
  S X = X → X → X

  T : {X Y : 𝓤 ̇ } → (X ≃ Y) → S X → S Y
  T 𝕗 _·_ = λ y y' → ⌜ 𝕗 ⌝ (⌜ 𝕗 ⌝⁻¹ y · ⌜ 𝕗 ⌝⁻¹ y')

  T-refl : {X : 𝓤 ̇ } → T (≃-refl X) ∼ id
  T-refl _·_ = dfunext fe' (λ x → dfunext fe' (λ x' → refl))

  module _ (p : Ω 𝓤)
           (A : p holds → 𝓤 ̇)
         where

   open notation₂ S T T-refl p A

   τ'⁻¹ : ((h : p holds) → S (A h)) → S (Π A)
   τ'⁻¹ g α β h = g h (⌜ π h ⌝ α) (⌜ π h ⌝ β)

   η : τ'⁻¹ ∘ τ' ∼ id
   η _·_ = dfunext fe' (λ α → dfunext fe' (I α))
    where
     I : ∀ α β → τ'⁻¹ (τ' _·_) α β ＝ α · β
     I α β =
      (τ'⁻¹ ∘ τ') _·_ α β                                              ＝⟨ refl ⟩
      (λ h → ⌜ π h ⌝  (⌜ π h ⌝⁻¹ (⌜ π h ⌝ α) · ⌜ π h ⌝⁻¹ (⌜ π h ⌝ β))) ＝⟨ II ⟩
      (λ h → ⌜ π h ⌝ (α · β))                                          ＝⟨ refl ⟩
      (λ h → (α · β) h)                                                ＝⟨ refl ⟩
      α · β                                                            ∎
      where
       II = dfunext fe' (λ h →
             ap₂ (λ -₁ -₂ → (-₁ · -₂) h)
                 (inverses-are-retractions (⌜ π h ⌝) ⌜ π h ⌝-is-equiv α)
                 (inverses-are-retractions (⌜ π h ⌝) ⌜ π h ⌝-is-equiv β))

   ε : τ' ∘ τ'⁻¹ ∼ id
   ε g =
    τ' (τ'⁻¹ g)                                                     ＝⟨ refl ⟩
    (λ h a b → g h (⌜ π h ⌝ (⌜ π h ⌝⁻¹ a)) (⌜ π h ⌝ (⌜ π h ⌝⁻¹ b))) ＝⟨ I ⟩
    (λ h a b → g h a b)                                             ＝⟨ refl ⟩
    g                                                               ∎
     where
      I = dfunext fe' (λ h → dfunext fe' (λ a → dfunext fe' (λ b →
           ap₂ (g h)
               (inverses-are-sections (⌜ π h ⌝) ⌜ π h ⌝-is-equiv a)
               (inverses-are-sections (⌜ π h ⌝) ⌜ π h ⌝-is-equiv b))))

   τ'-is-equiv : is-equiv τ'
   τ'-is-equiv = qinvs-are-equivs τ'  (τ'⁻¹ , η , ε)

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

TODO. Write more examples, such as monoids, groups and
1-categories. Perhaps it would be good to write combinators, like in
UF.SIP, to show that mathematical structures constructed from standard
building blocks, such as the above, form injective types.

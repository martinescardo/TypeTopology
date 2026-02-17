Ian Ray 1 September 2023 -- edited 9 April 2024

We formalize Curi's notion of abstract inductive definition (in CZF) within
the context of a sup-lattice L with small basis B (and β : B → L). An abstract
inductive definition is a subset ϕ : B × L → Prop (in the TypeTopology library
the type of propositions is denoted Ω) which can be thought of as a
'inference rule' concluding b from a (in the case ϕ(b,a) holds). An inductive
definition induces a closure condition. For example, a subset S is closed under
ϕ if for all b : B and a : L such that (b , a) ∈ ϕ and ↓ᴮa is 'contained' in
S then b ∈ S. Interestingly, there is an intimate connection between the
least-closed subsets of some inductive definition ϕ and the least fixed point
of a monotone map related to ϕ. Constructing these least-closed subsets in
traditional foundations is somewhat grueling. Fortunately, unlike in the realm
of set theory, inductive constructions are first class citizens in a type
theoretic setting. Using UF + HITs we can construct the least closed subset,
under an inductive definition ϕ, as a special quotient inductive type (QIT).
In this file we will develop this relationship and prove a predicative version
of the least fixed point theorem. This work follows the paper 'On Tarski's
Fixed Point Theorem' by Giovanni Curi:

Giovanni Curi. "On Tarski's fixed point theorem". In: Proc. Amer. Math. Soc
143 (2015), pp. 4439-4455. DOI: http://doi.org/10.1090/proc/12569

For a write up of the present formalization in a type theoretic setting see
https://arxiv.org/abs/2401.00841

The content of the present formalization works towards the following result.

Predicative Least Fixed Point Theorem:
Given a 𝓥-sup-lattice L with a 𝓥-presentation and a monotone
endomap f : L → L. If there exists a bounded abstract inductive definition
ϕ such that f ＝ Γ ϕ, then f has a least fixed point.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Size
open import UF.SmallnessProperties
open import UF.UniverseEmbedding

module OrderedTypes.PredicativeLFP
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of)
open import Slice.Family
open import UF.ImageAndSurjection pt
open import OrderedTypes.SupLattice pt fe
open import OrderedTypes.SupLattice-SmallBasis pt fe

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

We commence by defining what it means for a monotone endomap to have
a least fixed point.

\begin{code}

module _ {𝓤 𝓣 𝓥 : Universe} (L : Sup-Lattice 𝓤 𝓣 𝓥) where

 has-least-fixed-point : (f : ⟨ L ⟩ → ⟨ L ⟩) → 𝓤 ⊔ 𝓣 ̇
 has-least-fixed-point f =
  Σ p ꞉ ⟨ L ⟩ , (f p ＝ p) × ((a : ⟨ L ⟩) → (f a ＝ a) → (p ≤⟨ L ⟩ a) holds)

 has-least-fixed-point-is-prop : (f : ⟨ L ⟩ → ⟨ L ⟩)
                               → is-prop (has-least-fixed-point f)
 has-least-fixed-point-is-prop f (p₁ , fp₁ , l₁) (p₂ , fp₂ , l₂) =
  to-subtype-＝ (λ x → ×-is-prop
                       (sethood-of L)
                       (Π-is-prop fe (λ y → Π-is-prop fe
                        (λ _ → holds-is-prop (x ≤⟨ L ⟩ y)))))
                (antisymmetry-of L (l₁ p₂ fp₂) (l₂ p₁ fp₁))

\end{code}

We construct the least closed subset of an inductive definition as a QIT family.
Since QITs (and more generally HITs) are not native in Agda we will instead
assume the existence of such a type as well as its induction principle.
Technically speaking we are going to use record types to package the contents
of this QIT family.

Notice all constructors are 'strictly positive' and the path constructors are
'natural' (see Chapter 6 Section 13 of the HoTT book
https://homotopytypetheory.org/book/).

Notice that the QIT family has two constructors which represent the closure
conditions we wish to impose on subsets. The c-closure condition says:
for any subset contained in the least closed subset, elements in the downset of
its join are in the least closed subset as well. That is, Y is c-closed if
  for any U ⊆ Y we have ↓ᴮ (⋁ U) ⊆ Y.
The ϕ-cl constructor says:
if for any a : L and b : B with (b , a) ∈ ϕ and ↓ᴮ a 'contained' in the least
closed subset then b is in the least closed subset. That is, Y is ϕ-closed if
  for any a : L and b : B we have (b , a) ∈ ϕ ∧ ↓ᴮ a ⊆ Y ⇒ b ∈ Y.

It is worth noting that we don't encode the downsets as subsets in type
theory (rather they are total spaces) so for that reason we won't encode the
closure conditions exactly as above.

TODO: Add syntax so the closure conditions more closely align with the naive
description given above.

We also derive the initiality of the least closed subset from the postulated
induction principle. Initiality is closely related to the 'least' part of
our least fixed point theorem.

\begin{code}

module _
        {𝓤 𝓣 𝓥 : Universe}
        {B : 𝓥 ̇ }
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        (β : B → ⟨ L ⟩)
        (h : is-basis L β)
       where

 private
  _≤_ = order-of L
  ⋁_ = join-of L

 open Joins _≤_
 open is-basis h

\end{code}

We give names to the closure conditions.

\begin{code}

 c-closure : {𝓦 : Universe} (S : 𝓟 {𝓦} B) → (𝓥 ⁺) ⊔ 𝓦 ̇
 c-closure S = (U : 𝓟 {𝓥} B)
             → U ⊆ S
             → (b : B) → b ≤ᴮ (⋁ 【 β , U 】)
             → b ∈ S

 _closure : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
          → {𝓦 : Universe} (S : 𝓟 {𝓦} B)
          → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
 (ϕ closure) S = (a : ⟨ L ⟩)
               → (b : B)
               → (b , a) ∈ ϕ
               → ((b' : B) → (b' ≤ᴮ a → b' ∈ S))
               → b ∈ S

\end{code}

The following record type should be interpreted as supplying the assumption
that the QIT family exists with the apropriate 'initiality' principle
(initiality is considerably weaker than an induction/recursion principle that
one may expect).

\begin{code}

 record inductively-generated-subset-exists (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)): 𝓤ω
  where
  constructor
   inductively-generated-subset

  field
   Ind : B → 𝓤 ⊔ 𝓥 ⁺ ̇
   Ind-trunc : (b : B) → is-prop (Ind b)
  private
   𝓘 : 𝓟 {𝓤 ⊔ 𝓥 ⁺} B
   𝓘 b = (Ind b , Ind-trunc b)
  field
   c-closed : c-closure 𝓘
   ϕ-closed : (ϕ closure) 𝓘
   Ind-initial : (P : 𝓟 {𝓦} B)
               → c-closure P
               → (ϕ closure) P
               → 𝓘 ⊆ P

 module trunc-ind-def
         (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
         (ind-e : inductively-generated-subset-exists ϕ)
        where

  open inductively-generated-subset-exists ind-e

\end{code}

We will now combine the postulated data above to form the least closed subset
of B under some inductive definition ϕ and restate the closure properties and
initiality in terms of it.

\begin{code}

  𝓘nd : 𝓟 {𝓤 ⊔ 𝓥 ⁺} B
  𝓘nd b = (Ind b , Ind-trunc b)

  𝓘nd-is-c-closed : c-closure 𝓘nd
  𝓘nd-is-c-closed = c-closed

  𝓘nd-is-ϕ-closed : (ϕ closure) 𝓘nd
  𝓘nd-is-ϕ-closed = ϕ-closed

  𝓘nd-is-initial : (P : 𝓟 {𝓦} B)
                 → c-closure P
                 → (ϕ closure) P
                 → 𝓘nd ⊆ P
  𝓘nd-is-initial = Ind-initial

\end{code}

We now consider a restricted class of inductive definitions which we will call
local. A local inductive definition ϕ is one such that the type

  Σ b ꞉ B , (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a)

is small.

We then define an operator parameterized by local inductive definitions
and prove that it is monotone. Finally, we show that any monotone endo map on
a sup-lattice determines a monotone operator and corresponding local
inductive definition.

\begin{code}

module local-inductive-definitions
        {𝓤 𝓣 𝓥 : Universe}
        {B : 𝓥 ̇ }
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        (β : B → ⟨ L ⟩)
        (h : is-basis L β)
       where

 private
  _≤_ = order-of L
  ⋁_ = join-of L

 open Joins _≤_
 open is-basis h

\end{code}

We now define an auxiliary subset/total space which we will use to define the
upcoming monotone operator. This subset is in some sense a generalized downset
that depends on ϕ.

\begin{code}

 _↓_ : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → (a : ⟨ L ⟩) → 𝓤 ⊔ 𝓣 ⊔ 𝓥 ̇
 ϕ ↓ a = Σ b ꞉ B , (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds

 ↓-to-base : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → (a : ⟨ L ⟩) → ϕ ↓ a → B
 ↓-to-base ϕ a = pr₁

 ↓-monotonicity-lemma : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                      → (x y : ⟨ L ⟩)
                      → (x ≤ y) holds
                      → ϕ ↓ x
                      → ϕ ↓ y
 ↓-monotonicity-lemma ϕ x y o (b , c) = (b , inclusion c)
  where
   inclusion : (Ǝ a' ꞉ ⟨ L ⟩ , ((b , a') ∈ ϕ) × ((a' ≤ x) holds)) holds
             → (Ǝ a' ꞉ ⟨ L ⟩ , ((b , a') ∈ ϕ) × ((a' ≤ y) holds)) holds
   inclusion = ∥∥-functor untrunc-inclusion
    where
     untrunc-inclusion : Σ a' ꞉ ⟨ L ⟩ , ((b , a') ∈ ϕ) × ((a' ≤ x) holds)
                       → Σ a' ꞉ ⟨ L ⟩ , ((b , a') ∈ ϕ) × ((a' ≤ y) holds)
     untrunc-inclusion (a' , p , r) = (a' , p , transitivity-of L a' x y r o)

 ↓-has-sup-implies-monotone : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                            → (x y s s' : ⟨ L ⟩)
                            → (x ≤ y) holds
                            → (s is-lub-of (ϕ ↓ x , β ∘ ↓-to-base ϕ x)) holds
                            → (s' is-lub-of (ϕ ↓ y , β ∘ ↓-to-base ϕ y)) holds
                            → (s ≤ s') holds
 ↓-has-sup-implies-monotone
  ϕ x y s s' o (is-upbnd , is-least-upbnd) (is-upbnd' , is-least-upbnd') =
   is-least-upbnd (s' , s'-is-upbnd)
  where
   s'-is-upbnd : (s' is-an-upper-bound-of (ϕ ↓ x , β ∘ ↓-to-base ϕ x)) holds
   s'-is-upbnd (b , e) = is-upbnd' (↓-monotonicity-lemma ϕ x y o ((b , e)))

 is-local : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → 𝓤 ⊔ 𝓣 ⊔ (𝓥 ⁺) ̇
 is-local ϕ = (a : ⟨ L ⟩) → (ϕ ↓ a) is 𝓥 small

 module _ (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) (i : is-local ϕ) where

  private
   S' : (a : ⟨ L ⟩) → 𝓥 ̇
   S' a = resized (ϕ ↓ a) (i a)

   S'-equiv-↓ : (a : ⟨ L ⟩) → S' a ≃ ϕ ↓ a
   S'-equiv-↓ a  = resizing-condition (i a)

   S'-to-↓ : (a : ⟨ L ⟩) → S' a → ϕ ↓ a
   S'-to-↓ a = ⌜ S'-equiv-↓ a ⌝

   ↓-to-S' : (a : ⟨ L ⟩) → ϕ ↓ a → S' a
   ↓-to-S' a = ⌜ S'-equiv-↓ a ⌝⁻¹

   S'-monotone-ish : (x y : ⟨ L ⟩)
                   → (x ≤ y) holds
                   → S' x
                   → S' y
   S'-monotone-ish x y o =
    ↓-to-S' y ∘ ↓-monotonicity-lemma ϕ x y o ∘ S'-to-↓ x

  Γ : ⟨ L ⟩ → ⟨ L ⟩
  Γ a = ⋁ (S' a , β ∘ pr₁ ∘ S'-to-↓ a)

\end{code}

We show that Γ is monotone.

\begin{code}

  Γ-is-monotone : is-monotone-endomap L Γ
  Γ-is-monotone x y o =
   ↓-has-sup-implies-monotone ϕ x y (Γ x) (Γ y) o Γx-is-lub Γy-is-lub
   where
    Γx-is-lub : (Γ x is-lub-of (ϕ ↓ x , β ∘ ↓-to-base ϕ x)) holds
    Γx-is-lub = sup-of-small-fam-is-lub L (β ∘ ↓-to-base ϕ x) (i x)
    Γy-is-lub : (Γ y is-lub-of (ϕ ↓ y , β ∘ ↓-to-base ϕ y)) holds
    Γy-is-lub = sup-of-small-fam-is-lub L (β ∘ ↓-to-base ϕ y) (i y)

\end{code}

We now show that every monotone map determines and local inductive definition.

\begin{code}

 monotone-map-give-local-ind-def : (f : ⟨ L ⟩ → ⟨ L ⟩)
                                 → is-monotone-endomap L f
                                 → Σ ϕ ꞉ 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩) ,
                                   Σ i ꞉ (is-local ϕ) ,
                                    ((x : ⟨ L ⟩) → (Γ ϕ i) x ＝ f x)
 monotone-map-give-local-ind-def f f-mono = (ϕ , i , H)
  where
   ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)
   ϕ (b , a) =
    (Lift 𝓤 (b ≤ᴮ f a) , equiv-to-prop (Lift-≃ 𝓤 (b ≤ᴮ f a)) ≤ᴮ-is-prop-valued)
   ↓ᴮf-equiv-↓-tot : (a : ⟨ L ⟩) → small-↓ᴮ (f a) ≃ ϕ ↓ a
   ↓ᴮf-equiv-↓-tot a =
    Σ-cong' (λ z → z ≤ᴮ f a)
            ((λ z → (Ǝ a' ꞉ ⟨ L ⟩ , (z , a') ∈ ϕ × (a' ≤ a) holds) holds))
            ↓ᴮf-equiv-↓
    where
     ↓ᴮf-equiv-↓ : (z : B)
                 → (z ≤ᴮ f a)
                 ≃ (Ǝ a' ꞉ ⟨ L ⟩ , (z , a') ∈ ϕ × (a' ≤ a) holds) holds
     ↓ᴮf-equiv-↓ z =
      ⌜ prop-≃-≃-↔ fe ≤ᴮ-is-prop-valued ∥∥-is-prop ⌝⁻¹ (↓ᴮf-to-↓ , ↓-to-↓ᴮf)
      where
       ↓ᴮf-to-↓ : z ≤ᴮ f a
                → (Ǝ a' ꞉ ⟨ L ⟩ , (z , a') ∈ ϕ × (a' ≤ a) holds) holds
       ↓ᴮf-to-↓ o = ∣ (a , ⌜ ≃-Lift 𝓤 (z ≤ᴮ f a) ⌝ o , reflexivity-of L a) ∣
       ↓-to-↓ᴮf : (Ǝ a' ꞉ ⟨ L ⟩ , (z , a') ∈ ϕ × (a' ≤ a) holds) holds
                → z ≤ᴮ f a
       ↓-to-↓ᴮf = ∥∥-rec ≤ᴮ-is-prop-valued ↓-to-↓ᴮf'
        where
         ↓-to-↓ᴮf' : Σ a' ꞉ ⟨ L ⟩ , (z , a') ∈ ϕ × (a' ≤ a) holds → z ≤ᴮ f a
         ↓-to-↓ᴮf' (a' , o , r) =
          ≤-to-≤ᴮ (transitivity-of L (β z) (f a') (f a)
                                   (≤ᴮ-to-≤
                                   (⌜ ≃-Lift 𝓤 (z ≤ᴮ f a') ⌝⁻¹ o))
                                   (f-mono a' a r))
   i : is-local ϕ
   i a = (small-↓ᴮ (f a) , ↓ᴮf-equiv-↓-tot a)
   G : (x : ⟨ L ⟩) → (f x is-lub-of (ϕ ↓ x , β ∘ ↓-to-base ϕ x)) holds
   G x = (fx-is-upbnd , fx-is-least-upbnd)
    where
     fx-is-upbnd : (f x is-an-upper-bound-of (ϕ ↓ x , β ∘ ↓-to-base ϕ x)) holds
     fx-is-upbnd (b , e) = ↓-to-fx-upbnd e
      where
       ↓-to-fx-upbnd : (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ x) holds) holds
                     → (β b ≤ f x) holds
       ↓-to-fx-upbnd = ∥∥-rec (holds-is-prop (β b ≤ f x)) ↓-to-fx-upbnd'
        where
         ↓-to-fx-upbnd' : Σ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ x) holds
                        → (β b ≤ f x) holds
         ↓-to-fx-upbnd' (a' , o , r) =
          transitivity-of L (β b) (f a') (f x)
                          (≤ᴮ-to-≤ (⌜ ≃-Lift 𝓤 (b ≤ᴮ f a') ⌝⁻¹ o))
                          (f-mono a' x r)
     fx-is-least-upbnd : ((u , _) : upper-bound (ϕ ↓ x , β ∘ ↓-to-base ϕ x))
                       → (f x ≤ u) holds
     fx-is-least-upbnd (u , is-upbnd) =
      (is-least-upper-boundᴮ (f x))
       (u , λ z → is-upbnd (⌜ ↓ᴮf-equiv-↓-tot x ⌝ z))
   H : (x : ⟨ L ⟩) → (Γ ϕ i) x ＝ f x
   H x =
    reindexing-along-equiv-＝-sup
     L (id , id-is-equiv (ϕ ↓ x)) (β ∘ ↓-to-base ϕ x)
     ((Γ ϕ i) x) (f x) (sup-of-small-fam-is-lub  L (β ∘ ↓-to-base ϕ x) (i x))
     (G x)

 ind-def-from-monotone-map : (f : ⟨ L ⟩ → ⟨ L ⟩)
                           → is-monotone-endomap L f
                           → 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)
 ind-def-from-monotone-map f f-mono =
  pr₁ (monotone-map-give-local-ind-def f f-mono)

 local-from-monotone-map : (f : ⟨ L ⟩ → ⟨ L ⟩)
                         → (f-mono : is-monotone-endomap L f)
                         → is-local (ind-def-from-monotone-map f f-mono)
 local-from-monotone-map f f-mono =
  pr₁ (pr₂ (monotone-map-give-local-ind-def f f-mono))

 local-ind-def-is-section-of-Γ : (f : ⟨ L ⟩ → ⟨ L ⟩)
                               → (f-mono : is-monotone-endomap L f)
                               → (x : ⟨ L ⟩)
                               → (Γ (ind-def-from-monotone-map f f-mono)
                                    (local-from-monotone-map f f-mono)) x
                               ＝ f x
 local-ind-def-is-section-of-Γ f f-mono =
  pr₂ (pr₂ (monotone-map-give-local-ind-def f f-mono))

\end{code}

We now spell out the correspondence between small 'closed' subsets and
deflationary points in our sup-lattice. This will allow us to show that
monotone operators have a least fixed point under certain smallness
assumpions.

\begin{code}

module _
        {𝓤 𝓣 𝓥 : Universe}
        {B : 𝓥 ̇ }
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        (β : B → ⟨ L ⟩)
        (h : is-basis L β)
       where

 private
  _≤_ = order-of L
  ⋁_ = join-of L

 open Joins _≤_
 open is-basis h
 open local-inductive-definitions L β h

 module correspondance-from-locally-small-ϕ
         (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
         (i : is-local ϕ)
        where

\end{code}

Next we give a name to the type of subsets of size 𝓥 (small) that are c-closed
and ϕ-closed (recall, that closure was initially defined for subsets with
respect to an arbitrary universe parameter 𝓣.)

\begin{code}

  is-small-closed-subset : (P : 𝓟 {𝓥} B) → 𝓤 ⊔ (𝓥 ⁺) ̇
  is-small-closed-subset P = ((U : 𝓟 {𝓥} B)
                            → (U ⊆ P)
                            → ((b : B)
                            → b ≤ᴮ (⋁ 【 β , U 】)
                            → b ∈ P))
                           × ((a : ⟨ L ⟩)
                            → (b : B)
                            → (b , a) ∈ ϕ
                            → ((b' : B) → (b' ≤ᴮ a → b' ∈ P))
                            → b ∈ P)

  is-small-closed-subset-is-predicate : (P : 𝓟 {𝓥} B)
                                      → is-prop (is-small-closed-subset P)
  is-small-closed-subset-is-predicate P =
   ×-is-prop (Π₄-is-prop fe (λ _ _ b _ → holds-is-prop (P b)))
             (Π₄-is-prop fe (λ _ b _ _ → holds-is-prop (P b)))

  small-closed-subsets : 𝓤 ⊔ (𝓥 ⁺) ̇
  small-closed-subsets = Σ P ꞉ 𝓟 {𝓥} B , is-small-closed-subset P

  subset-of-small-closed-subset : small-closed-subsets → 𝓟 {𝓥} B
  subset-of-small-closed-subset (P , c-clsd , ϕ-clsd) = P

  c-closed-of-small-closed-subset : (X : small-closed-subsets)
                                  → ((U : 𝓟 {𝓥} B)
                                  → U ⊆ subset-of-small-closed-subset X
                                  → ((b : B)
                                  → b ≤ᴮ (⋁ 【 β , U 】)
                                  → b ∈ subset-of-small-closed-subset X))
  c-closed-of-small-closed-subset (P , c-clsd , ϕ-clsd) = c-clsd

  ϕ-closed-of-small-closed-subset : (X : small-closed-subsets)
                                  → ((a : ⟨ L ⟩)
                                  → (b : B)
                                  → ((b , a) ∈ ϕ)
                                  → ((b' : B)
                                  → (b' ≤ᴮ a
                                  → b' ∈ subset-of-small-closed-subset X))
                                  → b ∈ subset-of-small-closed-subset X)
  ϕ-closed-of-small-closed-subset (P , c-clsd , ϕ-clsd) = ϕ-clsd

  is-deflationary : (a : ⟨ L ⟩) → 𝓣 ̇
  is-deflationary a = ((Γ ϕ i) a ≤ a) holds

  is-deflationary-is-predicate : (a : ⟨ L ⟩) → is-prop (is-deflationary a)
  is-deflationary-is-predicate a = holds-is-prop ((Γ ϕ i) a ≤ a)

  deflationary-points : 𝓤 ⊔ 𝓣 ̇
  deflationary-points = Σ a ꞉ ⟨ L ⟩ , (is-deflationary a)

  point-def-points : deflationary-points → ⟨ L ⟩
  point-def-points (a , _) = a

  is-deflationary-def-points : (X : deflationary-points)
                             → is-deflationary (point-def-points X)
  is-deflationary-def-points (_ , dp) = dp

  small-closed-subsets-to-def-points : small-closed-subsets
                                     → deflationary-points
  small-closed-subsets-to-def-points (P , c-closed , ϕ-closed) =
   (sup-of-P , sup-is-def)
   where
    sup-of-P : ⟨ L ⟩
    sup-of-P = ⋁ 【 β , P 】
    sup-is-def : is-deflationary sup-of-P
    sup-is-def = lub-condition (sup-of-P , is-upper-bound)
     where
      sup-is-lub :
       ((Γ ϕ i) sup-of-P is-lub-of (ϕ ↓ sup-of-P , β ∘ ↓-to-base ϕ sup-of-P))
        holds
      sup-is-lub =
       sup-of-small-fam-is-lub L (β ∘ ↓-to-base ϕ sup-of-P) (i sup-of-P)
      lub-condition :
       ((u , _) : upper-bound (ϕ ↓ sup-of-P , β ∘ ↓-to-base ϕ sup-of-P))
       → ((Γ ϕ i) sup-of-P ≤ u) holds
      lub-condition = pr₂ sup-is-lub
      b-in-P-to-b-below-sup : (b : B) → b ∈ P → (β b ≤ sup-of-P) holds
      b-in-P-to-b-below-sup b b-in-P =
       (join-is-upper-bound-of L 【 β , P 】) (b , b-in-P)
      un-trunc-map : (b : B)
                   → Σ a ꞉ ⟨ L ⟩ , (b , a) ∈ ϕ × (a ≤ sup-of-P) holds
                   → (β b ≤ sup-of-P) holds
      un-trunc-map b (a , p , o) =
       b-in-P-to-b-below-sup b (ϕ-closed a b p (ϕ-hypothesis))
       where
        ϕ-hypothesis : (b' : B) → b' ≤ᴮ a → b' ∈ P
        ϕ-hypothesis b' r = c-closed P (λ x → id) b' b'-below-sup-P
         where
          b'-below-sup-P : b' ≤ᴮ sup-of-P
          b'-below-sup-P =
           ≤-to-≤ᴮ (transitivity-of L (β b') a sup-of-P (≤ᴮ-to-≤ r) o)
      is-upper-bound : ((b , e) : ϕ ↓ sup-of-P) → (β b ≤ sup-of-P) holds
      is-upper-bound (b , e) =
       ∥∥-rec (holds-is-prop (β b ≤ sup-of-P)) (un-trunc-map b) e

  def-points-to-small-closed-subsets : deflationary-points
                                     → small-closed-subsets
  def-points-to-small-closed-subsets (a , is-def) =
   (Q a , c-closed , ϕ-closed)
   where
    Q : (x : ⟨ L ⟩) → 𝓟 {𝓥} B
    Q x b = (b ≤ᴮ x , ≤ᴮ-is-prop-valued)
    sup-Q_ : (x : ⟨ L ⟩) → ⟨ L ⟩
    sup-Q x = ⋁ 【 β , Q x 】
    _is-sup-Q : (x : ⟨ L ⟩) → x ＝ sup-Q x
    x is-sup-Q = is-supᴮ' x
    c-closed : (U : 𝓟 {𝓥} B)
             → (U ⊆ Q a)
             → ((b : B) → (b ≤ᴮ (⋁ 【 β , U 】)) →  b ∈ Q a)
    c-closed U C b o =
     ≤-to-≤ᴮ (transitivity-of L (β b) (⋁ 【 β , U 】) a (≤ᴮ-to-≤ o)
              (transport (λ - → ((⋁ 【 β , U 】) ≤ -) holds)
                         (a is-sup-Q ⁻¹)
                         (joins-preserve-containment
                         L β {U} {Q a} C)))
    ϕ-closed : (a' : ⟨ L ⟩)
             → (b : B)
             → ((b , a') ∈ ϕ)
             → ((b' : B) → (b' ≤ᴮ a' → b' ∈ Q a)) → b ∈ Q a
    ϕ-closed a' b p f = trunc-map b ∣ (a' , p , a'-below-a) ∣
     where
      Γ-is-sup : ((Γ ϕ i) a is-lub-of (ϕ ↓ a , β ∘ ↓-to-base ϕ a)) holds
      Γ-is-sup = sup-of-small-fam-is-lub L (β ∘ ↓-to-base ϕ a) (i a)
      Γ-an-upper-bound :
       ((Γ ϕ i) a is-an-upper-bound-of (ϕ ↓ a , β ∘ ↓-to-base ϕ a)) holds
      Γ-an-upper-bound = pr₁ Γ-is-sup
      trunc-map : (x : B)
                → (Ǝ a'' ꞉ ⟨ L ⟩ , (x , a'') ∈ ϕ × (a'' ≤ a) holds) holds
                → x ≤ᴮ a
      trunc-map x e = ≤-to-≤ᴮ (transitivity-of L (β x) ((Γ ϕ i) a) a
                                               (Γ-an-upper-bound (x , e))
                                               (is-def))
      a'-below-a : (a' ≤ a) holds
      a'-below-a =
       transport (λ - → (- ≤ a) holds) (a' is-sup-Q ⁻¹)
                 (transport (λ - → ((sup-Q a') ≤ -) holds)
                            (a is-sup-Q ⁻¹)
                            (joins-preserve-containment L β {Q a'} {Q a} f))

  small-closed-subsets-≃-def-points :
    small-closed-subsets ≃ deflationary-points
  small-closed-subsets-≃-def-points =
   (small-closed-subsets-to-def-points ,
    qinvs-are-equivs small-closed-subsets-to-def-points is-qinv)
   where
    H : def-points-to-small-closed-subsets
      ∘ small-closed-subsets-to-def-points ∼ id
    H (P , c-closed , ϕ-closed) =
     to-subtype-＝ is-small-closed-subset-is-predicate P'-is-P
     where
      sup-P : ⟨ L ⟩
      sup-P = point-def-points
              (small-closed-subsets-to-def-points
               (P , c-closed , ϕ-closed))
      P' : 𝓟 {𝓥} B
      P' = subset-of-small-closed-subset
            (def-points-to-small-closed-subsets
             (small-closed-subsets-to-def-points
              (P , c-closed , ϕ-closed)))
      P'-is-P : P' ＝ P
      P'-is-P = dfunext fe P'-htpy-P
       where
        P'-htpy-P : P' ∼ P
        P'-htpy-P x =
         to-Ω-＝ fe
                (pe ≤ᴮ-is-prop-valued (holds-is-prop (P x)) P'-to-P P-to-P')
         where
          P'-to-P : x ≤ᴮ sup-P → x ∈ P
          P'-to-P = c-closed P (λ _ → id) x
          P-to-P' : x ∈ P → x ≤ᴮ sup-P
          P-to-P' r =
           ≤-to-≤ᴮ ((join-is-upper-bound-of L 【 β , P 】) (x , r))
    G : small-closed-subsets-to-def-points
      ∘ def-points-to-small-closed-subsets ∼ id
    G (a , is-def) = to-subtype-＝ is-deflationary-is-predicate sup-P-is-a
     where
      P : 𝓟 {𝓥} B
      P = subset-of-small-closed-subset
           (def-points-to-small-closed-subsets (a , is-def))
      sup-P : ⟨ L ⟩
      sup-P = point-def-points
               (small-closed-subsets-to-def-points
                (def-points-to-small-closed-subsets (a , is-def)))
      sup-P-is-a : sup-P ＝ a
      sup-P-is-a = is-supᴮ' a ⁻¹
    is-qinv : qinv small-closed-subsets-to-def-points
    is-qinv = (def-points-to-small-closed-subsets , H , G)

\end{code}

Using the previously displayed correspondance we can show that, under certain
smallness assumptions on the least closed subset 𝓘nd ϕ, the monotone operator
Γ ϕ has a least fixed point.

\begin{code}

  module small-𝓘nd-from-exists
          (ind-e : inductively-generated-subset-exists L β h ϕ)
         where

   open inductively-generated-subset-exists ind-e
   open trunc-ind-def L β h ϕ ind-e

   module smallness-assumption (j : (b : B) → (b ∈ 𝓘nd) is 𝓥 small) where

    private
     𝓘' : (b : B) →  𝓥 ̇
     𝓘' b = (resized (b ∈ 𝓘nd)) (j b)

     𝓘'-equiv-𝓘nd : (b : B) → 𝓘' b ≃ b ∈ 𝓘nd
     𝓘'-equiv-𝓘nd b = resizing-condition (j b)

     𝓘'-to-𝓘nd : (b : B) → 𝓘' b → b ∈ 𝓘nd
     𝓘'-to-𝓘nd b = ⌜ 𝓘'-equiv-𝓘nd b ⌝

     𝓘nd-to-𝓘' : (b : B) → b ∈ 𝓘nd → 𝓘' b
     𝓘nd-to-𝓘' b = ⌜ 𝓘'-equiv-𝓘nd b ⌝⁻¹

     𝓘'-is-prop-valued : {b : B} → is-prop (𝓘' b)
     𝓘'-is-prop-valued {b} = equiv-to-prop (𝓘'-equiv-𝓘nd b) (Ind-trunc b)

     𝓘'-subset : 𝓟 {𝓥} B
     𝓘'-subset = λ b → (𝓘' b , 𝓘'-is-prop-valued)

     𝓘'-is-c-closed : (U : 𝓟 {𝓥} B)
                    → U ⊆ 𝓘'-subset
                    → (b : B) → b ≤ᴮ (⋁ 【 β , U 】)
                    → b ∈ 𝓘'-subset
     𝓘'-is-c-closed U C b o =
       𝓘nd-to-𝓘' b (𝓘nd-is-c-closed U (λ x → 𝓘'-to-𝓘nd x ∘ C x) b o)

     𝓘'-is-ϕ-closed : (a : ⟨ L ⟩)
                    → (b : B)
                    → (b , a) ∈ ϕ
                    → ((b' : B) → b' ≤ᴮ a → b' ∈ 𝓘'-subset)
                    → b ∈ 𝓘'-subset
     𝓘'-is-ϕ-closed a b p f =
      𝓘nd-to-𝓘' b (𝓘nd-is-ϕ-closed a b p (λ b' → 𝓘'-to-𝓘nd b' ∘ f b'))

     total-space-𝓘-is-small : (𝕋 𝓘nd) is 𝓥 small
     total-space-𝓘-is-small = (𝕋 𝓘'-subset , Σ-cong λ b → 𝓘'-equiv-𝓘nd b)

     e : 𝕋 𝓘'-subset ≃ 𝕋 𝓘nd
     e = resizing-condition total-space-𝓘-is-small

     sup-𝓘 : ⟨ L ⟩
     sup-𝓘 = ⋁ (𝕋 𝓘'-subset , β ∘ 𝕋-to-carrier 𝓘nd ∘ ⌜ e ⌝)

     sup-𝓘-is-lub : (sup-𝓘 is-lub-of 【 β , 𝓘nd 】) holds
     sup-𝓘-is-lub = sup-of-small-fam-is-lub L (β ∘ 𝕋-to-carrier 𝓘nd)
                                            total-space-𝓘-is-small

    sup-𝓘-is-fixed-point : (Γ ϕ i) sup-𝓘 ＝ sup-𝓘
    sup-𝓘-is-fixed-point = antisymmetry-of L Γ-sup-below-sup sup-below-Γ-sup
     where
      Γ-sup-below-sup : ((Γ ϕ i) sup-𝓘 ≤ sup-𝓘) holds
      Γ-sup-below-sup = is-deflationary-def-points
                        (small-closed-subsets-to-def-points
                        (𝓘'-subset , 𝓘'-is-c-closed , 𝓘'-is-ϕ-closed))
      sup-below-Γ-sup : (sup-𝓘 ≤ (Γ ϕ i) sup-𝓘) holds
      sup-below-Γ-sup = transport (λ - → (sup-𝓘 ≤ -) holds)
                                  sup-Q-is-Γ-sup sup-𝓘-below-sup-Q
       where
        Γ-Γ-sup-below-Γ-sup : ((Γ ϕ i) ((Γ ϕ i) sup-𝓘) ≤ (Γ ϕ i) sup-𝓘) holds
        Γ-Γ-sup-below-Γ-sup =
         Γ-is-monotone ϕ i ((Γ ϕ i) sup-𝓘) sup-𝓘 Γ-sup-below-sup
        Q-Γ-sup : 𝓟 {𝓥} B
        Q-Γ-sup = subset-of-small-closed-subset
                   (def-points-to-small-closed-subsets
                    ((Γ ϕ i) sup-𝓘 , Γ-Γ-sup-below-Γ-sup))
        Q-is-c-closed : (U : 𝓟 {𝓥} B)
                      → (U ⊆ Q-Γ-sup)
                      → ((b : B)
                      → b ≤ᴮ (⋁ 【 β , U 】)
                      → b ∈ Q-Γ-sup)
        Q-is-c-closed =
         c-closed-of-small-closed-subset
          (def-points-to-small-closed-subsets
           ((Γ ϕ i) sup-𝓘 , Γ-Γ-sup-below-Γ-sup))
        Q-is-ϕ-closed : (a' : ⟨ L ⟩)
                      → (b : B)
                      → ((b , a') ∈ ϕ)
                      → ((b' : B)
                      → (b' ≤ᴮ a' → b' ∈ Q-Γ-sup))
                      → b ∈ Q-Γ-sup
        Q-is-ϕ-closed = ϕ-closed-of-small-closed-subset
                         (def-points-to-small-closed-subsets
                          ((Γ ϕ i) sup-𝓘 , Γ-Γ-sup-below-Γ-sup))
        𝓘nd-contained-Q-Γ-sup : 𝓘nd ⊆ Q-Γ-sup
        𝓘nd-contained-Q-Γ-sup =
         𝓘nd-is-initial Q-Γ-sup Q-is-c-closed Q-is-ϕ-closed
        𝓘-is-small-subset-contained-Q-Γ-sup : 𝓘'-subset ⊆ Q-Γ-sup
        𝓘-is-small-subset-contained-Q-Γ-sup =
         (λ z → 𝓘nd-contained-Q-Γ-sup z ∘ 𝓘'-to-𝓘nd z)
        sup-Q : ⟨ L ⟩
        sup-Q = ⋁ 【 β , Q-Γ-sup 】
        sup-𝓘-below-sup-Q : (sup-𝓘 ≤ sup-Q) holds
        sup-𝓘-below-sup-Q =
         joins-preserve-containment L β {𝓘'-subset} {Q-Γ-sup}
                                    𝓘-is-small-subset-contained-Q-Γ-sup
        sup-Q-is-Γ-sup : sup-Q ＝ (Γ ϕ i) sup-𝓘
        sup-Q-is-Γ-sup = is-supᴮ' ((Γ ϕ i) sup-𝓘) ⁻¹

    sup-𝓘-is-least-fixed-point : (a : ⟨ L ⟩)
                               → (Γ ϕ i) a ＝ a
                               → (sup-𝓘 ≤⟨ L ⟩ a) holds
    sup-𝓘-is-least-fixed-point a p = transport (λ - → (sup-𝓘 ≤ -) holds)
                                               sup-P-is-a
                                               sup-𝓘-below-sup-P
     where
      Γa-below-a : ((Γ ϕ i) a ≤ a) holds
      Γa-below-a = transport (λ - → ((Γ ϕ i) a ≤ -) holds)
                             p (reflexivity-of L ((Γ ϕ i) a))
      P-a : 𝓟 {𝓥} B
      P-a = subset-of-small-closed-subset
             (def-points-to-small-closed-subsets (a , Γa-below-a))
      P-is-c-closed : (U : 𝓟 {𝓥} B)
                    → (U ⊆ P-a)
                    → ((b : B)
                    → b ≤ᴮ (⋁ 【 β , U 】)
                    → b ∈ P-a)
      P-is-c-closed = c-closed-of-small-closed-subset
                       (def-points-to-small-closed-subsets
                        (a , Γa-below-a))
      P-is-ϕ-closed : (a' : ⟨ L ⟩)
                    → (b : B)
                    → ((b , a') ∈ ϕ)
                    → ((b' : B)
                    → (b' ≤ᴮ a' → b' ∈ P-a))
                    → b ∈ P-a
      P-is-ϕ-closed = ϕ-closed-of-small-closed-subset
                       (def-points-to-small-closed-subsets
                        (a , Γa-below-a))
      𝓘nd-contained-P-a : 𝓘nd ⊆ P-a
      𝓘nd-contained-P-a = 𝓘nd-is-initial P-a P-is-c-closed P-is-ϕ-closed
      𝓘'-subset-contained-P-a : 𝓘'-subset ⊆ P-a
      𝓘'-subset-contained-P-a = λ z → 𝓘nd-contained-P-a z ∘ 𝓘'-to-𝓘nd z
      sup-P : ⟨ L ⟩
      sup-P = ⋁ 【 β , P-a 】
      sup-𝓘-below-sup-P : (sup-𝓘 ≤ sup-P) holds
      sup-𝓘-below-sup-P =
       joins-preserve-containment L β {𝓘'-subset} {P-a}
                                  𝓘'-subset-contained-P-a
      sup-P-is-a : sup-P ＝ a
      sup-P-is-a = is-supᴮ' a ⁻¹

    Γ-has-least-fixed-point : has-least-fixed-point L (Γ ϕ i)
    Γ-has-least-fixed-point =
      (sup-𝓘 , sup-𝓘-is-fixed-point , sup-𝓘-is-least-fixed-point)
     where
      sup-𝓘-below : (a : ⟨ L ⟩) → ((Γ ϕ i) a ＝ a) → (sup-𝓘 ≤ a) holds
      sup-𝓘-below a p = transport (λ - → (sup-𝓘 ≤ -) holds)
                                  sup-P-is-a
                                  sup-𝓘-below-sup-P
       where
        Γa-below-a : ((Γ ϕ i) a ≤ a) holds
        Γa-below-a = transport (λ - → ((Γ ϕ i) a ≤ -) holds)
                               p (reflexivity-of L ((Γ ϕ i) a))
        P-a : 𝓟 {𝓥} B
        P-a = subset-of-small-closed-subset
               (def-points-to-small-closed-subsets (a , Γa-below-a))
        P-is-c-closed : (U : 𝓟 {𝓥} B)
                      → (U ⊆ P-a)
                      → ((b : B)
                      → b ≤ᴮ (⋁ 【 β , U 】)
                      → b ∈ P-a)
        P-is-c-closed = c-closed-of-small-closed-subset
                         (def-points-to-small-closed-subsets
                          (a , Γa-below-a))
        P-is-ϕ-closed : (a' : ⟨ L ⟩)
                      → (b : B)
                      → ((b , a') ∈ ϕ)
                      → ((b' : B)
                      → (b' ≤ᴮ a' → b' ∈ P-a))
                      → b ∈ P-a
        P-is-ϕ-closed = ϕ-closed-of-small-closed-subset
                         (def-points-to-small-closed-subsets
                          (a , Γa-below-a))
        𝓘nd-contained-P-a : 𝓘nd ⊆ P-a
        𝓘nd-contained-P-a = 𝓘nd-is-initial P-a P-is-c-closed P-is-ϕ-closed
        𝓘'-subset-contained-P-a : 𝓘'-subset ⊆ P-a
        𝓘'-subset-contained-P-a = λ z → 𝓘nd-contained-P-a z ∘ 𝓘'-to-𝓘nd z
        sup-P : ⟨ L ⟩
        sup-P = ⋁ 【 β , P-a 】
        sup-𝓘-below-sup-P : (sup-𝓘 ≤ sup-P) holds
        sup-𝓘-below-sup-P =
         joins-preserve-containment L β {𝓘'-subset} {P-a}
                                    𝓘'-subset-contained-P-a
        sup-P-is-a : sup-P ＝ a
        sup-P-is-a = is-supᴮ' a ⁻¹

\end{code}

The remainder of this formalization is essentially a search for restrictions
we may impose on sup-lattices and inductive definitions to achieve the
neccesary smallness assumptions on 𝓘nd which will guarentee least fixed points.

We now consider a boundedness restricion on inductive definitions and show
that bounded inductive definitions are local.

An inductive definition is bounded if there is a small indexed family of
types that can be substituted for elements a : L in a sense to be made
precise below.

\begin{code}

module bounded-inductive-definitions
        {𝓤 𝓣 𝓥 : Universe}
        {B : 𝓥 ̇ }
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        (β : B → ⟨ L ⟩)
        (h : is-basis L β)
       where

 private
  _≤_ = order-of L
  ⋁_ = join-of L

 open Joins _≤_
 open local-inductive-definitions L β h
 open is-basis h

 _is-a-small-cover-of_ : (X : 𝓥 ̇ ) → (Y : 𝓦 ̇ ) → 𝓥 ⊔ 𝓦 ̇
 X is-a-small-cover-of Y = X ↠ Y

 has-a-bound : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → 𝓤 ⊔ 𝓣 ⊔ (𝓥 ⁺) ̇
 has-a-bound ϕ = Σ I ꞉ 𝓥 ̇ , Σ α ꞉ (I → 𝓥 ̇ ) ,
                 ((a : ⟨ L ⟩)
               → (b : B)
               → (b , a) ∈ ϕ
               → (Ǝ i ꞉ I , α i is-a-small-cover-of ↓ᴮ L β a) holds)

 bound-index : {ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)} → has-a-bound ϕ → 𝓥 ̇
 bound-index (I , α , covering) = I

 bound-family : {ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)}
              → (bnd : has-a-bound ϕ)
              → (bound-index {ϕ} bnd → 𝓥 ̇ )
 bound-family (I , α , covering) = α

 covering-condition : {ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)}
                    → (bnd : has-a-bound ϕ)
                    → ((a : ⟨ L ⟩)
                    → (b : B)
                    → (b , a) ∈ ϕ
                    → (Ǝ i ꞉ (bound-index {ϕ} bnd) ,
                       ((bound-family {ϕ} bnd) i is-a-small-cover-of ↓ᴮ L β a))
                        holds)
 covering-condition (I , α , covering) = covering

 is-bounded : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → 𝓤 ⊔ 𝓣 ⊔ (𝓥 ⁺) ̇
 is-bounded ϕ = ((a : ⟨ L ⟩) → (b : B) → ((b , a) ∈ ϕ) is 𝓥 small)
              × (has-a-bound ϕ)

 bounded-implies-local : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                       → is-bounded ϕ
                       → is-local ϕ
 bounded-implies-local ϕ (ϕ-small , ϕ-has-bound) a =
  smallness-closed-under-≃ S₀-is-small S₀-equiv-↓
  where
   I : 𝓥 ̇
   I = bound-index {ϕ} ϕ-has-bound
   α : I → 𝓥 ̇
   α = bound-family {ϕ} ϕ-has-bound
   cov : (a : ⟨ L ⟩)
       → (b : B)
       → (b , a) ∈ ϕ
       → (Ǝ i ꞉ I , (α i is-a-small-cover-of ↓ᴮ L β a)) holds
   cov = covering-condition {ϕ} ϕ-has-bound
   S₀ : 𝓤 ⊔ 𝓣 ⊔ 𝓥 ̇
   S₀ = Σ b ꞉ B , (Ǝ i ꞉ I , (Σ m ꞉ (α i → ↓ᴮ L β a) ,
                  (b , ⋁ (α i , ↓ᴮ-inclusion L β a ∘ m)) ∈ ϕ)) holds
   S₀-is-small : S₀ is 𝓥 small
   S₀-is-small =
    Σ-is-small
     (B , ≃-refl B)
      (λ b → ∥∥-is-small pt
             (Σ-is-small (I , ≃-refl I)
              (λ i → Σ-is-small
               (Π-is-small fe' (α i , ≃-refl (α i))
                (λ _ → ↓ᴮ-is-small))
               (λ m → ϕ-small (⋁ (α i , ↓ᴮ-inclusion L β a ∘ m)) b))))

   S₀-to-↓ : S₀ → ϕ ↓ a
   S₀-to-↓ (b , e) = (b , ∥∥-functor u e)
    where
     u : Σ i ꞉ I , Σ m ꞉ (α i → ↓ᴮ L β a) ,
         (b , (⋁ (α i , ↓ᴮ-inclusion L β a ∘ m))) ∈ ϕ
       → Σ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds
     u (i , m , p) =
      (⋁ (α i , ↓ᴮ-inclusion L β a ∘ m) , p ,
       join-is-least-upper-bound-of L (α i , ↓ᴮ-inclusion L β a ∘ m)
                                    (a , λ z → is-upper-bound-↓ a (m z)))

   ↓-to-S₀ : ϕ ↓ a → S₀
   ↓-to-S₀ (b , e) = (b , t e)
    where
     g : (a' : ⟨ L ⟩)
       → (b , a') ∈ ϕ
       → (a' ≤ a) holds
       → Σ i ꞉ I , (α i is-a-small-cover-of ↓ᴮ L β a')
       → Σ i ꞉ I , (Σ m ꞉ (α i → ↓ᴮ L β a) ,
          (b , ⋁ (α i , ↓ᴮ-inclusion L β a ∘ m)) ∈ ϕ)
     g a' p o (i , α-covers) = (i , m , in-ϕ)
      where
       inclusion : (a' : ⟨ L ⟩) → (a' ≤ a) holds → ↓ᴮ L β a' → ↓ᴮ L β a
       inclusion a' o (x , r) = (x , transitivity-of L (β x) a' a r o)
       m : α i → ↓ᴮ L β a
       m = inclusion a' o ∘ ⌞ α-covers ⌟
       path : a' ＝ ⋁ (α i , ↓ᴮ-inclusion L β a ∘ m)
       path = reindexing-along-surj-＝-sup
               L α-covers (β ∘ pr₁)
               a' (⋁ (α i , ↓ᴮ-inclusion L β a ∘ m)) (↓-is-sup a')
               (join-is-lub-of L (α i , ↓ᴮ-inclusion L β a ∘ m))
       in-ϕ : (b , ⋁ (α i , ↓ᴮ-inclusion L β a ∘ m)) ∈ ϕ
       in-ϕ = transport (λ z → (b , z) ∈ ϕ) path p
     trunc-g : (a' : ⟨ L ⟩)
             → (b , a') ∈ ϕ
             → (a' ≤ a) holds
             → (Ǝ i ꞉ I , (α i is-a-small-cover-of ↓ᴮ L β a')) holds
             → (Ǝ i ꞉ I , (Σ m ꞉ (α i → ↓ᴮ L β a) ,
                 (b , ⋁ (α i , ↓ᴮ-inclusion L β a ∘ m)) ∈ ϕ)) holds
     trunc-g a' p o = ∥∥-functor (g a' p o)
     cur-trunc-g : Σ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds
                 → (Ǝ i ꞉ I , Σ m ꞉ (α i → ↓ᴮ L β a)
                   , (b , ⋁ (α i , ↓ᴮ-inclusion L β a ∘ m)) ∈ ϕ) holds
     cur-trunc-g (a' , p , o) = trunc-g a' p o (cov a' b p)
     t : (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
       → (Ǝ i ꞉ I , Σ m ꞉ (α i → ↓ᴮ L β a) ,
           (b , ⋁ (α i , ↓ᴮ-inclusion L β a ∘ m)) ∈ ϕ) holds
     t = ∥∥-rec ∥∥-is-prop cur-trunc-g

   S₀-equiv-↓ : S₀ ≃ ϕ ↓ a
   S₀-equiv-↓ = (S₀-to-↓ , qinvs-are-equivs S₀-to-↓ is-qinv)
    where
     H : ↓-to-S₀ ∘ S₀-to-↓ ∼ id
     H (b , e) = to-subtype-＝ (λ _ → ∥∥-is-prop) refl
     G : S₀-to-↓ ∘ ↓-to-S₀ ∼ id
     G (b , e) = to-subtype-＝ (λ _ → ∥∥-is-prop) refl
     is-qinv : qinv S₀-to-↓
     is-qinv = (↓-to-S₀ , H , G)

\end{code}

We now consider a presentation restriction on sup-lattices stronger than
having a basis.

A sup-lattice has a small presentation if there is a small indexed family of
subsets that can be substituted for arbitrary subsets in a sense to be made
precise below.

\begin{code}

module small-presentation-of-lattice
        {𝓤 𝓣 𝓥 : Universe}
        {B : 𝓥 ̇ }
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        (β : B → ⟨ L ⟩)
        (h : is-basis L β)
       where

 private
  _≤_ = order-of L
  ⋁_ = join-of L

 open Joins _≤_
 open PropositionalTruncation pt
 open is-basis h

 _is-a-small-presentation :
  Σ J ꞉ 𝓥 ̇ , (J → 𝓟 {𝓥} B) × 𝓟 {𝓥} (B × 𝓟 {𝓥} B) → (𝓥 ⁺) ̇
 (J , Y , R) is-a-small-presentation = (b : B)
                                     → (X : 𝓟 {𝓥} B)
                                     → b ≤ᴮ (⋁ 【 β , X 】)
                                     ≃ ((Ǝ j ꞉ J , Y j ⊆ X × (b , Y j) ∈ R)
                                        holds)

 has-small-presentation : (𝓥 ⁺) ̇
 has-small-presentation =
  Σ 𝓡 ꞉ Σ J ꞉ 𝓥 ̇ , (J → 𝓟 {𝓥} B) × 𝓟 {𝓥} (B × 𝓟 {𝓥} B)
                  , 𝓡 is-a-small-presentation

\end{code}

We will now define, in the context of bounded ϕ and small-presentation 𝓡, a
new QIT family that is equivalent to 𝓘nd. Our constructors should be familiar
but notice the bounded and small-presentation assumptions allow us to avoid
large quantification!

\begin{code}

module _
        {𝓤 𝓣 𝓥 : Universe}
        {B : 𝓥 ̇ }
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        (β : B → ⟨ L ⟩)
        (h : is-basis L β)
       where

 private
  _≤_ = order-of L
  ⋁_ = join-of L

 open bounded-inductive-definitions L β h
 open small-presentation-of-lattice L β h
 open is-basis h

 module small-QIT-from-bounded-and-small-presentation
         (small-pres : has-small-presentation)
         (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
         (bnd : is-bounded ϕ)
        where

  I₁ : 𝓥 ̇
  I₁ = pr₁ (pr₁ small-pres)

  Y : I₁ → 𝓟 {𝓥} B
  Y = pr₁ (pr₂ (pr₁ small-pres))

  R : 𝓟 {𝓥} (B × 𝓟 {𝓥} B)
  R = pr₂ (pr₂ (pr₁ small-pres))

  is-small-pres : (I₁ , Y , R) is-a-small-presentation
  is-small-pres = pr₂ small-pres

  is-small-pres-forward : (b : B)
                         → (X : 𝓟 {𝓥} B)
                         → b ≤ᴮ (⋁ 【 β , X 】)
                         → ((Ǝ j ꞉ I₁ , Y j ⊆ X × (b , Y j) ∈ R) holds)
  is-small-pres-forward b X = ⌜ is-small-pres b X ⌝

  is-small-pres-backward : (b : B)
                         → (X : 𝓟 {𝓥} B)
                         → ((Ǝ j ꞉ I₁ , Y j ⊆ X × (b , Y j) ∈ R) holds)
                         → b ≤ᴮ (⋁ 【 β , X 】)
  is-small-pres-backward b X = ⌜ is-small-pres b X ⌝⁻¹

  ϕ-is-small : (a : ⟨ L ⟩) → (b : B) → ((b , a) ∈ ϕ) is 𝓥 small
  ϕ-is-small = pr₁ bnd

  small-ϕ : (b : B) → (a : ⟨ L ⟩) → 𝓥 ̇
  small-ϕ b a = pr₁ (ϕ-is-small a b)

  small-ϕ-equiv-ϕ : (a : ⟨ L ⟩) → (b : B) → small-ϕ b a ≃ (b , a) ∈ ϕ
  small-ϕ-equiv-ϕ a b = pr₂ (ϕ-is-small a b)

  ϕ-is-small-forward : (a : ⟨ L ⟩) → (b : B) → small-ϕ b a → (b , a) ∈ ϕ
  ϕ-is-small-forward a b = ⌜ small-ϕ-equiv-ϕ a b  ⌝

  ϕ-is-small-backward : (a : ⟨ L ⟩) → (b : B) → (b , a) ∈ ϕ → small-ϕ b a
  ϕ-is-small-backward a b = ⌜ small-ϕ-equiv-ϕ a b ⌝⁻¹

  I₂ : 𝓥 ̇
  I₂ = pr₁ (pr₂ bnd)

  α : I₂ → 𝓥 ̇
  α = pr₁ (pr₂ (pr₂ bnd))

  cover-condition : ((a : ⟨ L ⟩)
                  → (b : B)
                  → (b , a) ∈ ϕ
                  → (Ǝ i ꞉ I₂ , α i is-a-small-cover-of ↓ᴮ L β a) holds)
  cover-condition = pr₂ (pr₂ (pr₂ bnd))

\end{code}

The following serves as evidence that the desired QIT family is small (and
atleast has strictly positive point constructors).

\begin{code}

  data Small-Ind-Check : B → 𝓥 ̇ where
   Small-c-cl' : (i : I₁)
               → ((b : B) → (b ∈ Y i → Small-Ind-Check b))
               → (b : B) → (b , Y i) ∈ R
               → Small-Ind-Check b
   Small-ϕ-cl' : (i : I₂)
               → (m : α i → B)
               → (b : B)
               → small-ϕ b (⋁ (α i , β ∘ m))
               → ((b' : B) → (b' ≤ᴮ (⋁ (α i , β ∘ m)) → Small-Ind-Check b'))
               → Small-Ind-Check b

\end{code}

Again, we use records to assert the existence of another QIT family with
apropriate 'intiality' principle. As before we will first introduce some
names for the closure properties.

\begin{code}

  Small-c-closure : {𝓦 : Universe} (S : 𝓟 {𝓦} B) → 𝓥 ⊔ 𝓦 ̇
  Small-c-closure S = (i : I₁)
                    → ((b : B) → (b ∈ Y i → b ∈ S))
                    → (b : B) → (b , Y i) ∈ R
                    → b ∈ S

  Small-ϕ-closure : {𝓦 : Universe} (S : 𝓟 {𝓦} B) → 𝓥 ⊔ 𝓦 ̇
  Small-ϕ-closure S = (i : I₂)
                    → (m : α i → B)
                    → (b : B)
                    → small-ϕ b (⋁ (α i , β ∘ m))
                    → ((b' : B) → (b' ≤ᴮ (⋁ (α i , β ∘ m)) → b' ∈ S))
                    → b ∈ S

  record inductively-generated-small-subset-exists : 𝓤ω where
   constructor
    inductively-generated-small-subset

   field
    Small-Ind : B → 𝓥 ̇
    Small-Ind-trunc : (b : B) → is-prop (Small-Ind b)
   private
    Small-𝓘 : 𝓟 {𝓥} B
    Small-𝓘 b = (Small-Ind b , Small-Ind-trunc b)
   field
    Small-c-cl : Small-c-closure Small-𝓘
    Small-ϕ-cl : Small-ϕ-closure Small-𝓘
    Small-Ind-Initial : (P : 𝓟 {𝓦} B)
                      → Small-c-closure P
                      → Small-ϕ-closure P
                      → Small-𝓘 ⊆ P

  module small-trunc-ind-def
          (ind-e : inductively-generated-small-subset-exists)
         where

   open inductively-generated-small-subset-exists ind-e

   Small-𝓘nd : 𝓟 {𝓥} B
   Small-𝓘nd b = (Small-Ind b , Small-Ind-trunc b)

   Small-𝓘nd-is-c-cl : Small-c-closure Small-𝓘nd
   Small-𝓘nd-is-c-cl = Small-c-cl

   Small-𝓘nd-is-ϕ-cl : Small-ϕ-closure Small-𝓘nd
   Small-𝓘nd-is-ϕ-cl = Small-ϕ-cl

   Small-𝓘nd-Initial : (P : 𝓟 {𝓦} B)
                     → Small-c-closure P
                     → Small-ϕ-closure P
                     → Small-𝓘nd ⊆ P
   Small-𝓘nd-Initial = Small-Ind-Initial

\end{code}

We will now show that under the assumptions of small presentation and bounded
ϕ that

  b ∈ Small-𝓘nd ≃ b ∈ 𝓘nd.

We make essential use of the initiality of both types here.

This will allow us to satisfy the smallness conditions needed to salvage the
least fixed point theorem.

\begin{code}

module _
        {𝓤 𝓣 𝓥 : Universe}
        {B : 𝓥 ̇ }
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        (β : B → ⟨ L ⟩)
        (h : is-basis L β)
       where

 private
  _≤_ = order-of L
  ⋁_ = join-of L

 open bounded-inductive-definitions L β h
 open small-presentation-of-lattice L β h
 open is-basis h

 module 𝓘nd-is-small-from-bounded-and-small-presentation
         (small-pres : has-small-presentation)
         (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
         (bnd : is-bounded ϕ)
        where

  open small-QIT-from-bounded-and-small-presentation L β h small-pres ϕ bnd

  module 𝓘nd-is-small-QITs-exists
          (ind-e : inductively-generated-subset-exists L β h ϕ)
          (ind-e' : inductively-generated-small-subset-exists)
         where

   open trunc-ind-def L β h ϕ ind-e
   open small-trunc-ind-def ind-e'

   𝓘nd-⊆-Small-𝓘nd : 𝓘nd ⊆ Small-𝓘nd
   𝓘nd-⊆-Small-𝓘nd = 𝓘nd-is-initial Small-𝓘nd is-c-cl is-ϕ-cl
    where
     is-c-cl : (U : 𝓟 {𝓥} B)
             → U ⊆ Small-𝓘nd
             → (b : B)
             → b ≤ᴮ (⋁ 【 β , U 】)
             → b ∈ Small-𝓘nd
     is-c-cl U C b o = trunc-u (is-small-pres-forward b U o)
      where
       u : (Σ j ꞉ I₁ , Y j ⊆ U × (b , Y j) ∈ R)
         → b ∈ Small-𝓘nd
       u (j , C' , r) = Small-𝓘nd-is-c-cl j (λ x → λ y → C x (C' x y)) b r
       trunc-u : (Ǝ j ꞉ I₁ , Y j ⊆ U × (b , Y j) ∈ R) holds
               → b ∈ Small-𝓘nd
       trunc-u = ∥∥-rec (holds-is-prop (Small-𝓘nd b)) u
     is-ϕ-cl : (a : ⟨ L ⟩)
             → (b : B)
             → (b , a) ∈ ϕ
             → ((b' : B) → b' ≤ᴮ a → b' ∈ Small-𝓘nd)
             → b ∈ Small-𝓘nd
     is-ϕ-cl a b p C = trunc-u (cover-condition a b p)
      where
       u : Σ i ꞉ I₂ , α i is-a-small-cover-of ↓ᴮ L β a → b ∈ Small-𝓘nd
       u (i , s) =
        Small-𝓘nd-is-ϕ-cl i (↓ᴮ-to-base L β a ∘ ⌞ s ⌟) b
         (ϕ-is-small-backward (⋁ (α i , ↓ᴮ-inclusion L β a ∘ ⌞ s ⌟))
                              b (transport (λ - → (b , -) ∈ ϕ) (a-＝-⋁-α) p))
         (λ b' → C b' ∘ (transport (λ - → b' ≤ᴮ -) (a-＝-⋁-α ⁻¹)))
        where
         a-＝-⋁-α : a ＝ ⋁ (α i , ↓ᴮ-inclusion L β a ∘ ⌞ s ⌟)
         a-＝-⋁-α =
          reindexing-along-surj-＝-sup
           L s (↓ᴮ-inclusion L β a) a (⋁ (α i , ↓ᴮ-inclusion L β a ∘ ⌞ s ⌟))
           (↓-is-sup a) (join-is-lub-of L (α i , ↓ᴮ-inclusion L β a ∘ ⌞ s ⌟))
       trunc-u : (Ǝ i ꞉ I₂ , α i is-a-small-cover-of ↓ᴮ L β a) holds
               → b ∈ Small-𝓘nd
       trunc-u = ∥∥-rec (holds-is-prop (Small-𝓘nd b)) u

   Small-𝓘nd-⊆-𝓘nd : Small-𝓘nd ⊆ 𝓘nd
   Small-𝓘nd-⊆-𝓘nd = Small-𝓘nd-Initial 𝓘nd is-small-c-cl is-small-ϕ-cl
    where
     is-small-c-cl : (i : I₁)
                   → Y i ⊆ 𝓘nd
                   → (b : B)
                   → (b , Y i) ∈ R
                   → b ∈ 𝓘nd
     is-small-c-cl i C b r =
      𝓘nd-is-c-closed (Y i) C b
                      (is-small-pres-backward b (Y i) ∣ (i , (λ _ → id) , r) ∣)
     is-small-ϕ-cl : (i : I₂)
                   → (m : α i → B)
                   → (b : B)
                   → small-ϕ b (⋁ (α i , β ∘ m))
                   → ((x : B) → x ≤ᴮ (⋁ (α i , β ∘ m)) → x ∈ 𝓘nd)
                   → b ∈ 𝓘nd
     is-small-ϕ-cl i m b s C =
      𝓘nd-is-ϕ-closed (⋁ (α i , β ∘ m)) b
                      (ϕ-is-small-forward (⋁ (α i , β ∘ m)) b s) C

   𝓘nd-is-small : (b : B) → (b ∈ 𝓘nd) is 𝓥 small
   𝓘nd-is-small b = (b ∈ Small-𝓘nd , small-𝓘nd-equiv-𝓘nd)
    where
     small-𝓘nd-equiv-𝓘nd : b ∈ Small-𝓘nd ≃ b ∈ 𝓘nd
     small-𝓘nd-equiv-𝓘nd = logically-equivalent-props-are-equivalent
                            (holds-is-prop (Small-𝓘nd b))
                            (holds-is-prop (𝓘nd b))
                            (Small-𝓘nd-⊆-𝓘nd b)
                            (𝓘nd-⊆-Small-𝓘nd b)

\end{code}

As a corollary of the above result we get a predicative version of the least
fixed point theorem. Notice that we are assuming our sup-lattice is
small-presented and that we have a bounded ϕ that corresponds to our
monotone map. This is the most general statement that can be made but we are
actively exploring other, cleaner, formulations. In particular see the below
notion of density which makes no mention of a particular inductive definition.

Least fixed point theorem:
Given a 𝓥-sup-lattice L with a 𝓥-presentation and a monotone
endomap f : L → L. If there exists a bounded abstract inductive definition
ϕ such that f ＝ Γ ϕ, then f has a least fixed point.

\begin{code}

module _
        {𝓤 𝓣 𝓥 : Universe}
        {B : 𝓥 ̇ }
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        (β : B → ⟨ L ⟩)
        (h : is-basis L β)
       where

 private
  _≤_ = order-of L
  ⋁_ = join-of L

 open local-inductive-definitions L β h
 open bounded-inductive-definitions L β h
 open small-presentation-of-lattice L β h
 open small-QIT-from-bounded-and-small-presentation L β h

 module QITs-exists-for-all-ϕ
         (ind-e : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                → inductively-generated-subset-exists L β h ϕ)
         (ind'-e : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                 → (bnd : is-bounded ϕ)
                 → (small-pres : has-small-presentation)
                 → inductively-generated-small-subset-exists small-pres ϕ bnd)
        where

\end{code}

We first present the untruncated least fixed point theorem.

\begin{code}

  Untruncated-Least-Fixed-Point-Theorem : (small-pres : has-small-presentation)
                                        → (f : ⟨ L ⟩ → ⟨ L ⟩)
                                        → (f-mono : is-monotone-endomap L f)
                                        → Σ ϕ ꞉ 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩) ,
                                          Σ bnd ꞉ is-bounded ϕ , ((x : ⟨ L ⟩)
                                         → (Γ ϕ (bounded-implies-local ϕ bnd)) x
                                         ＝ f x)
                                        → has-least-fixed-point L f
  Untruncated-Least-Fixed-Point-Theorem small-pres f f-mono (ϕ , bnd , H) =
   transport (λ g → Σ x ꞉ ⟨ L ⟩ , (g x ＝ x) × ((a : ⟨ L ⟩)
                                             → (g a ＝ a)
                                             → (x ≤ a) holds))
             path Γ-has-least-fixed-point
   where
    open correspondance-from-locally-small-ϕ L β h ϕ
                                             (bounded-implies-local ϕ bnd)
    open small-𝓘nd-from-exists (ind-e ϕ)
    open 𝓘nd-is-small-from-bounded-and-small-presentation L β h small-pres ϕ bnd
    open small-QIT-from-bounded-and-small-presentation L β h small-pres ϕ bnd
    open 𝓘nd-is-small-QITs-exists (ind-e ϕ) (ind'-e ϕ bnd small-pres)
    open smallness-assumption 𝓘nd-is-small
    path : Γ ϕ (bounded-implies-local ϕ bnd) ＝ f
    path = dfunext fe H

\end{code}

We can now state the (truncated) least fixed point theorem.

\begin{code}

  Least-Fixed-Point-Theorem : (small-pres : has-small-presentation)
                            → (f : ⟨ L ⟩ → ⟨ L ⟩)
                            → (f-mono : is-monotone-endomap L f)
                            → (Ǝ ϕ ꞉ 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩) ,
                               Σ bnd ꞉ is-bounded ϕ ,
                               ((x : ⟨ L ⟩)
                               → (Γ ϕ (bounded-implies-local ϕ bnd)) x ＝ f x))
                                   holds
                            → has-least-fixed-point L f
  Least-Fixed-Point-Theorem small-pres f f-mono =
    ∥∥-rec (has-least-fixed-point-is-prop L f)
           (Untruncated-Least-Fixed-Point-Theorem small-pres f f-mono)

\end{code}

We now explore conditions on monotone endomaps that guarantee they
correspond to some bounded inductive definition. We tentatively call this
notion 'density'.

A monotone map f, on a 𝓥-generated sup-lattice L, is dense if there is a family
γ : I → L, I : 𝓥, such that for all b : B and a : L we have

  b ≤ᴮ f a → (Ǝ v ꞉ I , b ≤ᴮ f (γ v) × v ≤ᴮ a)

\begin{code}

module _
        {𝓤 𝓣 𝓥 : Universe}
        {B : 𝓥 ̇ }
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        (β : B → ⟨ L ⟩)
        (h : is-basis L β)
       where

 private
  _≤_ = order-of L
  ⋁_ = join-of L

 open local-inductive-definitions L β h
 open bounded-inductive-definitions L β h
 open is-basis h

 density-condition : (f : ⟨ L ⟩ → ⟨ L ⟩)
                   → (I : 𝓥 ̇ )
                   → (γ : I → ⟨ L ⟩)
                   → 𝓤 ⊔ 𝓣 ⊔ 𝓥 ̇
 density-condition f I γ = (b : B)
                         → (a : ⟨ L ⟩)
                         → b ≤ᴮ f a
                         → (Ǝ i ꞉ I , b ≤ᴮ f (γ i) × (γ i ≤ a) holds) holds

 is-dense : (f : ⟨ L ⟩ → ⟨ L ⟩) → 𝓤 ⊔ 𝓣 ⊔ (𝓥 ⁺) ̇
 is-dense f = Σ I ꞉ 𝓥 ̇ , Σ γ ꞉ (I → ⟨ L ⟩) , density-condition f I γ

 module _ (l-small : ⟨ L ⟩ is-locally 𝓥 small) where

  private
   _＝ˢ_ : ⟨ L ⟩ → ⟨ L ⟩ → 𝓥 ̇
   x ＝ˢ y = resized (x ＝ y) (l-small x y)

   ＝ˢ-equiv-＝ : {x y : ⟨ L ⟩} → (x ＝ˢ y) ≃ (x ＝ y)
   ＝ˢ-equiv-＝ {x} {y} = resizing-condition (l-small x y)

   ＝ˢ-to-＝ : {x y : ⟨ L ⟩} → (x ＝ˢ y) → (x ＝ y)
   ＝ˢ-to-＝ = ⌜ ＝ˢ-equiv-＝ ⌝

   ＝-to-＝ˢ : {x y : ⟨ L ⟩} → (x ＝ y) → (x ＝ˢ y)
   ＝-to-＝ˢ = ⌜ ＝ˢ-equiv-＝ ⌝⁻¹

   ＝ˢ-refl : {x : ⟨ L ⟩} → x ＝ˢ x
   ＝ˢ-refl = ＝-to-＝ˢ refl

  dense-implies-bounded : (f : ⟨ L ⟩ → ⟨ L ⟩)
                        → is-monotone-endomap L f
                        → is-dense f
                        → Σ ϕ ꞉ 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩) ,
                          Σ bnd ꞉ is-bounded ϕ ,
                           ((a : ⟨ L ⟩)
                            → (Γ ϕ (bounded-implies-local ϕ bnd)) a ＝ f a)
  dense-implies-bounded f f-mono (I , γ , f-dense) = (ϕ , bnd , H)
   where
    ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)
    ϕ (b , a') =
     (Lift 𝓤 ((Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a') holds)
      , equiv-to-prop (Lift-≃ 𝓤 ((Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a') holds))
                      (holds-is-prop (Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a')))
    bnd : is-bounded ϕ
    bnd = (ϕ-small , (I , (λ z → small-↓ᴮ (γ z)) , covering-cond))
     where
      ϕ-small : (a : ⟨ L ⟩) → (b : B) → (ϕ (b , a) holds) is 𝓥 small
      ϕ-small a b = ((Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a) holds
                    , ≃-Lift 𝓤 ((Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a) holds))
      covering-cond : (a : ⟨ L ⟩)
                    → (b : B)
                    → (b , a) ∈ ϕ
                    → (Ǝ i ꞉ I , small-↓ᴮ (γ i) ↠ ↓ᴮ L β a) holds
      covering-cond a b = demote-equiv-to-surj ∘ transport-lemma ∘ unlift-ϕ
       where
        unlift-ϕ : (b , a) ∈ ϕ → (Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a) holds
        unlift-ϕ = ⌜ Lift-≃ 𝓤 ((Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a) holds) ⌝
        transport-lemma : (Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a) holds
                        → (Ǝ i ꞉ I , small-↓ᴮ (γ i) ≃ ↓ᴮ L β a) holds
        transport-lemma =
         ∥∥-rec (holds-is-prop (Ǝ i ꞉ I , small-↓ᴮ (γ i) ≃ ↓ᴮ L β a))
                (λ (i , o , eq)
                 → ∣ (i , transport (λ z → small-↓ᴮ (γ i) ≃ ↓ᴮ L β z)
                                    (＝ˢ-to-＝ eq)
                                    small-↓ᴮ-≃-↓ᴮ) ∣)
        demote-equiv-to-surj : (Ǝ i ꞉ I , small-↓ᴮ (γ i) ≃ ↓ᴮ L β a) holds
                             → (Ǝ i ꞉ I , small-↓ᴮ (γ i) ↠ ↓ᴮ L β a) holds
        demote-equiv-to-surj =
         ∥∥-functor (λ (i , f , f-is-equiv)
                     → (i , f , equivs-are-surjections f-is-equiv))

    H : (a : ⟨ L ⟩) → Γ ϕ (bounded-implies-local ϕ bnd) a ＝ f a
    H a = reindexing-along-equiv-＝-sup
           L ↓ᴮ-fa-equiv-↓ (β ∘ (↓-to-base ϕ a))
           (Γ ϕ (bounded-implies-local ϕ bnd) a) (f a)
           (sup-of-small-fam-is-lub L (β ∘ ↓-to-base ϕ a)
                                    (bounded-implies-local ϕ bnd a))
           (is-supᴮ (f a))
     where
      ↓ᴮ-fa-equiv-↓ : (small-↓ᴮ (f a)) ≃ (ϕ ↓ a)
      ↓ᴮ-fa-equiv-↓ = Σ-cong ↓ᴮ-fa-equiv
       where
        ↓ᴮ-fa-equiv : (b : B)
                    → b ≤ᴮ f a
                      ≃ (Ǝ a' ꞉ ⟨ L ⟩ ,
                         Lift 𝓤 ((Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a') holds)
                         × (a' ≤ a) holds) holds
        ↓ᴮ-fa-equiv b =
         logically-equivalent-props-are-equivalent
          ≤ᴮ-is-prop-valued
          (holds-is-prop (Ǝ a' ꞉ ⟨ L ⟩ ,
                         Lift 𝓤 ((Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a') holds)
                         × (a' ≤ a) holds))
          (↓ᴮ-fa-to b)
          (to-↓ᴮ-fa b)
         where
          ↓ᴮ-fa-to : (b : B)
                   → b ≤ᴮ f a
                   → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
          ↓ᴮ-fa-to b = ∥∥-functor (g ∘ u) ∘ f-dense b a
           where
            u : Σ i ꞉ I , b ≤ᴮ f (γ i) × (γ i ≤ a) holds
              → Σ a' ꞉ ⟨ L ⟩ ,
                (Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a') holds × (a' ≤ a) holds
            u (i , o , r) = (γ i , ∣ (i , o , ＝ˢ-refl) ∣ , r)
            g : Σ a' ꞉ ⟨ L ⟩ ,
                (Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a') holds × (a' ≤ a) holds
              → Σ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds
            g (a' , e , r) =
              (a' ,
               ⌜ ≃-Lift 𝓤 ((Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a') holds) ⌝ e , r)

          to-↓ᴮ-fa : (b : B)
                   → (Ǝ a' ꞉ ⟨ L ⟩ ,
                      (b , a') ∈ ϕ × (a' ≤ a) holds) holds
                   → b ≤ᴮ f a
          to-↓ᴮ-fa b = ∥∥-rec ≤ᴮ-is-prop-valued u ∘ ∥∥-functor g
           where
            u' : (a' : ⟨ L ⟩)
               → Σ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a'
               → (a' ≤ a) holds
               → b ≤ᴮ f a
            u' a' (i , r , path) o =
              ≤-to-≤ᴮ (transitivity-of L (β b) (f a') (f a)
                                       (transport (λ z → (β b ≤ z) holds)
                                                  (ap f (＝ˢ-to-＝ path))
                                                  (≤ᴮ-to-≤ r))
                                       (f-mono a' a o))
            trunc-u' : (a' : ⟨ L ⟩)
                     → (Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a') holds
                     → (a' ≤ a) holds
                     → b ≤ᴮ f a
            trunc-u' a' =
             ∥∥-rec (Π-is-prop fe (λ _ → ≤ᴮ-is-prop-valued)) (u' a')
            u : Σ a' ꞉ ⟨ L ⟩ ,
                (Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a') holds × (a' ≤ a) holds
              → b ≤ᴮ f a
            u = uncurry (λ a' → uncurry (trunc-u' a'))
            g : Σ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds
              → Σ a' ꞉ ⟨ L ⟩ ,
                (Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a') holds × (a' ≤ a) holds
            g (a' , e , r) =
              (a' ,
               ⌜ Lift-≃ 𝓤 ((Ǝ i ꞉ I , b ≤ᴮ f (γ i) × γ i ＝ˢ a') holds) ⌝ e , r)

\end{code}

We use the notion of density, along with the reasonable assumption that our
lattice is locally small, to state another version of the least fixed point
theorem.

\begin{code}

module _
        {𝓤 𝓣 𝓥 : Universe}
        {B : 𝓥 ̇ }
        (L : Sup-Lattice 𝓤 𝓣 𝓥)
        (β : B → ⟨ L ⟩)
        (h : is-basis L β)
       where

 open propositional-truncations-exist pt
 open bounded-inductive-definitions L β h
 open small-presentation-of-lattice L β h
 open small-QIT-from-bounded-and-small-presentation L β h

 module QITs-exists-density
         (ind-e : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                → inductively-generated-subset-exists L β h ϕ)
         (ind'-e : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                 → (bnd : is-bounded ϕ)
                 → (small-pres : has-small-presentation)
                 → inductively-generated-small-subset-exists small-pres ϕ bnd)
        where

  open QITs-exists-for-all-ϕ L β h ind-e ind'-e

  Least-Fixed-Point-Theorem-from-Density : has-small-presentation
                                         → ⟨ L ⟩ is-locally 𝓥 small
                                         → (f : ⟨ L ⟩ → ⟨ L ⟩)
                                         → is-monotone-endomap L f
                                         → is-dense L β h f
                                         → has-least-fixed-point L f
  Least-Fixed-Point-Theorem-from-Density small-pres l-small f f-mono f-dense =
   Untruncated-Least-Fixed-Point-Theorem small-pres f f-mono
    (dense-implies-bounded L β h l-small f f-mono f-dense)

\end{code}

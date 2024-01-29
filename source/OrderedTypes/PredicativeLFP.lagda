Ian Ray 01/09/2023.

We formalize Curi's notion of abstract inductive definition (in CZF) within
the context of a sup-lattice L with small basis B (and β : B → L). An abstract
inductive defintion is a subset ϕ : B × L → Prop which can be thought of as a
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

For a write up of the current formalization in a type theoretic setting see
https://arxiv.org/abs/2401.00841

We now state the main result for reference, although much of the context needs
to be developed:

Given a 𝓥-sup-lattice L with a 𝓥-presentation and a monotone
endomap f : L → L. If there exists a bounded abstract inductive definition
ϕ such that f ＝ Γ ϕ, then f has a least fixed point.

\begin{code}

{-# OPTIONS --safe --without-K --exact-split #-}

open import MLTT.Spartan
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Hedberg
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.PropTrunc
open import UF.Retracts
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.Size
open import UF.SmallnessProperties
open import UF.UniverseEmbedding

module OrderedTypes.PredicativeLFP
       (pt : propositional-truncations-exist)
       (fe : Fun-Ext)
       (fe' : FunExt)
       (pe : Prop-Ext)
        where

open import Locales.Frame pt fe hiding (⟨_⟩ ; join-of)
open import Slice.Family
open import UF.ImageAndSurjection pt
open import OrderedTypes.SupLattice pt fe fe' pe
open import OrderedTypes.SupLattice-SmallBasis pt fe fe' pe

open AllCombinators pt fe
open PropositionalTruncation pt

\end{code}

We commence this file by defining what it means for a monotone endomap to have
a least fixed point.

\begin{code}

module _ {𝓤 𝓦 𝓥 : Universe} (L : Sup-Lattice 𝓤 𝓦 𝓥) where

 has-least-fixed-point : (f : ⟨ L ⟩ → ⟨ L ⟩) → 𝓤 ⊔ 𝓦  ̇
 has-least-fixed-point f =  Σ p ꞉ ⟨ L ⟩ , (f p ＝ p) × ((a : ⟨ L ⟩)
                                                      → (f a ＝ a)
                                                      → (p ≤⟨ L ⟩ a) holds)

 has-least-fixed-point-is-prop : (f : ⟨ L ⟩ → ⟨ L ⟩)
                                → is-prop (has-least-fixed-point f) 
 has-least-fixed-point-is-prop f (p₁ , fp₁ , l₁) (p₂ , fp₂ , l₂) =
   to-subtype-＝
     (λ x → ×-is-prop
             (sethood-of L)
             (Π-is-prop fe (λ y → Π-is-prop
                                   fe (λ _ → holds-is-prop (x ≤⟨ L ⟩ y)))))
     (antisymmetry-of L (l₁ p₂ fp₂) (l₂ p₁ fp₁))

\end{code}

We construct the least closed subset of an inductive definition as a QIT.
Since HITs are not native in Agda we will instead assume the existence of such
a type as well as its induction principle. Technically speaking we are going
to use record types to package the contents of this HIT. See below:
  record inductively-generated-subset-exists

Notice that the QIT has two constructors which representing the closure
conditions we wish to impose on subsets. The c-closure condition says:
for any subset contained in the least closed subset, elements in the downset of
its join are in the least closed subset as well. That is, Y is c-closed if
  for any U ⊆ Y we have ↓ᴮ (⋁ U) ⊆ Y.
The ϕ-cl constructor says:
if for any a : L and b : B with (b , a) ∈ ϕ and ↓ᴮ a 'contained' in the least
closed subset then b is in the least closed subset. That is, Y is ϕ-closed if
  for any a : L and b : B we have ↓ᴮ a ⊆ Y ⇒ b ∈ Y.

Note: It is worth noting that we don't encode the downsets as subsets in type
theory (rather they are total spaces) so for that reason we won't encode the
closure conditions exactly as above.

We also derive the initiality of the least closed subset from the postulated
induction principle. Initiality is closely related to the 'least' part of
our least fixed point theorem.

\begin{code}

module inductive-definitions {𝓤 𝓦 𝓥 : Universe}
                             {B : 𝓥  ̇}
                             (L : Sup-Lattice 𝓤 𝓦 𝓥)
                             (β : B → ⟨ L ⟩)
                              where

 open small-basis L β
 open Joins _≤_

 module ind-from-small-basis-facts (h : is-small-basis) where

  open small-basis-facts h

  record inductively-generated-subset-exists (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)): 𝓤ω
   where
   constructor
    inductively-generated-subset

   field
    Ind : B → 𝓤 ⊔ 𝓥 ⁺  ̇
    Ind-trunc : (b : B) → is-prop (Ind b)
    c-closed : (U : 𝓟 {𝓥} B)
             → ((b : B) → (b ∈ U → Ind b))
             → (b : B) → b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))
             → Ind b
    ϕ-closed : (a : ⟨ L ⟩)
             → (b : B)
             → (b , a) ∈ ϕ
             → ((b' : B) → (b' ≤ᴮ a → Ind b'))
             → Ind b
    Ind-induction : (P : (b : B) → 𝓟 {𝓣} (Ind b))
                  → ((U : 𝓟 {𝓥} B) → (f : (x : B) → (x ∈ U → Ind x))
                   → ((x : B) → (u : x ∈ U) → f x u ∈ P x)
                   → (b : B)
                   → (g : (b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))))
                   → c-closed U f b g ∈ P b)
                  → ((a : ⟨ L ⟩)
                   → (b : B)
                   → (p : (b , a) ∈ ϕ)
                   → (f : (x : B) → (x ≤ᴮ a → Ind x))
                   → ((x : B) → (o : x ≤ᴮ a) → f x o ∈ P x)
                   → ϕ-closed a b p f ∈ P b)
                  → (b : B) → (i : Ind b) → i ∈ P b

  module trunc-ind-def (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                       (ind-e : inductively-generated-subset-exists ϕ)
                        where

   open inductively-generated-subset-exists ind-e

   𝓘nd : 𝓟 {𝓤 ⊔ 𝓥 ⁺} B
   𝓘nd b = (Ind b , Ind-trunc b)

   𝓘nd-is-c-closed : (U : 𝓟 {𝓥} B)
                   → (U ⊆ 𝓘nd)
                   → (b : B) → b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))
                   → b ∈ 𝓘nd
   𝓘nd-is-c-closed = c-closed

   𝓘nd-is-ϕ-closed : (a : ⟨ L ⟩)
                   → (b : B)
                   → (b , a) ∈ ϕ
                   → ((b' : B) → (b' ≤ᴮ a → b' ∈ 𝓘nd))
                   → b ∈ 𝓘nd
   𝓘nd-is-ϕ-closed = ϕ-closed

   𝓘nd-induction : (P : (b : B) → 𝓟 {𝓣} (b ∈ 𝓘nd))
                 → ((U : 𝓟 {𝓥} B) → (f : U ⊆ 𝓘nd)
                  → ((x : B) → (u : x ∈ U) → f x u ∈ P x)
                  → (b : B) → (g : (b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))))
                  → c-closed U f b g ∈ P b)
                 → ((a : ⟨ L ⟩)
                  → (b : B)
                  → (p : (b , a) ∈ ϕ)
                  → (f : (x : B) → (x ≤ᴮ a → x ∈ 𝓘nd))
                  → ((x : B) → (o : x ≤ᴮ a) → f x o ∈ P x)
                  → ϕ-closed a b p f ∈ P b)
                 → (b : B) → (i : b ∈ 𝓘nd) → i ∈ P b
   𝓘nd-induction = Ind-induction

   𝓘nd-recursion : (P : 𝓟 {𝓣} B)
                 → ((U : 𝓟 {𝓥} B)
                  → (U ⊆ 𝓘nd)
                  → (U ⊆ P)
                  → (b : B) → (b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U)))
                  → b ∈ P)
                 → ((a : ⟨ L ⟩)
                  → (b : B)
                  → (b , a) ∈ ϕ
                  → ((x : B) → (x ≤ᴮ a → x ∈ 𝓘nd))
                  → ((x : B) → (x ≤ᴮ a → x ∈ P))
                  → b ∈ P)
                 → 𝓘nd ⊆ P
   𝓘nd-recursion P = 𝓘nd-induction λ b → (λ _ → P b)

   𝓘nd-is-initial : (P : 𝓟 {𝓣} B)
                  → ((U : 𝓟 {𝓥} B)
                   → (U ⊆ P)
                   → ((b : B) → (b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U)))
                   → b ∈ P))
                  → ((a : ⟨ L ⟩)
                   → (b : B)
                   → (b , a) ∈ ϕ
                   → ((b' : B) → (b' ≤ᴮ a → b' ∈ P)) → b ∈ P)
                  → 𝓘nd ⊆ P
   𝓘nd-is-initial {𝓣} P IH₁ IH₂ b b-in-𝓘nd = 𝓘nd-recursion P R S b b-in-𝓘nd
    where
     R : (U : 𝓟 {𝓥} B)
       → U ⊆ 𝓘nd
       → U ⊆ P
       → (x : B) → x ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))
       →  x ∈ P
     R U C₁ C₂ x o = IH₁ U C₂ x o
     S : (a : ⟨ L ⟩)
       → (x : B)
       → (x , a) ∈ ϕ
       → ((z : B) → z ≤ᴮ a → z ∈ 𝓘nd)
       → ((z : B) → z ≤ᴮ a → z ∈ P)
       → x ∈ P
     S a x p f g = IH₂ a x p g

\end{code}

We now consider a restricted class of inductive definitions which we will call
local. A local inductive definition ϕ is one such that the type

  Σ b ꞉ B , (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a)

is small.

We then define an operator parameterized by local inductive definitions
and prove that it is monotone. Finally, we show that any monotone endo map on
the sup-lattice corresponds to a monotone operator and local inductive
definition.

\begin{code}

module local-inductive-definitions {𝓤 𝓦 𝓥 : Universe}
                                   {B : 𝓥  ̇}
                                   (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                   (β : B → ⟨ L ⟩)
                                    where

 open small-basis L β
 open Joins _≤_
 open inductive-definitions L β 

 module local-from-small-basis-facts (h : is-small-basis) where

  open small-basis-facts h

  S : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → (a : ⟨ L ⟩) → 𝓤 ⊔ 𝓦 ⊔ 𝓥  ̇
  S ϕ a = Σ b ꞉ B , (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds

  S-to-base : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → (a : ⟨ L ⟩) → S ϕ a → B
  S-to-base ϕ a = pr₁

  S-monotonicity-lemma : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                       → (x y : ⟨ L ⟩)
                       → (x ≤ y) holds
                       → S ϕ x → S ϕ y
  S-monotonicity-lemma ϕ x y o = I
   where
    I : S ϕ x → S ϕ y
    I (b , c) = (b , II c)
     where
      II : (Ǝ a' ꞉ ⟨ L ⟩ , ((b , a') ∈ ϕ) × ((a' ≤ x) holds)) holds
         → (Ǝ a' ꞉ ⟨ L ⟩ , ((b , a') ∈ ϕ) × ((a' ≤ y) holds)) holds
      II = ∥∥-functor III
       where
        III : Σ a' ꞉ ⟨ L ⟩ , ((b , a') ∈ ϕ) × ((a' ≤ x) holds)
            → Σ a' ꞉ ⟨ L ⟩ , ((b , a') ∈ ϕ) × ((a' ≤ y) holds)
        III (a' , p , r) = (a' , p , transitivity-of L a' x y r o)

  S-has-sup-implies-monotone : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                             → (x y s s' : ⟨ L ⟩)
                             → (x ≤ y) holds
                             → (s is-lub-of (S ϕ x , β ∘ S-to-base ϕ x)) holds
                             → (s' is-lub-of (S ϕ y , β ∘ S-to-base ϕ y)) holds
                             → (s ≤ s') holds
  S-has-sup-implies-monotone
    ϕ x y s s' o (is-upbnd , is-least-upbnd) (is-upbnd' , is-least-upbnd') =
     is-least-upbnd (s' , I)
   where
    I : (s' is-an-upper-bound-of (S ϕ x , β ∘ S-to-base ϕ x)) holds
    I (b , e) = is-upbnd' (S-monotonicity-lemma ϕ x y o ((b , e)))
        
  _is-local : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
  ϕ is-local = (a : ⟨ L ⟩) → S ϕ a is 𝓥 small

  module _ (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) (i : ϕ is-local) where

   private
    S' : (a : ⟨ L ⟩) → 𝓥  ̇
    S' a = resized (S ϕ a) (i a)

    S'-equiv-S : (a : ⟨ L ⟩) → S' a ≃ S ϕ a
    S'-equiv-S a  = resizing-condition (i a)

    S'-to-S : (a : ⟨ L ⟩) → S' a → S ϕ a
    S'-to-S a = ⌜ S'-equiv-S a ⌝

    S-to-S' : (a : ⟨ L ⟩) → S ϕ a → S' a 
    S-to-S' a = ⌜ S'-equiv-S a ⌝⁻¹

    S'-monotone-ish : (x y : ⟨ L ⟩)
                   → (x ≤ y) holds
                   → S' x
                   → S' y
    S'-monotone-ish x y o =
      S-to-S' y ∘ S-monotonicity-lemma ϕ x y o ∘ S'-to-S x

   Γ : ⟨ L ⟩ → ⟨ L ⟩
   Γ a = ⋁ (S' a , β ∘ pr₁ ∘ S'-to-S a)

   Γ-is-monotone : is-monotone L Γ
   Γ-is-monotone x y o =
     S-has-sup-implies-monotone ϕ x y (Γ x) (Γ y) o I II
    where
     I : (Γ x is-lub-of (S ϕ x , β ∘ S-to-base ϕ x)) holds
     I = sup-of-small-fam-is-lub L (β ∘ S-to-base ϕ x) (i x)      
     II : (Γ y is-lub-of (S ϕ y , β ∘ S-to-base ϕ y)) holds
     II = sup-of-small-fam-is-lub L (β ∘ S-to-base ϕ y) (i y)

  mono-map-give-local-ind-def : (f : ⟨ L ⟩ → ⟨ L ⟩)
                              → is-monotone L f
                              → Σ ϕ ꞉ 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩) ,
                                Σ i ꞉ (ϕ is-local) ,
                                ((x : ⟨ L ⟩) → (Γ ϕ i) x ＝ f x)
  mono-map-give-local-ind-def f f-mono = (ϕ , i , H)
   where
    ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)
    ϕ (b , a) = (Lift 𝓤 (b ≤ᴮ f a) ,
                 equiv-to-prop (Lift-≃ 𝓤 (b ≤ᴮ f a)) _≤ᴮ_-is-prop-valued )
    I : (a : ⟨ L ⟩) → small-↓ᴮ (f a) ≃ S ϕ a
    I a = Σ-cong' (λ z → z ≤ᴮ f a)
                        ((λ z → (Ǝ a' ꞉ ⟨ L ⟩ ,
                         (z , a') ∈ ϕ × (a' ≤ a) holds) holds)) II
     where
      II : (z : B)
         → (z ≤ᴮ f a) ≃ (Ǝ a' ꞉ ⟨ L ⟩ ,
                             (z , a') ∈ ϕ × (a' ≤ a) holds) holds
      II z = ⌜ prop-≃-≃-↔ fe _≤ᴮ_-is-prop-valued ∥∥-is-prop ⌝⁻¹
                  (III , IV)
       where
        III : z ≤ᴮ f a → (Ǝ a' ꞉ ⟨ L ⟩ , (z , a') ∈ ϕ × (a' ≤ a) holds) holds
        III o = ∣ (a , ⌜ ≃-Lift 𝓤 (z ≤ᴮ f a) ⌝ o , reflexivity-of L a) ∣
        IV : (Ǝ a' ꞉ ⟨ L ⟩ , (z , a') ∈ ϕ × (a' ≤ a) holds) holds → z ≤ᴮ f a
        IV = ∥∥-rec _≤ᴮ_-is-prop-valued V
         where
          V : Σ a' ꞉ ⟨ L ⟩ , (z , a') ∈ ϕ × (a' ≤ a) holds → z ≤ᴮ f a
          V (a' , o , r) =
             _≤_-to-_≤ᴮ_ (transitivity-of L (β z) (f a') (f a)
                                          (_≤ᴮ_-to-_≤_
                                            (⌜ ≃-Lift 𝓤 (z ≤ᴮ f a') ⌝⁻¹ o))
                                          (f-mono a' a r))
    i : ϕ is-local 
    i a = (small-↓ᴮ (f a) , I a)
    G : (x : ⟨ L ⟩) → (f x is-lub-of (S ϕ x , β ∘ S-to-base ϕ x)) holds 
    G x = (III , VI)
     where
      III : (f x is-an-upper-bound-of (S ϕ x , β ∘ S-to-base ϕ x)) holds
      III (b , e) = IV e
       where
        IV : (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ x) holds) holds
           → (β b ≤ f x) holds
        IV = ∥∥-rec (holds-is-prop (β b ≤ f x)) V
         where
          V : Σ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ x) holds
                → (β b ≤ f x) holds
          V (a' , o , r) = transitivity-of
                             L (β b) (f a') (f x)
                             (_≤ᴮ_-to-_≤_ (⌜ ≃-Lift 𝓤 (b ≤ᴮ f a') ⌝⁻¹ o))
                             (f-mono a' x r)
      VI : ((u , _) : upper-bound (S ϕ x , β ∘ S-to-base ϕ x))
         → (f x ≤ u) holds
      VI (u , is-upbnd) = (is-least-upper-boundᴮ (f x))
                                  (u , λ z → is-upbnd (⌜ I x ⌝ z))
    H : (x : ⟨ L ⟩) → (Γ ϕ i) x ＝ f x
    H x = reindexing-along-equiv-＝-sup
            L (id , id-is-equiv (S ϕ x)) (β ∘ S-to-base ϕ x)
            ((Γ ϕ i) x) (f x)
             (sup-of-small-fam-is-lub  L (β ∘ S-to-base ϕ x) (i x))
            (G x)

  ind-def-from-mono-map : (f : ⟨ L ⟩ → ⟨ L ⟩)
                        → is-monotone L f
                        → 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)
  ind-def-from-mono-map f f-mono = pr₁ (mono-map-give-local-ind-def f f-mono)

  local-from-mono-map : (f : ⟨ L ⟩ → ⟨ L ⟩)
                      → (f-mono : is-monotone L f)
                      → (ind-def-from-mono-map f f-mono) is-local
  local-from-mono-map f f-mono =
    pr₁ (pr₂ (mono-map-give-local-ind-def f f-mono))

  f-＝-Γ-from-mono-map : (f : ⟨ L ⟩ → ⟨ L ⟩)
                       → (f-mono : is-monotone L f)
                       → (x : ⟨ L ⟩)
                       → (Γ (ind-def-from-mono-map f f-mono)
                            (local-from-mono-map f f-mono)) x ＝ f x
  f-＝-Γ-from-mono-map f f-mono =
    pr₂ (pr₂ (mono-map-give-local-ind-def f f-mono))

\end{code}

We now spell out a correspondence between small 'closed' subsets and
deflationary points in our sup lattice. This will allow us to show that
monotone operators have a least fixed point under certain smallness
assumpions.

\begin{code}

module correspondance-small-ϕ-closed-types-def-points {𝓤 𝓦 𝓥 : Universe}
                                                      {B : 𝓥  ̇}
                                                      (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                                      (β : B → ⟨ L ⟩)
                                                       where

 open small-basis L β
 open Joins _≤_
 open inductive-definitions L β
 open local-inductive-definitions L β

 module correspondance-from-small-basis-facts (h : is-small-basis) where

  open small-basis-facts h
  open ind-from-small-basis-facts h
  open local-from-small-basis-facts h

  module correspondance-from-locally-small-ϕ (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                                             (i : ϕ is-local)
                                              where

   _is-small-ϕ-closed-subset : (P : 𝓟 {𝓥} B) → 𝓤 ⊔ (𝓥 ⁺)  ̇
   P is-small-ϕ-closed-subset = ((U : 𝓟 {𝓥} B)
                               → (U ⊆ P)
                               → ((b : B)
                               → b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))
                               → b ∈ P))
                              × ((a : ⟨ L ⟩)
                               → (b : B)
                               → (b , a) ∈ ϕ
                               → ((b' : B) → (b' ≤ᴮ a → b' ∈ P))
                               → b ∈ P)

   is-small-ϕ-closed-subset-is-predicate : (P : 𝓟 {𝓥} B)
                                         → is-prop (P is-small-ϕ-closed-subset)
   is-small-ϕ-closed-subset-is-predicate P =
     ×-is-prop (Π-is-prop fe λ U
                → Π-is-prop fe (λ C
                 → Π-is-prop fe (λ b
                  → Π-is-prop fe (λ f
                   → holds-is-prop (P b)))))
               (Π-is-prop fe (λ a
                → Π-is-prop fe (λ b
                 → Π-is-prop fe (λ p
                  → Π-is-prop fe (λ f
                   → holds-is-prop (P b))))))

   small-ϕ-closed-subsets : 𝓤 ⊔ (𝓥 ⁺)  ̇
   small-ϕ-closed-subsets =  Σ P ꞉ 𝓟 {𝓥} B , P is-small-ϕ-closed-subset

   subset-of-small-ϕ-closed-subset : small-ϕ-closed-subsets → 𝓟 {𝓥} B
   subset-of-small-ϕ-closed-subset (P , c-clsd , ϕ-clsd) = P

   c-closed-of-small-ϕ-closed-subset : (X : small-ϕ-closed-subsets)
                                     → ((U : 𝓟 {𝓥} B)
                                     → U ⊆ subset-of-small-ϕ-closed-subset X
                                     → ((b : B)
                                     → b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))
                                     → b ∈ subset-of-small-ϕ-closed-subset X))
   c-closed-of-small-ϕ-closed-subset (P , c-clsd , ϕ-clsd) = c-clsd

   ϕ-closed-of-small-ϕ-closed-subset : (X : small-ϕ-closed-subsets)
                                     → ((a : ⟨ L ⟩)
                                     → (b : B)
                                     → ((b , a) ∈ ϕ)
                                     → ((b' : B)
                                     → (b' ≤ᴮ a
                                     → b' ∈ subset-of-small-ϕ-closed-subset X))
                                     → b ∈ subset-of-small-ϕ-closed-subset X)
   ϕ-closed-of-small-ϕ-closed-subset (P , c-clsd , ϕ-clsd) = ϕ-clsd

   _is-non-inc : (a : ⟨ L ⟩) → 𝓦  ̇
   a is-non-inc = ((Γ ϕ i) a ≤ a) holds

   is-non-inc-is-predicate : (a : ⟨ L ⟩) → is-prop(a is-non-inc)
   is-non-inc-is-predicate a = holds-is-prop ((Γ ϕ i) a ≤ a)

   non-inc-points : 𝓤 ⊔ 𝓦  ̇
   non-inc-points = Σ a ꞉ ⟨ L ⟩ , (a is-non-inc)

   point-non-inc-points : non-inc-points → ⟨ L ⟩
   point-non-inc-points (a , non-inc) = a

   is-non-inc-non-inc-points : (X : non-inc-points)
                             → (point-non-inc-points X) is-non-inc
   is-non-inc-non-inc-points (a , non-inc) = non-inc

   small-ϕ-closed-subsets-to-non-inc-points : small-ϕ-closed-subsets
                                            → non-inc-points
   small-ϕ-closed-subsets-to-non-inc-points (P , c-closed , ϕ-closed) =
     (sup-of-P , sup-is-non-inc)
    where
     sup-of-P : ⟨ L ⟩
     sup-of-P = ⋁ (𝕋 P , β ∘ 𝕋-to-carrier P)
     sup-is-non-inc : sup-of-P is-non-inc
     sup-is-non-inc = lub-condition (sup-of-P , is-upper-bound)
      where
       sup-is-lub :
         ((Γ ϕ i) sup-of-P is-lub-of (S ϕ sup-of-P , β ∘ S-to-base ϕ sup-of-P))
                  holds
       sup-is-lub = sup-of-small-fam-is-lub
                    L (β ∘ S-to-base ϕ sup-of-P) (i sup-of-P)
       lub-condition :
         ((u , _) : upper-bound (S ϕ sup-of-P , β ∘ S-to-base ϕ sup-of-P))
         → ((Γ ϕ i) sup-of-P ≤ u) holds
       lub-condition = pr₂ sup-is-lub
       b-in-P-to-b-below-sup : (b : B) → b ∈ P → (β b ≤ sup-of-P) holds
       b-in-P-to-b-below-sup b b-in-P =
         (join-is-upper-bound-of L (𝕋 P , β ∘ 𝕋-to-carrier P)) (b , b-in-P)
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
           b'-below-sup-P = _≤_-to-_≤ᴮ_ (transitivity-of L (β b') a sup-of-P
                                                       (_≤ᴮ_-to-_≤_ r) o)
       is-upper-bound : ((b , e) : S ϕ sup-of-P) → (β b ≤ sup-of-P) holds
       is-upper-bound (b , e) = ∥∥-rec (holds-is-prop (β b ≤ sup-of-P))
                                       (un-trunc-map b) e

   non-inc-points-to-small-ϕ-closed-subsets : non-inc-points
                                            → small-ϕ-closed-subsets
   non-inc-points-to-small-ϕ-closed-subsets (a , is-non-inc) =
     (Q a , c-closed , ϕ-closed)
    where
     Q : (x : ⟨ L ⟩) → 𝓟 {𝓥} B
     Q x b = (b ≤ᴮ x , _≤ᴮ_-is-prop-valued)
     sup-Q_ : (x : ⟨ L ⟩) → ⟨ L ⟩
     sup-Q x = ⋁ (𝕋 (Q x) , β ∘ 𝕋-to-carrier (Q x))
     _is-sup-Q : (x : ⟨ L ⟩) → x ＝ sup-Q x
     x is-sup-Q = is-sup'ᴮ x
     c-closed : (U : 𝓟 {𝓥} B)
              → (U ⊆ Q a)
              → ((b : B) → (b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))) →  b ∈ Q a)
     c-closed U C b o = _≤_-to-_≤ᴮ_ (transitivity-of L (β b)
                                    (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))
                                    a
                                    (_≤ᴮ_-to-_≤_ o)
                                    (transport (λ z → ((⋁ (𝕋 U ,
                                      β ∘ 𝕋-to-carrier U)) ≤ z) holds)
                                               (a is-sup-Q ⁻¹)
                                               (joins-preserve-containment
                                                 L β {U} {Q a} C)))
     ϕ-closed : (a' : ⟨ L ⟩)
              → (b : B)
              → ((b , a') ∈ ϕ)
              → ((b' : B) → (b' ≤ᴮ a' → b' ∈ Q a)) → b ∈ Q a
     ϕ-closed a' b p f = trunc-map b ∣ (a' , p , a'-below-a) ∣
      where
       Γ-is-sup : ((Γ ϕ i) a is-lub-of (S ϕ a , β ∘ S-to-base ϕ a)) holds
       Γ-is-sup = sup-of-small-fam-is-lub
                    L (β ∘ S-to-base ϕ a) (i a)
       Γ-an-upper-bound :
         ((Γ ϕ i) a is-an-upper-bound-of (S ϕ a , β ∘ S-to-base ϕ a)) holds
       Γ-an-upper-bound = pr₁ Γ-is-sup
       trunc-map : (x : B)
                 → (Ǝ a'' ꞉ ⟨ L ⟩ , (x , a'') ∈ ϕ × (a'' ≤ a) holds) holds
                 → x ≤ᴮ a
       trunc-map x e = _≤_-to-_≤ᴮ_
                       (transitivity-of L (β x) ((Γ ϕ i) a) a
                                          (Γ-an-upper-bound (x , e))
                                          (is-non-inc))
       a'-below-a : (a' ≤ a) holds
       a'-below-a = transport (λ z → (z ≤ a) holds)
                          (a' is-sup-Q ⁻¹)
                          (transport (λ z → ((sup-Q a') ≤ z) holds)
                                            (a is-sup-Q ⁻¹)
                                            (joins-preserve-containment
                                              L β {Q a'} {Q a} f))

   small-ϕ-closed-subsets-≃-non-inc-points :
     small-ϕ-closed-subsets ≃ non-inc-points
   small-ϕ-closed-subsets-≃-non-inc-points =
     (small-ϕ-closed-subsets-to-non-inc-points ,
       qinvs-are-equivs small-ϕ-closed-subsets-to-non-inc-points is-qinv)
    where
     H : non-inc-points-to-small-ϕ-closed-subsets
       ∘ small-ϕ-closed-subsets-to-non-inc-points ∼ id
     H (P , c-closed , ϕ-closed) =
       to-subtype-＝ is-small-ϕ-closed-subset-is-predicate P'-is-P
      where
       sup-P : ⟨ L ⟩
       sup-P = point-non-inc-points
               (small-ϕ-closed-subsets-to-non-inc-points
                (P , c-closed , ϕ-closed))
       P' : 𝓟 {𝓥} B
       P' = subset-of-small-ϕ-closed-subset
             (non-inc-points-to-small-ϕ-closed-subsets
              (small-ϕ-closed-subsets-to-non-inc-points
               (P , c-closed , ϕ-closed)))
       P'-is-P : P' ＝ P
       P'-is-P = dfunext fe P'-htpy-P 
        where
         P'-htpy-P : P' ∼ P
         P'-htpy-P x = to-Ω-＝ fe (pe _≤ᴮ_-is-prop-valued (holds-is-prop (P x))
                                  P'-to-P P-to-P')
          where
           P'-to-P : x ≤ᴮ sup-P → x ∈ P
           P'-to-P = c-closed P (λ _ → id) x
           P-to-P' : x ∈ P → x ≤ᴮ sup-P
           P-to-P' r = _≤_-to-_≤ᴮ_ ((join-is-upper-bound-of L
                                    (𝕋 P , β ∘ 𝕋-to-carrier P)) (x , r))
     G : small-ϕ-closed-subsets-to-non-inc-points
       ∘ non-inc-points-to-small-ϕ-closed-subsets ∼ id
     G (a , is-non-inc) = to-subtype-＝ is-non-inc-is-predicate sup-P-is-a
      where
       P : 𝓟 {𝓥} B
       P = subset-of-small-ϕ-closed-subset
            (non-inc-points-to-small-ϕ-closed-subsets (a , is-non-inc))
       sup-P : ⟨ L ⟩
       sup-P = point-non-inc-points
                (small-ϕ-closed-subsets-to-non-inc-points
                 (non-inc-points-to-small-ϕ-closed-subsets (a , is-non-inc)))
       sup-P-is-a : sup-P ＝ a
       sup-P-is-a = is-sup'ᴮ a ⁻¹
     is-qinv : qinv small-ϕ-closed-subsets-to-non-inc-points
     is-qinv = (non-inc-points-to-small-ϕ-closed-subsets , H , G)

   module small-𝓘nd-from-exists (ind-e : inductively-generated-subset-exists ϕ)
                                 where

    open inductively-generated-subset-exists ind-e
    open trunc-ind-def ϕ ind-e

    module smallness-assumption (j : (b : B) → (b ∈ 𝓘nd) is 𝓥 small) where

     private
      𝓘' : (b : B) →  𝓥  ̇
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
                     → (b : B) → b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))
                     → b ∈ 𝓘'-subset
      𝓘'-is-c-closed U C b o =
        𝓘nd-to-𝓘' b (𝓘nd-is-c-closed U (λ x → 𝓘'-to-𝓘nd x ∘ C x) b o)
      
      𝓘'-is-ϕ-closed : (a : ⟨ L ⟩)
                     → (b : B)
                     → (b , a) ∈ ϕ
                     → ((b' : B) → b' ≤ᴮ a → b' ∈ 𝓘'-subset)
                     → b ∈ 𝓘'-subset
      𝓘'-is-ϕ-closed a b p f =
        𝓘nd-to-𝓘' b (𝓘nd-is-ϕ-closed a b p
                    (λ b' → 𝓘'-to-𝓘nd b' ∘ f b'))

      total-space-𝓘-is-small : (𝕋 𝓘nd) is 𝓥 small
      total-space-𝓘-is-small = (𝕋 𝓘'-subset , Σ-cong λ b → 𝓘'-equiv-𝓘nd b)
   
      e : 𝕋 𝓘'-subset ≃ 𝕋 𝓘nd
      e = resizing-condition total-space-𝓘-is-small

      sup-𝓘 : ⟨ L ⟩
      sup-𝓘 = ⋁ (𝕋 𝓘'-subset , β ∘ 𝕋-to-carrier 𝓘nd ∘ ⌜ e ⌝)

      sup-𝓘-is-lub : (sup-𝓘 is-lub-of (𝕋 𝓘nd , β ∘ 𝕋-to-carrier 𝓘nd)) holds
      sup-𝓘-is-lub = sup-of-small-fam-is-lub
                       L (β ∘ 𝕋-to-carrier 𝓘nd) total-space-𝓘-is-small

     Γ-has-least-fixed-point : has-least-fixed-point L (Γ ϕ i)
     Γ-has-least-fixed-point =
       (sup-𝓘 , antisymmetry-of L Γ-sup-below-sup sup-below-Γ-sup , sup-𝓘-below)
      where
       Γ-sup-below-sup : ((Γ ϕ i) sup-𝓘 ≤ sup-𝓘) holds
       Γ-sup-below-sup = is-non-inc-non-inc-points
                         (small-ϕ-closed-subsets-to-non-inc-points
                         (𝓘'-subset , 𝓘'-is-c-closed , 𝓘'-is-ϕ-closed))
       sup-below-Γ-sup : (sup-𝓘 ≤ (Γ ϕ i) sup-𝓘) holds
       sup-below-Γ-sup = transport (λ z → (sup-𝓘 ≤ z) holds)
                                   sup-Q-is-Γ-sup sup-𝓘-below-sup-Q
        where
         Γ-Γ-sup-below-Γ-sup : ((Γ ϕ i) ((Γ ϕ i) sup-𝓘) ≤ (Γ ϕ i) sup-𝓘) holds
         Γ-Γ-sup-below-Γ-sup =
           Γ-is-monotone ϕ i ((Γ ϕ i) sup-𝓘) sup-𝓘 Γ-sup-below-sup
         Q-Γ-sup : 𝓟 {𝓥} B
         Q-Γ-sup = subset-of-small-ϕ-closed-subset
                    (non-inc-points-to-small-ϕ-closed-subsets
                     ((Γ ϕ i) sup-𝓘 , Γ-Γ-sup-below-Γ-sup))
         Q-is-c-closed : (U : 𝓟 {𝓥} B)
                       → (U ⊆ Q-Γ-sup)
                       → ((b : B)
                       → b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))
                       → b ∈ Q-Γ-sup)
         Q-is-c-closed =
           c-closed-of-small-ϕ-closed-subset
            (non-inc-points-to-small-ϕ-closed-subsets
             ((Γ ϕ i) sup-𝓘 , Γ-Γ-sup-below-Γ-sup))
         Q-is-ϕ-closed : (a' : ⟨ L ⟩)
                       → (b : B)
                       → ((b , a') ∈ ϕ)
                       → ((b' : B)
                       → (b' ≤ᴮ a' → b' ∈ Q-Γ-sup))
                       → b ∈ Q-Γ-sup
         Q-is-ϕ-closed = ϕ-closed-of-small-ϕ-closed-subset
                          (non-inc-points-to-small-ϕ-closed-subsets
                           ((Γ ϕ i) sup-𝓘 , Γ-Γ-sup-below-Γ-sup))
         𝓘nd-contained-Q-Γ-sup : 𝓘nd ⊆ Q-Γ-sup
         𝓘nd-contained-Q-Γ-sup =
           𝓘nd-is-initial Q-Γ-sup Q-is-c-closed Q-is-ϕ-closed
         𝓘-is-small-subset-contained-Q-Γ-sup : 𝓘'-subset ⊆ Q-Γ-sup
         𝓘-is-small-subset-contained-Q-Γ-sup =
           (λ z → 𝓘nd-contained-Q-Γ-sup z ∘ 𝓘'-to-𝓘nd z)
         sup-Q : ⟨ L ⟩
         sup-Q = ⋁ (𝕋 Q-Γ-sup , β ∘ 𝕋-to-carrier Q-Γ-sup)
         sup-𝓘-below-sup-Q : (sup-𝓘 ≤ sup-Q) holds
         sup-𝓘-below-sup-Q =
           joins-preserve-containment L β {𝓘'-subset} {Q-Γ-sup}
                                      𝓘-is-small-subset-contained-Q-Γ-sup
         sup-Q-is-Γ-sup : sup-Q ＝ (Γ ϕ i) sup-𝓘
         sup-Q-is-Γ-sup = is-sup'ᴮ ((Γ ϕ i) sup-𝓘) ⁻¹
       sup-𝓘-below : (a : ⟨ L ⟩) → ((Γ ϕ i) a ＝ a) → (sup-𝓘 ≤ a) holds
       sup-𝓘-below a p = transport (λ z → (sup-𝓘 ≤ z) holds)
                                   sup-P-is-a
                                   sup-𝓘-below-sup-P
        where
         Γ-a-below-a : ((Γ ϕ i) a ≤ a) holds
         Γ-a-below-a = transport (λ z → ((Γ ϕ i) a ≤ z) holds)
                             p (reflexivity-of L ((Γ ϕ i) a))
         P-a : 𝓟 {𝓥} B
         P-a = subset-of-small-ϕ-closed-subset
                (non-inc-points-to-small-ϕ-closed-subsets (a , Γ-a-below-a))
         P-is-c-closed : (U : 𝓟 {𝓥} B)
                       → (U ⊆ P-a)
                       → ((b : B)
                       → b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))
                       → b ∈ P-a)
         P-is-c-closed = c-closed-of-small-ϕ-closed-subset
                          (non-inc-points-to-small-ϕ-closed-subsets
                           (a , Γ-a-below-a))
         P-is-ϕ-closed : (a' : ⟨ L ⟩)
                       → (b : B)
                       → ((b , a') ∈ ϕ)
                       → ((b' : B)
                       → (b' ≤ᴮ a' → b' ∈ P-a))
                       → b ∈ P-a
         P-is-ϕ-closed = ϕ-closed-of-small-ϕ-closed-subset
                          (non-inc-points-to-small-ϕ-closed-subsets
                           (a , Γ-a-below-a))
         𝓘nd-contained-P-a : 𝓘nd ⊆ P-a
         𝓘nd-contained-P-a = 𝓘nd-is-initial P-a P-is-c-closed P-is-ϕ-closed
         𝓘'-subset-contained-P-a : 𝓘'-subset ⊆ P-a
         𝓘'-subset-contained-P-a = λ z → 𝓘nd-contained-P-a z ∘ 𝓘'-to-𝓘nd z
         sup-P : ⟨ L ⟩
         sup-P = ⋁ (𝕋 P-a , β ∘ 𝕋-to-carrier P-a)
         sup-𝓘-below-sup-P : (sup-𝓘 ≤ sup-P) holds
         sup-𝓘-below-sup-P = joins-preserve-containment
                          L β {𝓘'-subset} {P-a} 𝓘'-subset-contained-P-a
         sup-P-is-a : sup-P ＝ a
         sup-P-is-a = is-sup'ᴮ a ⁻¹

\end{code}

We now consider a boundedness restricion on inductive definitions and show
that bounded inductive definitions are local.

An inductive definition is bounded if there is a small indexed family of
types that can be substituted for elements a : L in a sense to be made
precise below.

\begin{code}

module bounded-inductive-definition {𝓤 𝓦 𝓥 : Universe}
                                    {B : 𝓥  ̇}
                                    (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                    (β : B → ⟨ L ⟩)
                                     where

 open small-basis L β
 open Joins _≤_

 module bounded-from-small-basis-facts (h : is-small-basis) where

  open small-basis-facts h

  _is-a-small-cover-of_ : (X : 𝓥  ̇) → (Y : 𝓣  ̇) → 𝓥 ⊔ 𝓣  ̇
  X is-a-small-cover-of Y = X ↠ Y

  _has-a-bound : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
  ϕ has-a-bound = Σ I ꞉ 𝓥  ̇ , Σ α ꞉ (I → 𝓥  ̇) ,
                   ((a : ⟨ L ⟩)
                 → (b : B)
                 → (b , a) ∈ ϕ
                 → (Ǝ i ꞉ I , α i is-a-small-cover-of ↓ᴮ a) holds)

  bound-index : {ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)} → ϕ has-a-bound → 𝓥  ̇
  bound-index (I , α , covering) = I

  bound-family : {ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)}
               → (bnd : ϕ has-a-bound)
               → (bound-index {ϕ} bnd → 𝓥  ̇)
  bound-family (I , α , covering) = α

  covering-condition : {ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)}
                     → (bnd : ϕ has-a-bound)
                     → ((a : ⟨ L ⟩)
                     → (b : B)
                     → (b , a) ∈ ϕ
                     → (Ǝ i ꞉ (bound-index {ϕ} bnd) ,
                        ((bound-family {ϕ} bnd) i is-a-small-cover-of ↓ᴮ a))
                         holds)
  covering-condition (I , α , covering) = covering

  _is-bounded : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
  ϕ is-bounded = ((a : ⟨ L ⟩) → (b : B) → ((b , a) ∈ ϕ) is 𝓥 small)
               × (ϕ has-a-bound)

  open local-inductive-definitions L β
  open local-from-small-basis-facts h

  _bounded-implies-local : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                         → ϕ is-bounded
                         → ϕ is-local
  (ϕ bounded-implies-local) (ϕ-small , ϕ-has-bound) a =
    smallness-closed-under-≃ S₀-is-small S₀-equiv-S
   where
    I : 𝓥  ̇
    I = bound-index {ϕ} ϕ-has-bound
    α : I → 𝓥  ̇
    α = bound-family {ϕ} ϕ-has-bound
    cov : (a : ⟨ L ⟩)
        → (b : B)
        → (b , a) ∈ ϕ
        → (Ǝ i ꞉ I , (α i is-a-small-cover-of ↓ᴮ a)) holds
    cov = covering-condition {ϕ} ϕ-has-bound
    S₀ : 𝓤 ⊔ 𝓦 ⊔ 𝓥  ̇
    S₀ = Σ b ꞉ B , (Ǝ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
                   (b , ⋁ (α i , ↓ᴮ-inclusion a ∘ m)) ∈ ϕ) holds) holds
    S₀-is-small : S₀ is 𝓥 small
    S₀-is-small =
     Σ-is-small (B , ≃-refl B)
                (λ b → ∥∥-is-small pt (Σ-is-small (I , ≃-refl I)
                       λ i → ∥∥-is-small pt
                             (Σ-is-small (Π-is-small (fe') (α i , ≃-refl (α i))
                             λ _ → ↓ᴮ-is-small)
                             λ m → ϕ-small (⋁ (α i , ↓ᴮ-inclusion a ∘ m)) b)))

    S₀-to-S : S₀ → S ϕ a
    S₀-to-S (b , e) = (b , V e)
     where
      II : (i : I)
           → (Σ m ꞉ (α i → ↓ᴮ a) , (b , (⋁ (α i , ↓ᴮ-inclusion a ∘ m))) ∈ ϕ)
           → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
      II i (m , p) =
        ∣ (⋁ (α i , ↓ᴮ-inclusion a ∘ m) , p ,
          (join-is-least-upper-bound-of L (α i , ↓ᴮ-inclusion a ∘ m))
                                        (a , λ z → is-upper-bound-↓ a (m z))) ∣
      III : (i : I)
           → (Ǝ m ꞉ (α i → ↓ᴮ a) ,
             (b , (⋁ (α i , ↓ᴮ-inclusion a ∘ m))) ∈ ϕ) holds
           → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
      III i = ∥∥-rec ∥∥-is-prop (II i)
      IV : Σ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
              (b , (⋁ (α i , ↓ᴮ-inclusion a ∘ m))) ∈ ϕ) holds
           → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
      IV = uncurry III
      V : (Ǝ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
              (b , ⋁ (α i , ↓ᴮ-inclusion a ∘ m)) ∈ ϕ) holds) holds
           → (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
      V = ∥∥-rec ∥∥-is-prop IV

    S-to-S₀ : S ϕ a → S₀
    S-to-S₀ (b , e) = (b , V e)
     where
      inclusion : (a' : ⟨ L ⟩) → (a' ≤ a) holds → ↓ᴮ a' → ↓ᴮ a
      inclusion a' o (x , r) = (x , transitivity-of L (β x) a' a r o)
      II : (a' : ⟨ L ⟩)
        →  (b , a') ∈ ϕ
        → (a' ≤ a) holds
        → (Σ i ꞉ I , (α i is-a-small-cover-of ↓ᴮ a'))
        → (Ǝ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
            (b , ⋁ (α i , ↓ᴮ-inclusion a ∘ m)) ∈ ϕ) holds) holds
      II a' p o (i , α-covers) = ∣ (i , ∣ (m , in-ϕ) ∣) ∣
       where
        m : α i → ↓ᴮ a
        m = inclusion a' o ∘ ⌞ α-covers ⌟
        path : a' ＝ ⋁ (α i , ↓ᴮ-inclusion a ∘ m)
        path = reindexing-along-surj-＝-sup
                 L α-covers (β ∘ pr₁) 
                 a' (⋁ (α i , ↓ᴮ-inclusion a ∘ m)) (is-sup-↓ a')
                 (join-is-lub-of L (α i , ↓ᴮ-inclusion a ∘ m))
        in-ϕ : (b , ⋁ (α i , ↓ᴮ-inclusion a ∘ m)) ∈ ϕ
        in-ϕ = transport (λ z → (b , z) ∈ ϕ) path p
      III : (a' : ⟨ L ⟩)
          → (b , a') ∈ ϕ
          → (a' ≤ a) holds
          → (Ǝ i ꞉ I , (α i is-a-small-cover-of ↓ᴮ a')) holds
          → (Ǝ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
            (b , (⋁ (α i , ↓ᴮ-inclusion a ∘ m))) ∈ ϕ) holds) holds
      III a' p o = ∥∥-rec ∥∥-is-prop (II a' p o)
      IV : Σ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds
         → (Ǝ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
            (b , ⋁ (α i , ↓ᴮ-inclusion a ∘ m)) ∈ ϕ) holds) holds
      IV (a' , p , o) = III a' p o (cov a' b p)
      V : (Ǝ a' ꞉ ⟨ L ⟩ , (b , a') ∈ ϕ × (a' ≤ a) holds) holds
        → (Ǝ i ꞉ I , (Ǝ m ꞉ (α i → ↓ᴮ a) ,
           (b , ⋁ (α i , ↓ᴮ-inclusion a ∘ m)) ∈ ϕ) holds) holds
      V = ∥∥-rec ∥∥-is-prop IV

    S₀-equiv-S : S₀ ≃ S ϕ a
    S₀-equiv-S =
      (S₀-to-S , qinvs-are-equivs S₀-to-S is-qinv)
     where
      H : S-to-S₀ ∘ S₀-to-S ∼ id
      H (b , e) = to-subtype-＝ (λ _ → ∥∥-is-prop) refl
      G : S₀-to-S ∘ S-to-S₀ ∼ id
      G (b , e) = to-subtype-＝ (λ _ → ∥∥-is-prop) refl
      is-qinv : qinv S₀-to-S
      is-qinv = (S-to-S₀ , H , G)

\end{code}

We now consider a restriction on sup-lattices stronger than having a basis.
We want lattices to have a small presentation, so to speak.

A sup-lattice has a small presentation if there is a small indexed family of
subsets that can be substituted for arbitrary subsets in a sense to be made
precise below.

\begin{code}

module small-presentation-of-lattice {𝓤 𝓦 𝓥 : Universe}
                                     {B : 𝓥  ̇}
                                     (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                     (β : B → ⟨ L ⟩)
                                      where

 open small-basis L β
 open Joins _≤_

 module small-presentation-from-small-basis-facts (h : is-small-basis) where

  open small-basis-facts h
  open PropositionalTruncation pt

  _is-a-small-presentation : Σ J ꞉ 𝓥  ̇ , (J → 𝓟 {𝓥} B) × 𝓟 {𝓥} (B × 𝓟 {𝓥} B)
                           → (𝓥 ⁺)  ̇
  (J , Y , R) is-a-small-presentation = (b : B)
                                      → (X : 𝓟 {𝓥} B)
                                      → b ≤ᴮ (⋁ (𝕋 X , β ∘ 𝕋-to-carrier X))
                                      ≃ ((Ǝ j ꞉ J , Y j ⊆ X × (b , Y j) ∈ R)
                                         holds)

  has-small-presentation : (𝓥 ⁺)  ̇
  has-small-presentation = Σ 𝓡 ꞉ Σ J ꞉ 𝓥  ̇ ,
                            (J → 𝓟 {𝓥} B) × 𝓟 {𝓥} (B × 𝓟 {𝓥} B) ,
                            𝓡 is-a-small-presentation

\end{code}

We will now define, in the context of bounded ϕ and small-presentation 𝓡, a
new QIT that is equivalent to 𝓘nd. Our constructors should be familiar but
notice the bounded and small-presentation assumptions allow us to avoid large
quantification! 

\begin{code}

module small-QIT {𝓤 𝓦 𝓥 : Universe}
                 {B : 𝓥  ̇}
                 (L : Sup-Lattice 𝓤 𝓦 𝓥)
                 (β : B → ⟨ L ⟩)
                  where

 open small-basis L β
 open bounded-inductive-definition L β
 open small-presentation-of-lattice L β

 module small-QIT-from-small-basis-facts (h : is-small-basis) where
 
  open small-basis-facts h
  open bounded-from-small-basis-facts h
  open small-presentation-from-small-basis-facts h
 
  module small-QIT-from-bounded-and-small-presentation
    (small-pres : has-small-presentation)
    (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
    (bnd : ϕ is-bounded)
     where

   I₁ : 𝓥  ̇
   I₁ = pr₁ (pr₁ small-pres)

   Y : I₁ → 𝓟 {𝓥} B
   Y = pr₁ (pr₂ (pr₁ small-pres))

   R : 𝓟 {𝓥} (B × 𝓟 {𝓥} B)
   R = pr₂ (pr₂ (pr₁ small-pres))

   is-small-pres : (I₁ , Y , R) is-a-small-presentation
   is-small-pres = pr₂ small-pres

   is-small-pres-forward : (b : B)
                         → (X : 𝓟 {𝓥} B)
                         → b ≤ᴮ (⋁ (𝕋 X , β ∘ 𝕋-to-carrier X))
                         → ((Ǝ j ꞉ I₁ , Y j ⊆ X × (b , Y j) ∈ R) holds)
   is-small-pres-forward b X = ⌜ is-small-pres b X ⌝

   is-small-pres-backward : (b : B)
                          → (X : 𝓟 {𝓥} B)
                          → ((Ǝ j ꞉ I₁ , Y j ⊆ X × (b , Y j) ∈ R) holds)
                          → b ≤ᴮ (⋁ (𝕋 X , β ∘ 𝕋-to-carrier X))
   is-small-pres-backward b X = ⌜ is-small-pres b X ⌝⁻¹

   ϕ-is-small : (a : ⟨ L ⟩) → (b : B) → ((b , a) ∈ ϕ) is 𝓥 small
   ϕ-is-small = pr₁ bnd

   small-ϕ : (b : B) → (a : ⟨ L ⟩) → 𝓥  ̇
   small-ϕ b a = pr₁ (ϕ-is-small a b)

   small-ϕ-equiv-ϕ : (a : ⟨ L ⟩) → (b : B) → small-ϕ b a ≃ (b , a) ∈ ϕ
   small-ϕ-equiv-ϕ a b = pr₂ (ϕ-is-small a b)

   ϕ-is-small-forward : (a : ⟨ L ⟩) → (b : B) → small-ϕ b a → (b , a) ∈ ϕ
   ϕ-is-small-forward a b = ⌜ small-ϕ-equiv-ϕ a b  ⌝

   ϕ-is-small-backward : (a : ⟨ L ⟩) → (b : B) → (b , a) ∈ ϕ → small-ϕ b a
   ϕ-is-small-backward a b = ⌜ small-ϕ-equiv-ϕ a b ⌝⁻¹

   I₂ : 𝓥  ̇
   I₂ = pr₁ (pr₂ bnd)

   α : I₂ → 𝓥  ̇
   α = pr₁ (pr₂ (pr₂ bnd))

   cover-condition : ((a : ⟨ L ⟩)
                   → (b : B)
                   → (b , a) ∈ ϕ
                   → (Ǝ i ꞉ I₂ , α i is-a-small-cover-of ↓ᴮ a) holds)
   cover-condition = pr₂ (pr₂ (pr₂ bnd))

   data Small-Ind-Check : B → 𝓥  ̇ where
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

   record inductively-generated-small-subset-exists : 𝓤ω where
    constructor
     inductively-generated-small-subset

    field
     Small-Ind : B → 𝓥  ̇
     Small-Ind-trunc : (b : B) → is-prop (Small-Ind b)
     Small-c-cl : (i : I₁)
                → ((b : B) → (b ∈ Y i → Small-Ind b))
                → (b : B) → (b , Y i) ∈ R
                → Small-Ind b
     Small-ϕ-cl : (i : I₂)
                → (m : α i → B)
                → (b : B)
                → small-ϕ b (⋁ (α i , β ∘ m))
                → ((b' : B) → (b' ≤ᴮ (⋁ (α i , β ∘ m)) → Small-Ind b'))
                → Small-Ind b
     Small-Ind-Induction : (P : (b : B) → 𝓟 {𝓣} (Small-Ind b))
                         → ((i : I₁) → (f : (x : B) → (x ∈ Y i → Small-Ind x))
                          → ((x : B) → (y : x ∈ Y i) → f x y ∈ P x)
                          → (b : B) → (g : (b , Y i) ∈ R)
                          → Small-c-cl i f b g ∈ P b)
                         → ((i : I₂)
                          → (m : α i → B)
                          → (b : B)
                          → (p : small-ϕ b (⋁ (α i , β ∘ m)))
                          → (f : (x : B)
                          → (x ≤ᴮ (⋁ (α i , β ∘ m))
                          → Small-Ind x))
                          → ((x : B)
                          → (o : x ≤ᴮ (⋁ (α i , β ∘ m)))
                          → f x o ∈ P x)
                          → Small-ϕ-cl i m b p f ∈ P b)
                         → (b : B) → (i : Small-Ind b) → i ∈ P b

   module small-trunc-ind-def
     (ind-e : inductively-generated-small-subset-exists)
      where

    open inductively-generated-small-subset-exists ind-e

    Small-𝓘nd : 𝓟 {𝓥} B
    Small-𝓘nd b = (Small-Ind b , Small-Ind-trunc b)

    Small-𝓘nd-is-c-cl : (i : I₁)
                      → Y i ⊆ Small-𝓘nd
                      → (b : B)
                      → (b , Y i) ∈ R
                      → b ∈ Small-𝓘nd
    Small-𝓘nd-is-c-cl = Small-c-cl

    Small-𝓘nd-is-ϕ-cl : (i : I₂)
                      → (m : α i → B)
                      → (b : B)
                      → small-ϕ b (⋁ (α i , β ∘ m))
                      → ((b' : B)
                      → (b' ≤ᴮ (⋁ (α i , β ∘ m))
                      → b' ∈ Small-𝓘nd))
                      → b ∈ Small-𝓘nd
    Small-𝓘nd-is-ϕ-cl = Small-ϕ-cl

    Small-𝓘nd-Induction : (P : (b : B) → 𝓟 {𝓣} (b ∈ Small-𝓘nd))
                        → ((i : I₁) → (f : Y i ⊆ Small-𝓘nd)
                         → ((x : B) → (y : x ∈ Y i) → f x y ∈ P x)
                         → (b : B) → (g : (b , Y i) ∈ R)
                         → Small-c-cl i f b g ∈ P b)
                        → ((i : I₂)
                         → (m : α i → B)
                         → (b : B)
                         → (p : small-ϕ b (⋁ (α i , β ∘ m)))
                         → (f : (x : B)
                         → (x ≤ᴮ (⋁ (α i , β ∘ m))
                         → x ∈ Small-𝓘nd))
                         → ((x : B)
                         → (o : x ≤ᴮ (⋁ (α i , β ∘ m)))
                         → f x o ∈ P x)
                         → Small-ϕ-cl i m b p f ∈ P b)
                        → (b : B) → (i : b ∈ Small-𝓘nd) → i ∈ P b
    Small-𝓘nd-Induction = Small-Ind-Induction

    Small-𝓘nd-Recursion : (P : 𝓟 {𝓣} B)
                        → ((i : I₁)
                         → (Y i ⊆ Small-𝓘nd)
                         → (Y i ⊆ P)
                         → (b : B) → (b , Y i) ∈ R
                         → b ∈ P)
                        → ((i : I₂)
                         → (m : α i → B)
                         → (b : B)
                         → small-ϕ b (⋁ (α i , β ∘ m))
                         → ((x : B) → (x ≤ᴮ (⋁ (α i , β ∘ m)) → x ∈ Small-𝓘nd))
                         → ((x : B) → (x ≤ᴮ (⋁ (α i , β ∘ m)) → x ∈ P))
                         → b ∈ P)
                        → Small-𝓘nd ⊆ P
    Small-𝓘nd-Recursion P = Small-𝓘nd-Induction λ b → (λ _ → P b)

    Small-𝓘nd-Initial : (P : 𝓟 {𝓣} B)
                      → ((i : I₁)
                       → (Y i ⊆ P)
                       → (b : B) → (b , Y i) ∈ R
                       → b ∈ P)
                      → ((i : I₂)
                       → (m : α i → B)
                       → (b : B)
                       → small-ϕ b (⋁ (α i , β ∘ m))
                       → ((x : B) → (x ≤ᴮ (⋁ (α i , β ∘ m)) → x ∈ P))
                       → b ∈ P)
                      → Small-𝓘nd ⊆ P
    Small-𝓘nd-Initial {𝓣} P IH₁ IH₂ b b-in-Small-𝓘nd =
      Small-𝓘nd-Recursion P S S' b b-in-Small-𝓘nd
     where
      S : (i : I₁)
        → (Y i ⊆ Small-𝓘nd)
        → (Y i ⊆ P)
        → (b : B) → (b , Y i) ∈ R
        → b ∈ P
      S i C₁ C₂ b r = IH₁ i C₂ b r
      S' : (i : I₂)
         → (m : α i → B)
         → (b : B)
         → small-ϕ b (⋁ (α i , β ∘ m))
         → ((x : B) → (x ≤ᴮ (⋁ (α i , β ∘ m)) → x ∈ Small-𝓘nd))
         → ((x : B) → (x ≤ᴮ (⋁ (α i , β ∘ m)) → x ∈ P))
         → b ∈ P
      S' i m b s f g = IH₂ i m b s g

\end{code}

We will now show that under the assumptions of small presentation and bounded
ϕ that

  b ∈ Small-𝓘nd ≃ b ∈ 𝓘nd.
  
We make essential use of the initiality of both types here.

This will allow us to satisfy the smallness conditions needed to salvage the
least fixed point theorem.

\begin{code}

module 𝓘nd-is-small {𝓤 𝓦 𝓥 : Universe}
                    {B : 𝓥  ̇}
                    (L : Sup-Lattice 𝓤 𝓦 𝓥)
                    (β : B → ⟨ L ⟩)
                     where

 open small-basis L β
 open bounded-inductive-definition L β
 open small-presentation-of-lattice L β
 open inductive-definitions L β
 open small-QIT L β

 module 𝓘nd-is-small-from-small-basis-facts (h : is-small-basis) where
 
  open small-basis-facts h
  open bounded-from-small-basis-facts h
  open small-presentation-from-small-basis-facts h
  open ind-from-small-basis-facts h
  open small-QIT-from-small-basis-facts h
 
  module 𝓘nd-is-small-from-bounded-and-small-presentation
    (small-pres : has-small-presentation)
    (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
    (bnd : ϕ is-bounded)
     where

   open small-QIT-from-bounded-and-small-presentation small-pres ϕ bnd

   module 𝓘nd-is-small-QITs-exists
    (ind-e : inductively-generated-subset-exists ϕ)
    (ind-e' : inductively-generated-small-subset-exists)
     where

    open trunc-ind-def ϕ ind-e
    open small-trunc-ind-def ind-e'

    𝓘nd-⊆-Small-𝓘nd : 𝓘nd ⊆ Small-𝓘nd
    𝓘nd-⊆-Small-𝓘nd = 𝓘nd-is-initial Small-𝓘nd f g
     where
      f : (U : 𝓟 {𝓥} B)
        → U ⊆ Small-𝓘nd
        → (b : B)
        → b ≤ᴮ (⋁ (𝕋 U , β ∘ 𝕋-to-carrier U))
        → b ∈ Small-𝓘nd
      f U C b o = f'' (is-small-pres-forward b U o)
       where
        f' : (Σ j ꞉ I₁ , Y j ⊆ U × (b , Y j) ∈ R)
           → b ∈ Small-𝓘nd
        f' (j , C' , r) = Small-𝓘nd-is-c-cl j (λ x → λ y → C x (C' x y)) b r
        f'' : (Ǝ j ꞉ I₁ , Y j ⊆ U × (b , Y j) ∈ R) holds
            → b ∈ Small-𝓘nd
        f'' = ∥∥-rec (holds-is-prop (Small-𝓘nd b)) f'
      g : (a : ⟨ L ⟩)
        → (b : B)
        → (b , a) ∈ ϕ
        → ((b' : B) → b' ≤ᴮ a → b' ∈ Small-𝓘nd)
        → b ∈ Small-𝓘nd
      g a b p C = g'' (cover-condition a b p)
       where
        g' : Σ i ꞉ I₂ , α i is-a-small-cover-of ↓ᴮ a
           → b ∈ Small-𝓘nd
        g' (i , s) =
         Small-𝓘nd-is-ϕ-cl i (↓ᴮ-to-base a ∘ ⌞ s ⌟) b
                         (ϕ-is-small-backward (⋁ (α i , ↓ᴮ-inclusion a ∘ ⌞ s ⌟))
                                              b
                                              (transport (λ a' → (b , a') ∈ ϕ)
                                                         (a-＝-⋁-α) p))
                                              (λ b' → C b'
                                                ∘ (transport (λ a'
                                                  → b' ≤ᴮ a') (a-＝-⋁-α ⁻¹))) 
         where
          a-＝-⋁-α : a ＝ ⋁ (α i , ↓ᴮ-inclusion a ∘ ⌞ s ⌟)
          a-＝-⋁-α =
            reindexing-along-surj-＝-sup
              L s (↓ᴮ-inclusion a)
              a (⋁ (α i , ↓ᴮ-inclusion a ∘ ⌞ s ⌟)) (is-sup-↓ a)
              (join-is-lub-of L (α i , ↓ᴮ-inclusion a ∘ ⌞ s ⌟))
        g'' : (Ǝ i ꞉ I₂ , α i is-a-small-cover-of ↓ᴮ a) holds
            → b ∈ Small-𝓘nd
        g'' = ∥∥-rec (holds-is-prop (Small-𝓘nd b)) g'

    Small-𝓘nd-⊆-𝓘nd : Small-𝓘nd ⊆ 𝓘nd
    Small-𝓘nd-⊆-𝓘nd = Small-𝓘nd-Initial 𝓘nd f g
     where
      f : (i : I₁)
        → Y i ⊆ 𝓘nd
        → (b : B)
        → (b , Y i) ∈ R
        → b ∈ 𝓘nd
      f i C b r =
        𝓘nd-is-c-closed (Y i) C b
                        (is-small-pres-backward b (Y i)
                                                ∣ (i , (λ _ → id) , r) ∣)
      g : (i : I₂)
        → (m : α i → B)
        → (b : B)
        → small-ϕ b (⋁ (α i , β ∘ m))
        → ((x : B) → x ≤ᴮ (⋁ (α i , β ∘ m)) → x ∈ 𝓘nd)
        → b ∈ 𝓘nd
      g i m b s C =
        𝓘nd-is-ϕ-closed (⋁ (α i , β ∘ m)) b
                        (ϕ-is-small-forward (⋁ (α i , β ∘ m)) b s) C

    𝓘nd-is-small : (b : B) → (b ∈ 𝓘nd) is 𝓥 small
    𝓘nd-is-small b = (b ∈ Small-𝓘nd , equiv)
     where
      equiv : b ∈ Small-𝓘nd ≃ b ∈ 𝓘nd
      equiv = logically-equivalent-props-are-equivalent
               (holds-is-prop (Small-𝓘nd b))
               (holds-is-prop (𝓘nd b))
               (Small-𝓘nd-⊆-𝓘nd b)
               (𝓘nd-⊆-Small-𝓘nd b)

\end{code}

As a corollary of the above result we get a predicative version of the least
fixed point theorem. Notice that we are assuming our lattice is
small-presented and that we have a bounded ϕ that corresponds to our
monotone map. This is the most general statement that can be made but we are
actively exploring other, cleaner, formulations.

Least fixed point theorem:
Given a 𝓥-sup-lattice L with a 𝓥-presentation and a monotone
endomap f : L → L. If there exists a bounded abstract inductive definition
ϕ such that f ＝ Γ ϕ, then f has a least fixed point.

\begin{code}

module least-fixed-point {𝓤 𝓦 𝓥 : Universe}
                         {B : 𝓥  ̇}
                         (L : Sup-Lattice 𝓤 𝓦 𝓥)
                         (β : B → ⟨ L ⟩)
                          where

 open small-basis L β 
 open bounded-inductive-definition L β
 open small-presentation-of-lattice L β
 open correspondance-small-ϕ-closed-types-def-points L β
 open inductive-definitions L β
 open small-QIT L β
 open local-inductive-definitions L β
 open 𝓘nd-is-small L β

 module least-fixed-point-from-small-basis-facts (h : is-small-basis) where

  open small-basis-facts h
  open bounded-from-small-basis-facts h
  open small-presentation-from-small-basis-facts h
  open correspondance-from-small-basis-facts h
  open ind-from-small-basis-facts h
  open small-QIT-from-small-basis-facts h
  open local-from-small-basis-facts h
  open 𝓘nd-is-small-from-small-basis-facts h

  module QITs-exists-for-all-ϕ (ind-e : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                                      → inductively-generated-subset-exists ϕ)
                               (ind'-e : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                                       → (bnd : ϕ is-bounded)
                                       → (small-pres : has-small-presentation)
                                       →
    small-QIT-from-bounded-and-small-presentation.inductively-generated-small-subset-exists
    small-pres ϕ bnd)
                                 where

\end{code}

We first present the untruncated least fixed point theorem.

\begin{code}

   Untruncated-Least-Fixed-Point-Theorem :
      (small-pres : has-small-presentation)
    → (f : ⟨ L ⟩ → ⟨ L ⟩)
    → (f-mono : is-monotone L f)
    → Σ ϕ ꞉ 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩) ,
      Σ bnd ꞉ ϕ is-bounded ,
        ((x : ⟨ L ⟩)
       → (Γ ϕ ((ϕ bounded-implies-local) bnd)) x ＝ f x)
    → has-least-fixed-point L f
   Untruncated-Least-Fixed-Point-Theorem small-pres f f-mono (ϕ , bnd , H) =
    transport (λ g → Σ x ꞉ ⟨ L ⟩ , (g x ＝ x) × ((a : ⟨ L ⟩)
                                              → (g a ＝ a)
                                              → (x ≤ a) holds))
              path Γ-has-least-fixed-point
    where
     open correspondance-from-locally-small-ϕ ϕ ((ϕ bounded-implies-local) bnd)
     open small-𝓘nd-from-exists (ind-e ϕ)
     open 𝓘nd-is-small-from-bounded-and-small-presentation small-pres ϕ bnd
     open small-QIT-from-bounded-and-small-presentation small-pres ϕ bnd
     open 𝓘nd-is-small-QITs-exists (ind-e ϕ) (ind'-e ϕ bnd small-pres)
     open smallness-assumption 𝓘nd-is-small
     path : Γ ϕ ((ϕ bounded-implies-local) bnd) ＝ f
     path = dfunext fe H

\end{code}

The next *slightly awkward* theorem is going to provide us an intermediate
step toward the fully truncated least fixed point theorem.

\begin{code}

   Half-Truncated-Least-Fixed-Point-Theorem :
      (small-pres : has-small-presentation)
    → (f : ⟨ L ⟩ → ⟨ L ⟩)
    → (f-mono : is-monotone L f)
    → (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)) 
    → (Ǝ bnd ꞉ ϕ is-bounded ,
       ((x : ⟨ L ⟩)
      → (Γ ϕ ((ϕ bounded-implies-local) bnd)) x ＝ f x)) holds
    → has-least-fixed-point L f
   Half-Truncated-Least-Fixed-Point-Theorem small-pres f f-mono ϕ =
     ∥∥-rec (has-least-fixed-point-is-prop L f)
            (λ (bnd , H) → Untruncated-Least-Fixed-Point-Theorem small-pres
                                                                 f
                                                                 f-mono
                                                                 (ϕ , bnd , H))

\end{code}

We can now state the least fixed point theorem in it fully truncated form.

\begin{code}

   Least-Fixed-Point-Theorem : (small-pres : has-small-presentation)
                             → (f : ⟨ L ⟩ → ⟨ L ⟩)
                             → (f-mono : is-monotone L f)
                             → (Ǝ ϕ ꞉ 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩) ,
                               (Ǝ bnd ꞉ ϕ is-bounded ,
                               ((x : ⟨ L ⟩)
                              → (Γ ϕ ((ϕ bounded-implies-local) bnd)) x ＝ f x))
                                  holds) holds
                             → has-least-fixed-point L f
   Least-Fixed-Point-Theorem small-pres f f-mono =
     ∥∥-rec (has-least-fixed-point-is-prop L f)
            (uncurry (Half-Truncated-Least-Fixed-Point-Theorem small-pres
                                                               f
                                                               f-mono))

\end{code}

We begin exploring conditions on monotone endomaps that guarentee they
correspond to some bounded inductive definition. We tentatively call this
notion density.

A monotone map f, on a 𝓥-generated sup-lattice L, is dense if there is a family
γ : I → L, I : 𝓥, such that for all b : B and a : L we have

  b ≤ᴮ f a → Ǝ v ꞉ I , b ≤ᴮ f (γ v) × v ≤ᴮ a

\begin{code}

module density-of-monotone-maps {𝓤 𝓦 𝓥 : Universe}
                                {B : 𝓥  ̇}
                                (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                (β : B → ⟨ L ⟩)
                                 where

 open small-basis L β
 open bounded-inductive-definition L β
 open local-inductive-definitions L β

 module density-from-small-basis-facts (h : is-small-basis) where

  open small-basis-facts h
  open bounded-from-small-basis-facts h
  open local-from-small-basis-facts h

  is-dense : (f : ⟨ L ⟩ → ⟨ L ⟩) → 𝓤 ⊔ 𝓥  ̇
  is-dense f = (b : B)
             → (a : ⟨ L ⟩)
             → b ≤ᴮ f a
             → (Ǝ x ꞉ B , b ≤ᴮ f (β x) × x ≤ᴮ a) holds

  density-condition : (f : ⟨ L ⟩ → ⟨ L ⟩)
                    → (I : 𝓥  ̇)
                    → (γ : I → ⟨ L ⟩)
                    → 𝓤 ⊔ 𝓦 ⊔ 𝓥  ̇
  density-condition f I γ = (b : B)
                          → (a : ⟨ L ⟩)
                          → b ≤ᴮ f a
                          → (Ǝ i ꞉ I , b ≤ᴮ f (γ i) × (γ i ≤ a) holds) holds

  is-dense' : (f : ⟨ L ⟩ → ⟨ L ⟩) → 𝓤 ⊔ 𝓦 ⊔ (𝓥 ⁺)  ̇
  is-dense' f = Σ I ꞉ 𝓥  ̇ , Σ γ ꞉ (I → ⟨ L ⟩) , density-condition f I γ

  module locally-small-assumption (l-small : ⟨ L ⟩ is-locally 𝓥 small) where

   _＝ˢ_ : ⟨ L ⟩ → ⟨ L ⟩ → 𝓥 ̇
   x ＝ˢ y = resized (x ＝ y) (l-small x y)

   ＝ˢ-equiv-＝ : (x y : ⟨ L ⟩) → (x ＝ˢ y) ≃ (x ＝ y)
   ＝ˢ-equiv-＝ x y = resizing-condition (l-small x y)

   ＝ˢ-to-＝ : (x y : ⟨ L ⟩) → (x ＝ˢ y) → (x ＝ y)
   ＝ˢ-to-＝ x y = ⌜ ＝ˢ-equiv-＝ x y ⌝

   ＝-to-＝ˢ : (x y : ⟨ L ⟩) → (x ＝ y) → (x ＝ˢ y)
   ＝-to-＝ˢ x y = ⌜ ＝ˢ-equiv-＝ x y ⌝⁻¹

   dense-implies-bounded : (f : ⟨ L ⟩ → ⟨ L ⟩)
                         → is-monotone L f
                         → is-dense f
                         → Σ ϕ ꞉ 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩) ,
                           Σ bnd ꞉ ϕ is-bounded ,
                            ((a : ⟨ L ⟩)
                           → (Γ ϕ ((ϕ bounded-implies-local) bnd)) a ＝ f a)
   dense-implies-bounded f f-is-mono f-is-dense = (ϕ , bnd , H)
    where
     ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩)
     ϕ (b , a') =
       (Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds)
       , equiv-to-prop (Lift-≃ 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds))
                       (holds-is-prop (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a')))
     bnd : ϕ is-bounded
     bnd = (ϕ-small , (B , (λ z → small-↓ᴮ (β z)) , covering-cond))
      where
       ϕ-small : (a : ⟨ L ⟩) → (b : B) → (ϕ (b , a) holds) is 𝓥 small
       ϕ-small a b = ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a) holds
                     , ≃-Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a) holds))
       covering-cond : (a : ⟨ L ⟩)
                     → (b : B)
                     → (b , a) ∈ ϕ
                     → (Ǝ x ꞉ B , small-↓ᴮ (β x) ↠ ↓ᴮ a) holds
       covering-cond a b = map₃ ∘ map₂ ∘ map₁ 
        where
         map₁ : Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a) holds)
              → (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a) holds
         map₁ = ⌜ Lift-≃ 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a) holds) ⌝
         map₂ : (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a) holds
              → (Ǝ x ꞉ B , small-↓ᴮ (β x) ≃ ↓ᴮ a) holds
         map₂ =
           ∥∥-rec (holds-is-prop (Ǝ x ꞉ B , small-↓ᴮ (β x) ≃ ↓ᴮ a))
                  (λ (x , o , eq)
                   → ∣ (x , transport (λ z → small-↓ᴮ (β x) ≃ ↓ᴮ z)
                                      (＝ˢ-to-＝ (β x) a eq)
                                      small-↓ᴮ-≃-↓ᴮ) ∣)
         map₃ : (Ǝ x ꞉ B , small-↓ᴮ (β x) ≃ ↓ᴮ a) holds
              → (Ǝ x ꞉ B , small-↓ᴮ (β x) ↠ ↓ᴮ a) holds
         map₃ = ∥∥-rec (holds-is-prop (Ǝ x ꞉ B , small-↓ᴮ (β x) ↠ ↓ᴮ a))
                       (λ (x , f , f-is-equiv)
                        → ∣ (x , f , equivs-are-surjections f-is-equiv) ∣)
     H : (a : ⟨ L ⟩) → Γ ϕ ((ϕ bounded-implies-local) bnd) a ＝ f a
     H a = reindexing-along-equiv-＝-sup
             L equiv (β ∘ (S-to-base ϕ a))
             (Γ ϕ ((ϕ bounded-implies-local) bnd) a) (f a)
             (sup-of-small-fam-is-lub L (β ∘ S-to-base ϕ a)
                                      ((ϕ bounded-implies-local) bnd a))
             (is-supᴮ (f a))
      where
       map : (b : B)
           → b ≤ᴮ f a
           → (Ǝ a' ꞉ ⟨ L ⟩ ,
              Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds)
              × (a' ≤ a) holds) holds
       map b = map₄ b ∘ (map₂ b ∘ f-is-dense b a)
        where
         map₁ : (b : B)
              → Σ x ꞉ B , b ≤ᴮ f (β x) × x ≤ᴮ a
              → (Ǝ a' ꞉ ⟨ L ⟩ ,
                (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds
                × (a' ≤ a) holds) holds
         map₁ b (x , o , o') =
          ∣ (β x , ∣ (x , o , ＝-to-＝ˢ (β x) (β x) refl) ∣ , _≤ᴮ_-to-_≤_ o') ∣
         map₂ : (b : B)
              → (Ǝ x ꞉ B , b ≤ᴮ f (β x) × x ≤ᴮ a) holds
              → (Ǝ a' ꞉ ⟨ L ⟩ ,
                (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds
                × (a' ≤ a) holds) holds
         map₂ b = 
           ∥∥-rec (holds-is-prop (Ǝ a' ꞉ ⟨ L ⟩ ,
                                 (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds
                                 × (a' ≤ a) holds))
                  (map₁ b)
         map₃ : (b : B)
              → Σ a' ꞉ ⟨ L ⟩ ,
                (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds
                 × (a' ≤ a) holds
              → (Ǝ a' ꞉ ⟨ L ⟩ ,
                Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds)
                × (a' ≤ a) holds) holds
         map₃ b (a' , ex , o) =
           ∣ (a'
             , ⌜ ≃-Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds) ⌝ ex
             , o) ∣ 
         map₄ : (b : B)
              → (Ǝ a' ꞉ ⟨ L ⟩ ,
                (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds
                × (a' ≤ a) holds) holds
              → (Ǝ a' ꞉ ⟨ L ⟩ ,
                Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds)
                × (a' ≤ a) holds) holds
         map₄ b = ∥∥-rec (holds-is-prop (Ǝ a' ꞉ ⟨ L ⟩ ,
                           Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds)
                           × (a' ≤ a) holds))
                         (map₃ b)
       map' : (b : B)
            → (Ǝ a' ꞉ ⟨ L ⟩ ,
               Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds)
               × (a' ≤ a) holds) holds
            → b ≤ᴮ f a
       map' b = map₆ b ∘ map₂ b
        where
         map₁ : (b : B)
              → Σ a' ꞉ ⟨ L ⟩ ,
                Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds)
                × (a' ≤ a) holds
              → (Ǝ a' ꞉ ⟨ L ⟩ ,
                (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds
                × (a' ≤ a) holds) holds
         map₁ b (a' , lex , o) =
           ∣ (a'
             , ⌜ Lift-≃ 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds) ⌝ lex
             , o) ∣ 
         map₂ : (b : B)
              → (Ǝ a' ꞉ ⟨ L ⟩ ,
                Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds)
                × (a' ≤ a) holds) holds
              → (Ǝ a' ꞉ ⟨ L ⟩ ,
                (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds
                × (a' ≤ a) holds) holds
         map₂ b = 
           ∥∥-rec (holds-is-prop (Ǝ a' ꞉ ⟨ L ⟩ ,
                                 (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds
                                 × (a' ≤ a) holds))
                  (map₁ b)
         map₃ : (b : B)
              → (a' : ⟨ L ⟩)
              → (a' ≤ a) holds
              → Σ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a'
              → b ≤ᴮ f a
         map₃ b a' o (x , r , eq) =
           _≤_-to-_≤ᴮ_ (transitivity-of L
                                        (β b)
                                        (f a')
                                        (f a)
                                        (transport (λ z → (β b ≤ f z) holds)
                                                   (＝ˢ-to-＝ (β x)
                                                              a'
                                                              eq)
                                                   (_≤ᴮ_-to-_≤_ r))
                                        (f-is-mono a' a o))
         map₄ : (b : B)
              → (a' : ⟨ L ⟩)
              → (a' ≤ a) holds
              → (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds
              → b ≤ᴮ f a
         map₄ b a' o =
           ∥∥-rec (holds-is-prop (b ≤ᴮ f a , _≤ᴮ_-is-prop-valued)) (map₃ b a' o)
         map₅ : (b : B)
              → Σ a' ꞉ ⟨ L ⟩ ,
                (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds
                × (a' ≤ a) holds
              → b ≤ᴮ f a
         map₅ b = uncurry (λ a' → uncurry (λ ex → λ o → map₄ b a' o ex))
         map₆ : (b : B)
              → (Ǝ a' ꞉ ⟨ L ⟩ ,
                (Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds
                × (a' ≤ a) holds) holds
              → b ≤ᴮ f a
         map₆ b =
           ∥∥-rec (holds-is-prop (b ≤ᴮ f a , _≤ᴮ_-is-prop-valued)) (map₅ b) 
       equiv : (small-↓ᴮ (f a)) ≃ (S ϕ a)
       equiv = Σ-cong equiv-props
        where
         equiv-props : (b : B)
                     → b ≤ᴮ f a
                     ≃ ((Ǝ a' ꞉ ⟨ L ⟩ ,
                       Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds)
                       × (a' ≤ a) holds) holds)
         equiv-props b =
           logically-equivalent-props-are-equivalent
             _≤ᴮ_-is-prop-valued
             (holds-is-prop (Ǝ a' ꞉ ⟨ L ⟩ ,
                            Lift 𝓤 ((Ǝ x ꞉ B , b ≤ᴮ f (β x) × β x ＝ˢ a') holds)
                            × (a' ≤ a) holds))
             (map b)
             (map' b)

   dense'-implies-bounded : (f : ⟨ L ⟩ → ⟨ L ⟩)
                          → is-monotone L f
                          → is-dense' f
                          → Σ ϕ ꞉ 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩) ,
                            Σ bnd ꞉ ϕ is-bounded ,
                             ((a : ⟨ L ⟩)
                             → (Γ ϕ ((ϕ bounded-implies-local) bnd)) a ＝ f a)
   dense'-implies-bounded f f-mono (I , γ , f-dense) = {!!}
                                                
\end{code}

We use the notion of density to state another version of the least fixed point
theorem.

\begin{code}

module least-fixed-point-from-density {𝓤 𝓦 𝓥 : Universe}
                                      {B : 𝓥  ̇}
                                      (L : Sup-Lattice 𝓤 𝓦 𝓥)
                                      (β : B → ⟨ L ⟩)
                                       where

 open small-basis L β 
 open bounded-inductive-definition L β
 open small-presentation-of-lattice L β
 open correspondance-small-ϕ-closed-types-def-points L β
 open inductive-definitions L β
 open small-QIT L β
 open local-inductive-definitions L β
 open 𝓘nd-is-small L β
 open propositional-truncations-exist pt
 open least-fixed-point L β
 open density-of-monotone-maps L β

 module lfp-from-density-from-small-basis-facts (h : is-small-basis) where

  open small-basis-facts h
  open bounded-from-small-basis-facts h
  open small-presentation-from-small-basis-facts h
  open correspondance-from-small-basis-facts h
  open ind-from-small-basis-facts h
  open small-QIT-from-small-basis-facts h
  open local-from-small-basis-facts h
  open 𝓘nd-is-small-from-small-basis-facts h
  open least-fixed-point-from-small-basis-facts h
  open density-from-small-basis-facts h

  module QITs-exists-density (ind-e : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                                    → inductively-generated-subset-exists ϕ)
                             (ind'-e : (ϕ : 𝓟 {𝓤 ⊔ 𝓥} (B × ⟨ L ⟩))
                                     → (bnd : ϕ is-bounded)
                                     → (small-pres : has-small-presentation)
                                     →
    small-QIT-from-bounded-and-small-presentation.inductively-generated-small-subset-exists
    small-pres ϕ bnd)
                              where

   open QITs-exists-for-all-ϕ ind-e ind'-e

   Least-Fixed-Point-Theorem-from-Density : has-small-presentation
                                          → ⟨ L ⟩ is-locally 𝓥 small
                                          → (f : ⟨ L ⟩ → ⟨ L ⟩)
                                          → is-monotone L f
                                          → is-dense f
                                          → has-least-fixed-point L f
   Least-Fixed-Point-Theorem-from-Density small-pres l-small f f-mono f-dense =
     Untruncated-Least-Fixed-Point-Theorem
       small-pres
       f
       f-mono
       (dense-implies-bounded f f-mono f-dense)
    where
     open locally-small-assumption l-small

\end{code}

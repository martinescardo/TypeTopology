Tom de Jong, 27 & 30 November and 7 & 8 December 2022.
In collaboration with Nicolai Kraus, Fredrik Norvall Forsberg and Chuangjie Xu.

Cleaned up on 16, 17 and 19 December 2022.

Abstract
────────
We previously defined (in Ordinals/CumulativeHierarchy.lagda) the map
  𝕍-to-Ord : 𝕍 → Ord
such that
  𝕍-to-Ord (𝕍-set f) ＝ sup (λ a → 𝕍-to-Ord (f a) +ₒ 𝟙ₒ).

The recursive nature of 𝕍-to-Ord is convenient because it allows us to prove
properties by induction. Moreover, the supremum yields an ordinal by
construction.

We show here that this map also admits a nonrecursive description and pay
partiuclar attention to the size issues involved.


Introduction
────────────
A natural function that turns elements of 𝕍 into types is the map that takes an
element x : 𝕍 to its total space
  Σ y ꞉ 𝕍 , y ∈ x.
Note that when x is a set theoretic ordinal, i.e. it is an element of x : 𝕍ᵒʳᵈ,
then, since being a set theoretic ordinal is hereditary, we have
  (Σ y ꞉ 𝕍 , y ∈ x) ≃ (Σ y ꞉ 𝕍ᵒʳᵈ , y ∈ x).
Hence, the total space is an ordinal as it inherits the well-order from 𝕍ᵒʳᵈ.

However, the above does *not* define a map 𝕍 → Ord, because 𝕍, and hence the
total space, are large types, so that we get an ordinal in 𝓤 ⁺ and not in 𝓤, as
desired.

Still, we can prove that the total space yields an ordinal isomorphic to the one
obtained by 𝕍-to-Ord as the recursive supremum. In particular, it it thus
possible to give a more direct presentation, at least up to equivalence, of
𝕍-to-Ord (𝕍-set f) that is nonrecursive.

But we can do better, because the cumulative hierarchy 𝕍 is locally small,
meaning that its identity types are 𝓤-valued up to equivalence. We first observe
that the total space
  Σ y ꞉ 𝕍 , y ∈ 𝕍-set f
is equivalent to the image of f : A → 𝕍 (with A : 𝓤), which is a small type up
to equivalence thanks to the fact that 𝕍 is locally small.

(This general fact on small images of maps into locally small sets is recorded
in the module set-replacement-construction in the file UF/Quotient.lagda.)

Specifically, the image of f is equivalent to the set quotient A/~ where ~
relates two elements if f identifies them. We then prove that
  𝕍-to-Ord (𝕍-set {A} f) ＝ (A/~ , <),
where [a] < [a'] is defined to hold when f a ∈ f a'.


Summary
───────
In summary, we prove two results:
  (1) 𝕍-to-Ord (𝕍-set {A} f) and (A/~ , <) are equal as ordinals, and
  (2) 𝕍-to-Ord x and the total space (Σ y ꞉ 𝕍 , y ∈ x) are isomorphic as
      ordinals.
The isomorphism in (2) cannot be promoted to an equality (despite univalence),
because (Σ y ꞉ 𝕍 , y ∈ x) is a large type.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import MLTT.Spartan

open import UF.PropTrunc
open import UF.Univalence

module Ordinals.CumulativeHierarchy-Addendum
        (pt : propositional-truncations-exist)
        (ua : Univalence)
        (𝓤 : Universe)
       where

open import UF.Base hiding (_≈_)
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.ImageAndSurjection
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Quotient hiding (is-prop-valued)
open import UF.UA-FunExt

open ImageAndSurjection pt
open PropositionalTruncation pt

private
 fe : Fun-Ext
 fe = Univalence-gives-Fun-Ext ua

 fe' : FunExt
 fe' _ _ = fe

 pe : Prop-Ext
 pe = Univalence-gives-Prop-Ext ua

open import UF.CumulativeHierarchy pt fe pe
open import UF.CumulativeHierarchy-LocallySmall pt fe pe

open import Ordinals.CumulativeHierarchy pt ua 𝓤
open import Ordinals.Notions
open import Ordinals.OrdinalOfOrdinals ua
open import Ordinals.Type
open import Ordinals.WellOrderTransport fe'

module _
        (ch : cumulative-hierarchy-exists 𝓤)
       where

 open cumulative-hierarchy-exists ch

 open 𝕍-is-locally-small ch
 open ordinal-of-set-theoretic-ordinals ch

\end{code}

We start by showing that the total space (Σ y ꞉ 𝕍 , y ∈ x) of a set theoretic
ordinal x is a (large) type theoretic ordinal when ordered by membership.

\begin{code}

 module total-space-of-an-element-of-𝕍
         (x : 𝕍)
         (σ : is-set-theoretic-ordinal x)
        where

  𝕋x : 𝓤 ⁺ ̇
  𝕋x = Σ y ꞉ 𝕍 , y ∈ x

  _∈ₓ_ : 𝕋x → 𝕋x → 𝓤 ⁺ ̇
  u ∈ₓ v = pr₁ u ∈ pr₁ v

  ∈ₓ-is-prop-valued : is-prop-valued _∈ₓ_
  ∈ₓ-is-prop-valued u v = ∈-is-prop-valued

  ∈ₓ-is-transitive : is-transitive _∈ₓ_
  ∈ₓ-is-transitive u v w m n =
   transitive-set-if-set-theoretic-ordinal
    (being-set-theoretic-ordinal-is-hereditary σ (pr₂ w)) (pr₁ v) (pr₁ u) n m

  ∈ₓ-is-extensional : is-extensional _∈ₓ_
  ∈ₓ-is-extensional u v s t =
   to-subtype-＝ (λ _ → ∈-is-prop-valued)
                (∈-extensionality (pr₁ u) (pr₁ v) s' t')
    where
     s' : pr₁ u ⊆ pr₁ v
     s' y y-in-u = s (y , τ) y-in-u
      where
       τ : y ∈ x
       τ = transitive-set-if-set-theoretic-ordinal σ (pr₁ u) y (pr₂ u) y-in-u
     t' : pr₁ v ⊆ pr₁ u
     t' y y-in-v = t (y , τ) y-in-v
      where
       τ : y ∈ x
       τ = transitive-set-if-set-theoretic-ordinal σ (pr₁ v) y (pr₂ v) y-in-v

  ∈ₓ-is-well-founded : is-well-founded _∈ₓ_
  ∈ₓ-is-well-founded = λ (y , m) → ρ y m
   where
    ρ : (y : 𝕍) (m : y ∈ x) → is-accessible _∈ₓ_ (y , m)
    ρ = transfinite-induction _∈_ ∈-is-well-founded _ h
     where
      h : (y : 𝕍)
        → ((u : 𝕍) → u ∈ y → (m : u ∈ x) → is-accessible _∈ₓ_ (u , m))
        → (m : y ∈ x) → is-accessible _∈ₓ_ (y , m)
      h y IH m = step (λ (u , u-in-x) u-in-y → IH u u-in-y u-in-x)

  𝕋xᵒʳᵈ : Ordinal (𝓤 ⁺)
  𝕋xᵒʳᵈ = 𝕋x , _∈ₓ_ , ∈ₓ-is-prop-valued , ∈ₓ-is-well-founded
                    , ∈ₓ-is-extensional , ∈ₓ-is-transitive

\end{code}

Because being an set theoretic ordinal is hereditary the total spaces
  (Σ y ꞉ 𝕍 , y ∈ x) and (Σ y ꞉ 𝕍ᵒʳᵈ , y ∈ᵒʳᵈ (x , σ))
are equivalent, as we record below.

\begin{code}

  𝕋x-restricted-to-𝕍ᵒʳᵈ : 𝓤 ⁺ ̇
  𝕋x-restricted-to-𝕍ᵒʳᵈ = Σ y ꞉ 𝕍ᵒʳᵈ , y ∈ᵒʳᵈ (x , σ)

  𝕋x-restricted-to-𝕍ᵒʳᵈ-≃-𝕋x : 𝕋x-restricted-to-𝕍ᵒʳᵈ ≃ 𝕋x
  𝕋x-restricted-to-𝕍ᵒʳᵈ-≃-𝕋x = qinveq f (g , η , ε)
   where
    f : 𝕋x-restricted-to-𝕍ᵒʳᵈ → 𝕋x
    f ((y , _) , m) = y , m
    g : 𝕋x → 𝕋x-restricted-to-𝕍ᵒʳᵈ
    g (y , m) = (y , (being-set-theoretic-ordinal-is-hereditary σ m)) , m
    ε : f ∘ g ∼ id
    ε (y , m) = to-subtype-＝ (λ _ → ∈-is-prop-valued) refl
    η : g ∘ f ∼ id
    η ((y , τ) , m) =
     to-subtype-＝ (λ _ → ∈-is-prop-valued)
                   (to-subtype-＝ (λ _ → being-set-theoretic-ordinal-is-prop)
                                  refl)

\end{code}

When x = 𝕍-set f, then the total space of x is equivalent to the image f,
because y ∈ 𝕍-set f if and only if y is in the image of f.

\begin{code}

 module total-space-of-𝕍-set
         (sq : set-quotients-exist)
         {A : 𝓤 ̇ }
         (f : A → 𝕍)
         (σ : is-set-theoretic-ordinal (𝕍-set f))
        where

  private
   x = 𝕍-set f

  open total-space-of-an-element-of-𝕍 x σ
  open set-quotients-exist sq

  𝕋x-≃-image-f : 𝕋x ≃ image f
  𝕋x-≃-image-f = Σ-cong h
   where
    h : (y : 𝕍) → (y ∈ x) ≃ y ∈image f
    h y = logically-equivalent-props-are-equivalent
           ∈-is-prop-valued
           (being-in-the-image-is-prop y f)
           from-∈-of-𝕍-set
           to-∈-of-𝕍-set

\end{code}

The well order on the total space induces a well order on the image of f.

\begin{code}

  private
   transfer : Σ s ꞉ OrdinalStructure (image f) , (image f , s) ≃ₒ 𝕋xᵒʳᵈ
   transfer = transfer-structure (image f) 𝕋xᵒʳᵈ
               (≃-sym 𝕋x-≃-image-f)
               (_∈ₓ_ , (λ u v → ≃-refl (u ∈ₓ v)))

  image-fᵒʳᵈ : Ordinal (𝓤 ⁺)
  image-fᵒʳᵈ = image f , pr₁ transfer

  𝕋xᵒʳᵈ-≃-image-fᵒʳᵈ : 𝕋xᵒʳᵈ ≃ₒ image-fᵒʳᵈ
  𝕋xᵒʳᵈ-≃-image-fᵒʳᵈ = ≃ₒ-sym _ _ (pr₂ transfer)

\end{code}

As mentioned at the top of this file, the image of f : A → 𝕍 is equivalent to
the set quotient A/~ where ~ relates two elements of A if f identifies them.

We show that the relation ≺ on A/~ defined by [ a ] ≺ [ a' ] := f a ∈ f a' makes
this quotient into a type theoretic ordinal that moreover is isomorphic to the
ordinal image-fᵒʳᵈ.

Note that because equality on 𝕍 and ∈ take values in 𝓤 ⁺, this quotient
construction yields an ordinal in 𝓤 ⁺. We present a resized small-valued
varation of this construction below to get a quotient that lives in 𝓤, rather
than 𝓤 ⁺.

\begin{code}

 module 𝕍-set-carrier-quotient
         (sq : set-quotients-exist)
         {A : 𝓤 ̇ }
         (f : A → 𝕍)
        where

  open set-quotients-exist sq
  open extending-relations-to-quotient fe pe

  _~_ : A → A → 𝓤 ⁺ ̇
  a ~ b = f a ＝ f b

  ~EqRel : EqRel A
  ~EqRel = _~_ , (λ a b → 𝕍-is-large-set)
               , (λ a → refl)
               , (λ a b e → e ⁻¹)
               , (λ a b c e₁ e₂ → e₁ ∙ e₂)

  A/~ : 𝓤 ⁺ ̇
  A/~ = A / ~EqRel

  [_] : A → A/~
  [_] = η/ ~EqRel

  _≺[Ω]_ : A/~ → A/~ → Ω (𝓤 ⁺)
  _≺[Ω]_ = extension-rel₂ ~EqRel (λ a b → f a ∈[Ω] f b) ρ
   where
    ρ : {a b a' b' : A}
      → a ~ a' → b ~ b' → f a ∈[Ω] f b ＝ f a' ∈[Ω] f b'
    ρ {a} {b} {a'} {b'} e e' =
     Ω-extensionality fe pe (transport₂ _∈_ e e')
                            (transport₂ _∈_ (e ⁻¹) (e' ⁻¹))

  _≺_ : A/~ → A/~ → 𝓤 ⁺ ̇
  a ≺ b = (a ≺[Ω] b) holds

  ≺-is-prop-valued : is-prop-valued _≺_
  ≺-is-prop-valued a b = holds-is-prop (a ≺[Ω] b)

  ≺-＝-∈ : {a b : A} → [ a ] ≺ [ b ] ＝ f a ∈ f b
  ≺-＝-∈ {a} {b} = ap (_holds) (extension-rel-triangle₂ ~EqRel _ _ a b)

  ∈-to-≺ : {a b : A} → f a ∈ f b → [ a ] ≺ [ b ]
  ∈-to-≺ = back-Idtofun ≺-＝-∈

  ≺-to-∈ : {a b : A} → [ a ] ≺ [ b ] → f a ∈ f b
  ≺-to-∈ = Idtofun ≺-＝-∈

  ≺-is-transitive : is-set-theoretic-ordinal (𝕍-set f)
                  → is-transitive _≺_
  ≺-is-transitive σ = /-induction₃ fe ~EqRel prop-valued trans
    where
     prop-valued : (x y z : A / ~EqRel) → is-prop (x ≺ y → y ≺ z → x ≺ z)
     prop-valued x y z = Π₂-is-prop fe (λ _ _ → ≺-is-prop-valued x z)
     trans : (a b c : A) → [ a ] ≺ [ b ] → [ b ] ≺ [ c ] → [ a ] ≺ [ c ]
     trans a b c m n = ∈-to-≺ (τ (f a) (≺-to-∈ n) (≺-to-∈ m))
      where
       τ : (v : 𝕍) → f b ∈ f c → v ∈ f b → v ∈ f c
       τ = transitive-set-if-element-of-set-theoretic-ordinal σ
            (to-∈-of-𝕍-set ∣ c , refl ∣) (f b)

  ≺-is-extensional : is-transitive-set (𝕍-set f)
                   → is-extensional _≺_
  ≺-is-extensional τ =
   /-induction₂ fe ~EqRel (λ x y → Π₂-is-prop fe (λ _ _ → /-is-set ~EqRel))
                ext
    where
     ext : (a b : A)
         → ((x : A/~) → x ≺ [ a ] → x ≺ [ b ])
         → ((x : A/~) → x ≺ [ b ] → x ≺ [ a ])
         → [ a ] ＝ [ b ]
     ext a b s t = η/-identifies-related-points ~EqRel e'
      where
       e' : a ~ b
       e' = ∈-extensionality (f a) (f b) s' t'
        where
         lem : (x : 𝕍) (c : A) → x ∈ f c → ∃ d ꞉ A , f d ＝ x
         lem x c m = from-∈-of-𝕍-set (τ (f c) x (to-∈-of-𝕍-set ∣ c , refl ∣) m)
         s' : f a ⊆ f b
         s' x m = ∥∥-rec ∈-is-prop-valued h (lem x a m)
          where
           h : (Σ c ꞉ A , f c ＝ x) → x ∈ f b
           h (c , refl) = ≺-to-∈ (s [ c ] (∈-to-≺ m))
         t' : f b ⊆ f a
         t' x m = ∥∥-rec ∈-is-prop-valued h (lem x b m)
          where
           h : (Σ c ꞉ A , f c ＝ x) → x ∈ f a
           h (c , refl) = ≺-to-∈ (t [ c ] (∈-to-≺ m))

  ≺-is-well-founded : is-well-founded _≺_
  ≺-is-well-founded = /-induction ~EqRel acc-is-prop acc
   where
    acc-is-prop : (x : A/~) → is-prop (is-accessible _≺_ x)
    acc-is-prop = accessibility-is-prop _≺_ fe'
    acc' : (x : 𝕍) → ((a : A) → f a ＝ x → is-accessible _≺_ [ a ])
    acc' = transfinite-induction _∈_ ∈-is-well-founded _ h
     where
      h : (x : 𝕍)
        → ((y : 𝕍) → y ∈ x → (a : A) → f a ＝ y → is-accessible _≺_ [ a ])
        → (a : A) → f a ＝ x → is-accessible _≺_ [ a ]
      h x IH a refl =
       step (/-induction ~EqRel (λ _ → Π-is-prop fe (λ _ → acc-is-prop _)) α)
        where
         α : (b : A) → [ b ] ≺ [ a ] → is-accessible _≺_ [ b ]
         α b m = IH (f b) (≺-to-∈ m) b refl
    acc : (a : A) → is-accessible _≺_ [ a ]
    acc a = acc' (f a) a refl

  module quotient-as-ordinal
          (σ : is-set-theoretic-ordinal (𝕍-set f))
         where

   A/~ᵒʳᵈ : Ordinal (𝓤 ⁺)
   A/~ᵒʳᵈ = A/~ , _≺_
                , ≺-is-prop-valued
                , ≺-is-well-founded
                , ≺-is-extensional (transitive-set-if-set-theoretic-ordinal σ)
                , ≺-is-transitive σ

\end{code}

We now show that for x = 𝕍-set {A} f, the total space 𝕋xᵒʳᵈ and the above set
quotient A/~ᵒʳᵈ are equal as (large) ordinals. The equivalence of types is
proved generally in the module set-replacement-construction in the file
UF/Quotient.lagda. We only need to check that the equivalence is order
preserving and reflecting.

\begin{code}

   private
    x = 𝕍-set f

   open total-space-of-an-element-of-𝕍 x σ
   open total-space-of-𝕍-set sq f σ

   open set-replacement-construction sq pt f
                                     𝕍-is-locally-small
                                     𝕍-is-large-set
        hiding ([_])

   private
    ϕ : A/~ → image f
    ϕ = quotient-to-image

    ϕ-behaviour : (a : A) → ϕ [ a ] ＝ corestriction f a
    ϕ-behaviour = universality-triangle/ ~EqRel
                   (image-is-set f 𝕍-is-large-set) (corestriction f) _

    ϕ-is-order-preserving : is-order-preserving A/~ᵒʳᵈ image-fᵒʳᵈ ϕ
    ϕ-is-order-preserving = /-induction₂ fe ~EqRel prop-valued preserve
     where
      prop-valued : (a' b' : A / ~EqRel)
                  → is-prop (a' ≺ b' → underlying-order image-fᵒʳᵈ (ϕ a') (ϕ b'))
      prop-valued a' b' = Π-is-prop fe (λ _ → prop-valuedness _
                                               (is-well-ordered image-fᵒʳᵈ)
                                               (ϕ a') (ϕ b'))
      preserve : (a b : A)
               → [ a ] ≺ [ b ]
               → underlying-order image-fᵒʳᵈ (ϕ [ a ]) (ϕ [ b ])
      preserve a b l = transport₂ (underlying-order image-fᵒʳᵈ) p q mon
       where
        mem : f a ∈ f b
        mem = ≺-to-∈ l
        mon : underlying-order image-fᵒʳᵈ (corestriction f a) (corestriction f b)
        mon = mem
        p : corestriction f a ＝ ϕ [ a ]
        p = (ϕ-behaviour a) ⁻¹
        q : corestriction f b ＝ ϕ [ b ]
        q = (ϕ-behaviour b) ⁻¹

    ϕ-is-order-reflecting : is-order-reflecting A/~ᵒʳᵈ image-fᵒʳᵈ ϕ
    ϕ-is-order-reflecting = /-induction₂ fe ~EqRel prop-valued reflect
     where
      prop-valued : (a' b' : A/~)
                  → is-prop (underlying-order image-fᵒʳᵈ (ϕ a') (ϕ b') → a' ≺ b')
      prop-valued a' b' = Π-is-prop fe (λ _ → prop-valuedness _≺_
                                               (is-well-ordered A/~ᵒʳᵈ) a' b')
      reflect : (a b : A)
              → underlying-order image-fᵒʳᵈ (ϕ [ a ]) (ϕ [ b ])
              → [ a ] ≺ [ b ]
      reflect a b l = ∈-to-≺ mem
       where
        p : ϕ [ a ] ＝ corestriction f a
        p = ϕ-behaviour a
        q : ϕ [ b ] ＝ corestriction f b
        q = ϕ-behaviour b
        mem : f a ∈ f b
        mem = transport₂ (underlying-order image-fᵒʳᵈ) p q l

   total-space-is-quotientᵒʳᵈ : 𝕋xᵒʳᵈ ＝ A/~ᵒʳᵈ
   total-space-is-quotientᵒʳᵈ = 𝕋xᵒʳᵈ      ＝⟨ ⦅1⦆ ⟩
                                image-fᵒʳᵈ ＝⟨ ⦅2⦆ ⟩
                                A/~ᵒʳᵈ     ∎
    where
     ⦅1⦆ = eqtoidₒ 𝕋xᵒʳᵈ image-fᵒʳᵈ 𝕋xᵒʳᵈ-≃-image-fᵒʳᵈ
     ⦅2⦆ = eqtoidₒ image-fᵒʳᵈ A/~ᵒʳᵈ (≃ₒ-sym A/~ᵒʳᵈ image-fᵒʳᵈ (ϕ , ϕ-is-order-equiv))
      where
       ϕ-is-order-equiv : is-order-equiv A/~ᵒʳᵈ image-fᵒʳᵈ ϕ
       ϕ-is-order-equiv =
        order-preserving-reflecting-equivs-are-order-equivs _ _
         ϕ (⌜⌝⁻¹-is-equiv image-≃-quotient)
         ϕ-is-order-preserving
         ϕ-is-order-reflecting

\end{code}

Next, we make use of the fact that the cumulative hierarchy 𝕍 is locally small,
as shown in UF/CumulativeHierarchy-LocallySmall.lagda, to construct a small quotient
A/~⁻ equivalent to A/~.

\begin{code}

  _~⁻_ : A → A → 𝓤 ̇
  a ~⁻ b = f a ＝⁻ f b

  ~⁻EqRel : EqRel A
  ~⁻EqRel = _~⁻_ , (λ a b → ＝⁻-is-prop-valued)
                 , (λ a → ＝⁻-is-reflexive)
                 , (λ a b → ＝⁻-is-symmetric)
                 , (λ a b c → ＝⁻-is-transitive)

  A/~⁻ : 𝓤 ̇
  A/~⁻ = A / ~⁻EqRel

  A/~-≃-A/~⁻ : A/~ ≃ A/~⁻
  A/~-≃-A/~⁻ = quotients-equivalent A ~EqRel ~⁻EqRel (＝-to-＝⁻ , ＝⁻-to-＝)

\end{code}

The small-valued membership relation ∈⁻ developed in the aforementioned file now
allows us define a small-valued relation ≺' on A/~ and transfer the well order
on A/~ to A/~⁻, for which we use the machinery developed by Martín Escardó in
Ordinals/WellOrderTransport.lagda.

\begin{code}

  private
   ≺-has-small-values : (x y : A/~) → is-small (x ≺ y)
   ≺-has-small-values =
    /-induction₂ fe ~EqRel
                 (λ x y → being-small-is-prop ua (x ≺ y) 𝓤)
                 (λ a b → (f a ∈⁻ f b)
                        , ((f a ∈⁻ f b)    ≃⟨ ∈⁻-≃-∈ ⟩
                           (f a ∈ f b)     ≃⟨ idtoeq _ _ (≺-＝-∈ ⁻¹) ⟩
                           ([ a ] ≺ [ b ]) ■))

   _≺'_ : A/~ → A/~ → 𝓤 ̇
   x ≺' y = pr₁ (≺-has-small-values x y)

   ≺-≃-≺' : {x y : A/~} → x ≺ y ≃ x ≺' y
   ≺-≃-≺' {x} {y} = ≃-sym (pr₂ (≺-has-small-values x y))

  module small-quotient-as-ordinal
          (σ : is-set-theoretic-ordinal (𝕍-set f))
         where

   open quotient-as-ordinal σ

   private
    resize-ordinal : Σ s ꞉ OrdinalStructure A/~⁻ , (A/~⁻ , s) ≃ₒ A/~ᵒʳᵈ
    resize-ordinal = transfer-structure A/~⁻ A/~ᵒʳᵈ (≃-sym A/~-≃-A/~⁻)
                      (_≺'_ , (λ x y → ≺-≃-≺'))

   A/~⁻ᵒʳᵈ : Ordinal 𝓤
   A/~⁻ᵒʳᵈ = A/~⁻ , pr₁ resize-ordinal

   A/~⁻ᵒʳᵈ-≃ₒ-A/~ᵒʳᵈ : A/~⁻ᵒʳᵈ ≃ₒ A/~ᵒʳᵈ
   A/~⁻ᵒʳᵈ-≃ₒ-A/~ᵒʳᵈ = pr₂ resize-ordinal

   A/~ᵒʳᵈ--≃ₒ-A/~⁻ᵒʳᵈ : A/~ᵒʳᵈ ≃ₒ A/~⁻ᵒʳᵈ
   A/~ᵒʳᵈ--≃ₒ-A/~⁻ᵒʳᵈ = ≃ₒ-sym A/~⁻ᵒʳᵈ A/~ᵒʳᵈ A/~⁻ᵒʳᵈ-≃ₒ-A/~ᵒʳᵈ

   [_]⁻ : A → A/~⁻
   [_]⁻ = ⌜ A/~-≃-A/~⁻ ⌝ ∘ [_]

   []⁻-is-surjection : is-surjection [_]⁻
   []⁻-is-surjection = ∘-is-surjection (image-surjection-converse [_] λ P → /-induction ~EqRel) (equivs-are-surjections (⌜⌝-is-equiv A/~-≃-A/~⁻))

   _≺⁻_ : A/~⁻ → A/~⁻ → 𝓤 ̇
   _≺⁻_ = underlying-order A/~⁻ᵒʳᵈ

\end{code}

We relate the order ≺⁻ on the small quotient A/~⁻ to the order ≺ on the large
quotient A/~ and the set membership relation ∈ on 𝕍.

\begin{code}

   ≺⁻-≃-≺ : {a b : A} → [ a ]⁻ ≺⁻ [ b ]⁻ ≃ [ a ] ≺ [ b ]
   ≺⁻-≃-≺ {a} {b} = logically-equivalent-props-are-equivalent
                      (prop-valuedness _≺⁻_ (is-well-ordered A/~⁻ᵒʳᵈ)
                        [ a ]⁻ [ b ]⁻)
                      (≺-is-prop-valued [ a ] [ b ])
                      (⦅2⦆ [ a ] [ b ])
                      (⦅1⦆ [ a ] [ b ])
    where
     φ⁺ : A/~⁻ᵒʳᵈ ≃ₒ A/~ᵒʳᵈ
     φ⁺ = A/~⁻ᵒʳᵈ-≃ₒ-A/~ᵒʳᵈ
     φ⁻¹ : A/~ → A/~⁻
     φ⁻¹ = ≃ₒ-to-fun⁻¹ _ _ φ⁺
     φ-is-order-equiv : is-order-equiv A/~⁻ᵒʳᵈ A/~ᵒʳᵈ (≃ₒ-to-fun _ _ φ⁺)
     φ-is-order-equiv = ≃ₒ-to-fun-is-order-equiv _ _ φ⁺
     ⦅1⦆ : (x y : A/~) → x ≺ y → φ⁻¹ x ≺⁻ φ⁻¹ y
     ⦅1⦆ = inverses-of-order-equivs-are-order-preserving A/~⁻ᵒʳᵈ A/~ᵒʳᵈ
                                                         φ-is-order-equiv
     ⦅2⦆ : (x y : A/~) → φ⁻¹ x ≺⁻ φ⁻¹ y → x ≺ y
     ⦅2⦆ = inverses-of-order-equivs-are-order-reflecting A/~⁻ᵒʳᵈ A/~ᵒʳᵈ
                                                          φ-is-order-equiv

   ≺⁻-≃-∈ : {a b : A} → [ a ]⁻ ≺⁻ [ b ]⁻ ≃ f a ∈ f b
   ≺⁻-≃-∈ {a} {b} = [ a ]⁻ ≺⁻ [ b ]⁻ ≃⟨ ≺⁻-≃-≺ ⟩
                    ([ a ] ≺ [ b ])  ≃⟨ idtoeq _ _ ≺-＝-∈ ⟩
                    f a ∈ f b        ■

   ≺⁻-to-∈ : {a b : A} → [ a ]⁻ ≺⁻ [ b ]⁻ → f a ∈ f b
   ≺⁻-to-∈ = ⌜ ≺⁻-≃-∈ ⌝

   ∈-to-≺⁻ : {a b : A} → f a ∈ f b → [ a ]⁻ ≺⁻ [ b ]⁻
   ∈-to-≺⁻ = ⌜ ≺⁻-≃-∈ ⌝⁻¹

\end{code}

    We prove that A/~ is the supremum defined above by showing that
      Ord-to-𝕍 (A/~ᵒʳᵈ) ＝ 𝕍-set f.
    This boils down to proving
      (a : A) → f a ＝ Ord-to-𝕍 (A/~ ↓ [ a ]) (module size issues)

\begin{code}

   key-lemma : (a' : A/~⁻) (a : A) → a' ＝ [ a ]⁻ → Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻) ＝ f a
   key-lemma = transfinite-induction _≺⁻_ (Well-foundedness A/~⁻ᵒʳᵈ) _ ind-proof
    where
     ind-proof : (a' : A/~⁻)
               → ((b' : A/~⁻) → b' ≺⁻ a'
                              → (b : A) → b' ＝ [ b ]⁻
                              → Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ b ]⁻) ＝ f b)
               → (a : A) → a' ＝ [ a ]⁻ → Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻) ＝ f a
     ind-proof a' IH a refl = ∈-extensionality _ _ ⦅1⦆ ⦅2⦆
      where
       -- TO DO: Clean
       ⦅1⦆ : Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻) ⊆ f a
       ⦅1⦆ x m = ∥∥-rec ∈-is-prop-valued bzz
           (from-∈-of-𝕍-set (transport (x ∈_) (Ord-to-𝕍-behaviour (A/~⁻ᵒʳᵈ ↓ [ a ]⁻)) m))
        where
         foo : (b : A) → f b ∈ f a → x ＝ Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ b ]⁻) → x ∈ f a
         foo b n e = transport (_∈ f a) ((IH [ b ]⁻ (∈-to-≺⁻ n) b refl) ⁻¹ ∙ e ⁻¹) n
         bzz : Σ (λ a₁ → Ord-to-𝕍 ((A/~⁻ᵒʳᵈ ↓ [ a ]⁻) ↓ a₁) ＝ x) → x ∈ f a
         bzz ((b' , l) , e) = ∥∥-rec ∈-is-prop-valued zzz ([]⁻-is-surjection b')
          where
           zzz : Σ (λ x₁ → [ x₁ ]⁻ ＝ b') → x ∈ f a
           zzz (b , refl) = transport (_∈ f a) ((IH [ b ]⁻ l b refl) ⁻¹ ∙ ((ap Ord-to-𝕍 (iterated-↓ A/~⁻ᵒʳᵈ [ a ]⁻ [ b ]⁻ l)) ⁻¹ ∙ e ) ) (≺⁻-to-∈ l)
       ⦅2⦆ : f a ⊆ Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻)
       ⦅2⦆ x m = ∥∥-rec ∈-is-prop-valued (λ (b , n , e) → baz b n e) m'
        where
         m' : ∃ b ꞉ A , (f b ∈ f a) × (f b ＝ x)
         m' = ∥∥-functor h blah
          where
           blah : ∃ b ꞉ A , f b ＝ x
           blah = from-∈-of-𝕍-set (transitive-set-if-set-theoretic-ordinal σ (f a) x (to-∈-of-𝕍-set ∣ a , refl ∣) m)
           abstract
            h : (Σ b ꞉ A , f b ＝ x)
              → Σ b ꞉ A , (f b ∈ f a) × (f b ＝ x)
            h (b , e) = b , transport⁻¹ (_∈ f a) e m , e
         foo : (b : A) → f b ∈ f a → f b ＝ x → Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ b ]⁻) ＝ f b
         foo b n e = IH [ b ]⁻ (∈-to-≺⁻ n) b refl
         baz : (b : A) → f b ∈ f a → f b ＝ x → x ∈ Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻)
         baz b n e = transport (_∈ Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ a ]⁻)) (IH [ b ]⁻ (∈-to-≺⁻ n) b refl ∙ e)
                               (transport⁻¹ (Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ [ b ]⁻) ∈_)
                                            (Ord-to-𝕍-behaviour (A/~⁻ᵒʳᵈ ↓ [ a ]⁻))
                                            (to-∈-of-𝕍-set ∣ ([ b ]⁻ , (∈-to-≺⁻ n)) , (ap Ord-to-𝕍 (iterated-↓ A/~⁻ᵒʳᵈ [ a ]⁻ [ b ]⁻ (∈-to-≺⁻ n))) ∣))

   open 𝕍-to-Ord-construction sq
   coincide : 𝕍ᵒʳᵈ-to-Ord (𝕍-set f , σ) ＝ A/~⁻ᵒʳᵈ
   coincide = Ord-to-𝕍-is-left-cancellable (𝕍ᵒʳᵈ-to-Ord (𝕍-set f , σ)) A/~⁻ᵒʳᵈ
               e
    where
     e : Ord-to-𝕍 (𝕍ᵒʳᵈ-to-Ord (𝕍-set f , σ)) ＝ Ord-to-𝕍 A/~⁻ᵒʳᵈ
     e = Ord-to-𝕍 (𝕍ᵒʳᵈ-to-Ord (𝕍-set f , σ)) ＝⟨ ap pr₁ (𝕍ᵒʳᵈ-to-Ord-is-section-of-Ord-to-𝕍ᵒʳᵈ (𝕍-set f , σ)) ⟩
         𝕍-set f ＝⟨ 𝕍-set-ext f _ ⦅2⦆ ⟩
         𝕍-set (λ a' → Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ a')) ＝⟨ (Ord-to-𝕍-behaviour A/~⁻ᵒʳᵈ) ⁻¹ ⟩
         Ord-to-𝕍 A/~⁻ᵒʳᵈ ∎
      where
       ⦅2⦆ : f ≈ (λ a' → Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ a'))
       pr₁ ⦅2⦆ a = ∣ [ a ]⁻ , (key-lemma [ a ]⁻ a refl) ∣
       pr₂ ⦅2⦆ a' = ∥∥-functor h ([]⁻-is-surjection a')
        where
         h : Σ (λ x → [ x ]⁻ ＝ a') → Σ (λ b → f b ＝ Ord-to-𝕍 (A/~⁻ᵒʳᵈ ↓ a'))
         h (a , refl) = a , ((key-lemma a' a refl) ⁻¹)

 module _
         (sq : set-quotients-exist)
         (x : 𝕍ᵒʳᵈ)
        where

  open 𝕍-to-Ord-construction sq
  open total-space-of-an-element-of-𝕍
  open total-space-of-𝕍-set sq

  finally : 𝕍ᵒʳᵈ-to-Ord x ≃ₒ 𝕋xᵒʳᵈ (pr₁ x) (pr₂ x)
  finally = blah (pr₁ x) (pr₂ x)
   where
    blah : (y : 𝕍) (σ : is-set-theoretic-ordinal y)
         → 𝕍ᵒʳᵈ-to-Ord (y , σ) ≃ₒ 𝕋xᵒʳᵈ y σ
    blah = 𝕍-prop-simple-induction _ (λ y → Π-is-prop fe (λ σ → ≃ₒ-is-prop-valued (𝕍ᵒʳᵈ-to-Ord (y , σ)) (𝕋xᵒʳᵈ y σ))) foofoo
     where
      foofoo : {A : 𝓤 ̇ } (f : A → 𝕍) (σ : is-set-theoretic-ordinal (𝕍-set f))
             → 𝕍ᵒʳᵈ-to-Ord (𝕍-set f , σ) ≃ₒ 𝕋xᵒʳᵈ (𝕍-set f) σ
      foofoo {A} f σ = ≃ₒ-trans (𝕍ᵒʳᵈ-to-Ord (𝕍-set f , σ)) A/~⁻ᵒʳᵈ (𝕋xᵒʳᵈ (𝕍-set f) σ)
                        (idtoeqₒ _ _ coincide)
                        (≃ₒ-sym _ _ (≃ₒ-trans (𝕋xᵒʳᵈ (𝕍-set f) σ) A/~ᵒʳᵈ A/~⁻ᵒʳᵈ
                                              (idtoeqₒ _ _ total-space-is-quotientᵒʳᵈ)
                                              A/~ᵒʳᵈ--≃ₒ-A/~⁻ᵒʳᵈ))
       where
        open 𝕍-set-carrier-quotient sq f
        open small-quotient-as-ordinal σ
        open quotient-as-ordinal σ

\end{code}

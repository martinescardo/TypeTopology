---
title:          Properties of compactness
author:         Ayberk Tosun
date-started:   2024-07-19
date-completed: 2024-07-31
dates-updated:  [2024-09-05]
---

We collect properties related to compactness in locale theory in this module.
This includes the equivalences to two alternative definitions of the notion of
compactness, which we denote `is-compact-open'` and `is-compact-open''`.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

module Locales.Compactness.Properties
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Fin.Kuratowski pt
open import Fin.Type
open import Locales.Compactness.Definition pt fe
open import Locales.Frame pt fe renaming (⟨_⟩ to ⟨_⟩∙) hiding (∅)
open import MLTT.List using (member; []; _∷_; List; in-head; in-tail; length)
open import MLTT.List-Properties
open import Slice.Family
open import UF.ImageAndSurjection pt
open import UF.Logic
open import UF.Powerset-Fin pt
open import UF.Powerset-MultiUniverse
open import Notation.UnderlyingType

open AllCombinators pt fe
open Locale
open PropositionalTruncation pt

\end{code}

\section{Preliminaries}

We define a frame instance of the `Underlying-Type` typeclass to avoid name
clashes.

\begin{code}

instance
 underlying-type-of-frame : Underlying-Type (Frame 𝓤 𝓥 𝓦) (𝓤 ̇ )
 ⟨_⟩ {{underlying-type-of-frame}} (A , _) = A

\end{code}

Given a family `S`, we denote the type of its subfamilies by `SubFam S`.

\begin{code}

SubFam : {A : 𝓤 ̇ } {𝓦 : Universe} → Fam 𝓦 A → 𝓦 ⁺ ̇
SubFam {_} {A} {𝓦} (I , α) = Σ J ꞉ 𝓦 ̇ , (J → I)

\end{code}

Given any list, the type of elements that fall in the list is a
Kuratowski-finite type.

\begin{code}

list-members-is-Kuratowski-finite : {X : 𝓤 ̇ }
                                  → (xs : List X)
                                  → is-Kuratowski-finite
                                     (Σ x ꞉ X , ∥ member x xs ∥)
list-members-is-Kuratowski-finite {𝓤} {A} xs =
 ∣ length xs , nth xs , nth-is-surjection xs ∣
  where
   open list-indexing pt

\end{code}

TODO: The function `nth` above should be placed in a more appropriate module.

\section{Alternative definition of compactness}

Compactness could have been alternatively defined as:

\begin{code}

is-compact-open' : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact-open' {𝓤} {𝓥} {𝓦} X U =
 Ɐ S ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ ,
  U ≤ (⋁[ 𝒪 X ] S) ⇒
   (Ǝ (J , h) ꞉ SubFam S , is-Kuratowski-finite J
                         × (U ≤ (⋁[ 𝒪 X ] ⁅  S [ h j ] ∣ j ∶ J ⁆)) holds)
   where
    open PosetNotation (poset-of (𝒪 X))

\end{code}

This is much closer to the “every cover has a finite subcover” definition from
point-set topology.

It is easy to show that this implies the standard definition of compactness, but
we need a bit of preparation first.

Given a family `S`, we denote by `family-of-lists S` the family of families
of lists of `S`.

\begin{code}

module some-lemmas-on-directification (F : Frame 𝓤 𝓥 𝓦) where

 family-of-lists : Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 (Fam 𝓦 ⟨ F ⟩)
 family-of-lists S = List (index S) , h
  where
   h : List (index S) → Fam 𝓦 ⟨ F ⟩
   h is = (Σ i ꞉ index S , ∥ member i is ∥) , S [_] ∘ pr₁

\end{code}

Using this, we can give an alternative definition of the directification of
a family:

\begin{code}

 directify₂ : Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 ⟨ F ⟩
 directify₂ S = ⁅ ⋁[ F ] T ∣ T ε family-of-lists S ⁆

\end{code}

The function `directify₂` is equal to `directify` as expected.

\begin{code}

 directify₂-is-equal-to-directify
  : (S : Fam 𝓦 ⟨ F ⟩)
  → directify₂ S [_] ∼ directify F S [_]

 directify₂-is-equal-to-directify S [] =
  directify₂ S [ [] ]   ＝⟨ Ⅰ    ⟩
  𝟎[ F ]                ＝⟨refl⟩
  directify F S [ [] ]   ∎
   where

    † : (directify₂ S [ [] ] ≤[ poset-of F ] 𝟎[ F ]) holds
    † = ⋁[ F ]-least
         (family-of-lists S [ [] ])
         (𝟎[ F ] , λ { (_ , μ) → 𝟘-elim (∥∥-rec 𝟘-is-prop not-in-empty-list μ)})

    Ⅰ = only-𝟎-is-below-𝟎 F (directify₂ S [ [] ]) †

 directify₂-is-equal-to-directify S (i ∷ is) =
  directify₂ S [ i ∷ is ]                ＝⟨ Ⅰ    ⟩
  S [ i ] ∨[ F ] directify₂ S [ is ]     ＝⟨ Ⅱ    ⟩
  S [ i ] ∨[ F ] directify  F S [ is ]   ＝⟨refl⟩
  directify F S [ i ∷ is ]               ∎
   where
    open PosetNotation (poset-of F)
    open PosetReasoning (poset-of F)
    open Joins (λ x y → x ≤[ poset-of F ] y)

    IH = directify₂-is-equal-to-directify S is

    β : ((S [ i ] ∨[ F ] directify₂ S [ is ])
          is-an-upper-bound-of
         (family-of-lists S [ i ∷ is ]))
         holds
    β (j , ∣μ∣) =
     ∥∥-rec (holds-is-prop (S [ j ] ≤ (S [ i ] ∨[ F ] directify₂ S [ is ]))) † ∣μ∣
      where
       † : member j (i ∷ is)
         → (S [ j ] ≤ (S [ i ] ∨[ F ] directify₂ S [ is ]))
            holds
       † in-head     = ∨[ F ]-upper₁ (S [ j ]) (directify₂ S [ is ])
       † (in-tail μ) =
        family-of-lists S [ i ∷ is ] [ j , μ′ ]  ＝⟨ refl ⟩ₚ
        S [ j ]                                  ≤⟨ Ⅰ     ⟩
        directify₂ S [ is ]                      ≤⟨ Ⅱ     ⟩
        S [ i ] ∨[ F ] directify₂ S [ is ]       ■
         where
          μ′ : ∥ member j (i ∷ is) ∥
          μ′ = ∣ in-tail μ ∣

          Ⅰ = ⋁[ F ]-upper (family-of-lists S [ is ]) (j , ∣ μ ∣)
          Ⅱ = ∨[ F ]-upper₂ (S [ i ]) (directify₂ S [ is ])

    γ : ((directify₂ S [ i ∷ is ])
          is-an-upper-bound-of
         (family-of-lists S [ is ]))
        holds
    γ (k , μ) = ∥∥-rec (holds-is-prop (S [ k ] ≤ directify₂ S [ i ∷ is ])) ♢ μ
     where
      ♢ : member k is → (S [ k ] ≤ directify₂ S [ i ∷ is ]) holds
      ♢ μ = ⋁[ F ]-upper (family-of-lists S [ i ∷ is ]) (k , ∣ in-tail μ ∣)

    † : (directify₂ S [ i ∷ is ] ≤ (S [ i ] ∨[ F ] directify₂ S [ is ]))
         holds
    † = ⋁[ F ]-least
         (family-of-lists S [ i ∷ is ])
         ((S [ i ] ∨[ F ] directify₂ S [ is ]) , β)

    ‡ : ((S [ i ] ∨[ F ] directify₂ S [ is ]) ≤ directify₂ S [ i ∷ is ])
         holds
    ‡ = ∨[ F ]-least ‡₁ ‡₂
     where
      ‡₁ : (S [ i ] ≤ directify₂ S [ i ∷ is ]) holds
      ‡₁ = ⋁[ F ]-upper (family-of-lists S [ i ∷ is ]) (i , ∣ in-head ∣)

      ‡₂ : (directify₂ S [ is ] ≤ directify₂ S [ i ∷ is ]) holds
      ‡₂ = ⋁[ F ]-least
            (family-of-lists S [ is ])
            (directify₂ S [ i ∷ is ] , γ)

    Ⅰ  = ≤-is-antisymmetric (poset-of F) † ‡
    Ⅱ  = ap (λ - → S [ i ] ∨[ F ] -) IH

\end{code}

Using the equality between `directify` and `directify₂`, we can now easily show
how to obtain a subcover, from which it follows that `is-compact` implies
`is-compact'`.

\begin{code}

module characterization-of-compactness₁ (X : Locale 𝓤 𝓥 𝓦) where

 open PosetNotation (poset-of (𝒪 X))
 open PosetReasoning (poset-of (𝒪 X))
 open some-lemmas-on-directification (𝒪 X)

 finite-subcover-through-directification
  : (U : ⟨ 𝒪 X ⟩)
  → (S : Fam 𝓦 ⟨ 𝒪 X ⟩)
  → (is : List (index S))
  → (U ≤ directify (𝒪 X) S [ is ]) holds
  → Σ (J , β) ꞉ SubFam S ,
     is-Kuratowski-finite J × (U ≤ (⋁[ 𝒪 X ] ⁅  S [ β j ] ∣ j ∶ J ⁆)) holds
 finite-subcover-through-directification U S is p = T , 𝕗 , q
  where
   T : SubFam S
   T = (Σ i ꞉ index S , ∥ member i is ∥) , pr₁

   𝕗 : is-Kuratowski-finite (index T)
   𝕗 = list-members-is-Kuratowski-finite is

   † = directify₂-is-equal-to-directify S is ⁻¹

   q : (U ≤ (⋁[ 𝒪 X ] ⁅ S [ T [ x ] ] ∣ x ∶ index T ⁆)) holds
   q = U                                          ≤⟨ p     ⟩
       directify (𝒪 X) S [ is ]                   ＝⟨ †    ⟩ₚ
       directify₂ S [ is ]                        ＝⟨ refl ⟩ₚ
       ⋁[ 𝒪 X ] ⁅ S [ T [ x ] ] ∣ x ∶ index T ⁆   ■

\end{code}

It follows from this that `is-compact-open` implies `is-compact-open'`.

\begin{code}

 compact-open-implies-compact-open' : (U : ⟨ 𝒪 X ⟩)
                                    → is-compact-open  X U holds
                                    → is-compact-open' X U holds
 compact-open-implies-compact-open' U κ S q = ∥∥-functor † (κ S↑ δ p)
  where
   open JoinNotation (join-of (𝒪 X))

   Xₚ = poset-of (𝒪 X)

   S↑ : Fam 𝓦 ⟨ 𝒪 X ⟩
   S↑ = directify (𝒪 X) S

   δ : is-directed (𝒪 X) (directify (𝒪 X) S) holds
   δ = directify-is-directed (𝒪 X) S

   p : (U ≤[ Xₚ ] (⋁[ 𝒪 X ] S↑)) holds
   p = U             ≤⟨ Ⅰ ⟩
       ⋁[ 𝒪 X ] S    ＝⟨ Ⅱ ⟩ₚ
       ⋁[ 𝒪 X ] S↑   ■
        where
         Ⅰ = q
         Ⅱ = directify-preserves-joins (𝒪 X) S

   † : Σ is ꞉ index S↑ , (U ≤[ Xₚ ] S↑ [ is ]) holds
     → Σ (J , β) ꞉ SubFam S , is-Kuratowski-finite J
                            × (U ≤[ Xₚ ] (⋁⟨ j ∶ J ⟩ S [ β j ])) holds
   † = uncurry (finite-subcover-through-directification U S)

\end{code}

We now prove the converse which is a bit more difficult. We start with some
preparation.

Given a subset `P : ⟨ 𝒪 X ⟩ → Ω` and a family `S : Fam 𝓤 ⟨ 𝒪 X ⟩`, the type
`Upper-Bound-Data P S` is the type of indices `i` of `S` such that `S [ i ]` is
an upper bound of the subset `P`.

\begin{code}

module characterization-of-compactness₂ (X : Locale (𝓤 ⁺) 𝓤 𝓤) where

 open some-lemmas-on-directification (𝒪 X)
 open PosetNotation (poset-of (𝒪 X))
 open PosetReasoning (poset-of (𝒪 X))
 open Joins (λ x y → x ≤ y)

 Upper-Bound-Data : 𝓟 {𝓣} ⟨ 𝒪 X ⟩ → Fam 𝓤 ⟨ 𝒪 X ⟩ → 𝓤 ⁺ ⊔ 𝓣 ̇
 Upper-Bound-Data P S =
  Σ i ꞉ index S , (Ɐ x ꞉ ⟨ 𝒪 X ⟩ , P x ⇒ x ≤ S [ i ]) holds

\end{code}

We now define the truncated version of this which we denote `has-upper-bound-in`:

\begin{code}

 has-upper-bound-in :  𝓟 {𝓣} ⟨ 𝒪 X ⟩ → Fam 𝓤 ⟨ 𝒪 X ⟩ → Ω (𝓤 ⁺ ⊔ 𝓣)
 has-upper-bound-in P S = ∥ Upper-Bound-Data P S ∥Ω

\end{code}

Given a family `S`, we denote by `χ∙ S` the subset corresponding to the image of
the family.

\begin{code}

 χ∙ : Fam 𝓤 ⟨ 𝒪 X ⟩ → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⁺)
 χ∙ S U = U ∈image (S [_]) , being-in-the-image-is-prop U (S [_])
  where
   open Equality carrier-of-[ poset-of (𝒪 X) ]-is-set

\end{code}

Given a Kuratowski-finite family `S`, the subset `χ∙ S` is a Kuratowski-finite
subset.

\begin{code}

 χ∙-of-Kuratowski-finite-subset-is-Kuratowski-finite
  : (S : Fam 𝓤 ⟨ 𝒪 X ⟩)
  → is-Kuratowski-finite (index S)
  → is-Kuratowski-finite-subset (χ∙ S)
 χ∙-of-Kuratowski-finite-subset-is-Kuratowski-finite S = ∥∥-functor †
  where
   † : Σ n ꞉ ℕ , Fin n ↠ index S → Σ n ꞉ ℕ , Fin n ↠ image (S [_])
   † (n , h , σ) = n , h′ , φ
    where
     h′ : Fin n → image (S [_])
     h′ = corestriction (S [_]) ∘ h

     φ : is-surjection h′
     φ = ∘-is-surjection σ (corestrictions-are-surjections (S [_]))

\end{code}

We are now ready to prove our main lemma stating that every directed family `S`
contains at least one upper bound of every Kuratowski-finite subset.

\begin{code}

 open binary-unions-of-subsets pt

 directed-families-have-upper-bounds-of-Kuratowski-finite-subsets
  : (S : Fam 𝓤 ⟨ 𝒪 X ⟩)
  → is-directed (𝒪 X) S holds
  → (P : 𝓚 ⟨ 𝒪 X ⟩)
  → (⟨ P ⟩ ⊆ χ∙ S)
  → has-upper-bound-in ⟨ P ⟩ S holds
 directed-families-have-upper-bounds-of-Kuratowski-finite-subsets S 𝒹 (P , 𝕗) φ =
  Kuratowski-finite-subset-induction pe fe ⟨ 𝒪 X ⟩ σ R i β γ δ (P , 𝕗) φ
   where
    R : 𝓚 ⟨ 𝒪 X ⟩ → 𝓤 ⁺ ̇
    R Q = ⟨ Q ⟩ ⊆ χ∙ S → has-upper-bound-in ⟨ Q ⟩ S holds

    i : (Q : 𝓚 ⟨ 𝒪 X ⟩) → is-prop (R Q)
    i Q = Π-is-prop fe λ _ → holds-is-prop (has-upper-bound-in ⟨ Q ⟩ S)

    σ : is-set ⟨ 𝒪 X ⟩
    σ = carrier-of-[ poset-of (𝒪 X) ]-is-set

    open singleton-Kuratowski-finite-subsets σ

    β : R ∅[𝓚]
    β _ = ∥∥-functor
           (λ i → i , λ _ → 𝟘-elim)
           (directedness-entails-inhabitation (𝒪 X) S 𝒹)

    γ : (U : ⟨ 𝒪 X ⟩) → R ❴ U ❵[𝓚]
    γ U μ = ∥∥-functor † (μ U refl)
     where
      † : Σ i ꞉ index S , S [ i ] ＝ U
        → Upper-Bound-Data ⟨ ❴ U ❵[𝓚] ⟩ S
      † (i , q) = i , ϑ
       where
        ϑ : (V : ⟨ 𝒪 X ⟩ ) → U ＝ V → (V ≤ S [ i ]) holds
        ϑ V p = V          ＝⟨ p ⁻¹ ⟩ₚ
                U          ＝⟨ q ⁻¹ ⟩ₚ
                S [ i ]    ■

    δ : (𝒜 ℬ : 𝓚 ⟨ 𝒪 X ⟩) → R 𝒜 → R ℬ → R (𝒜 ∪[𝓚] ℬ)
    δ 𝒜@(A , _) ℬ@(B , _) ψ ϑ ι =
     ∥∥-rec₂ (holds-is-prop (has-upper-bound-in (A ∪ B) S)) † (ψ ι₁) (ϑ ι₂)
      where
       ι₁ : A ⊆ χ∙ S
       ι₁ V μ = ι V ∣ inl μ ∣

       ι₂ : B ⊆ χ∙ S
       ι₂ V μ = ι V ∣ inr μ ∣

       † : Upper-Bound-Data A S
         → Upper-Bound-Data B S
         → has-upper-bound-in (A ∪ B) S holds
       † (i , ξ) (j , ζ) = ∥∥-functor ‡ (pr₂ 𝒹 i j)
        where
         ‡ : (Σ k ꞉ index S , (S [ i ] ≤[ poset-of (𝒪 X) ] S [ k ]) holds
                            × (S [ j ] ≤[ poset-of (𝒪 X) ] S [ k ]) holds)
           → Upper-Bound-Data (A ∪ B) S
         ‡ (k , p , q) = k , ♢
          where
           ♢ : (U : ⟨ 𝒪 X ⟩) → U ∈ (A ∪ B) → (U ≤ S [ k ]) holds
           ♢ U = ∥∥-rec (holds-is-prop (U ≤ S [ k ])) ♠
            where
             ♠ : A U holds + B U holds → (U ≤ S [ k ]) holds
             ♠ (inl μ) = U           ≤⟨ ξ U μ ⟩
                         S [ i ]     ≤⟨ p     ⟩
                         S [ k ]     ■
             ♠ (inr μ) = U           ≤⟨ ζ U μ ⟩
                         S [ j ]     ≤⟨ q     ⟩
                         S [ k ]     ■

\end{code}

From this, we get that directed families contain at least one upper bound of
their Kuratowski-finite subfamilies.

\begin{code}

 directed-families-have-upper-bounds-of-Kuratowski-finite-subfamilies
  : (S : Fam 𝓤 ⟨ 𝒪 X ⟩)
  → is-directed (𝒪 X) S holds
  → (𝒥 : SubFam S)
  → is-Kuratowski-finite (index 𝒥)
  → has-upper-bound-in (χ∙ ⁅ S [ 𝒥 [ j ] ] ∣ j ∶ index 𝒥 ⁆) S holds
 directed-families-have-upper-bounds-of-Kuratowski-finite-subfamilies S 𝒹 𝒥 𝕗 =
  directed-families-have-upper-bounds-of-Kuratowski-finite-subsets
   S
   𝒹
   (χ∙ ⁅ S [ 𝒥 [ j ] ] ∣ j ∶ index 𝒥 ⁆ , 𝕗′)
   †
    where
     𝕗′ : is-Kuratowski-finite-subset (χ∙ ⁅ S [ 𝒥 [ j ] ] ∣ j ∶ index 𝒥 ⁆)
     𝕗′ = χ∙-of-Kuratowski-finite-subset-is-Kuratowski-finite
           ⁅ S [ 𝒥 [ j ] ] ∣ j ∶ index 𝒥 ⁆
           𝕗

     † : χ∙ ⁅ S [ 𝒥 [ j ] ] ∣ j ∶ index 𝒥 ⁆ ⊆ χ∙ S
     † U = ∥∥-functor ‡
      where
       ‡ : Σ j ꞉ index 𝒥 , S [ 𝒥 [ j ] ] ＝ U → Σ i ꞉ index S , S [ i ] ＝ U
       ‡ (i , p) = 𝒥 [ i ] , p

\end{code}

It easily follows from this that `is-compact-open'` implies `is-compact-open`.

\begin{code}

 compact-open'-implies-compact-open : (U : ⟨ 𝒪 X ⟩)
                                    → is-compact-open' X U holds
                                    → is-compact-open  X U holds
 compact-open'-implies-compact-open U κ S δ p = ∥∥-rec ∃-is-prop † (κ S p)
  where
   † : Σ (J , h) ꞉ SubFam S , is-Kuratowski-finite J
                            × (U ≤ (⋁[ 𝒪 X ] ⁅  S [ h j ] ∣ j ∶ J ⁆)) holds
     → ∃ i ꞉ index S , (U ≤ S [ i ]) holds
   † ((J , h) , 𝕗 , c) = ∥∥-functor ‡ γ
    where
     S′ : Fam 𝓤 ⟨ 𝒪 X ⟩
     S′ = ⁅  S [ h j ] ∣ j ∶ J ⁆

     ‡ : Upper-Bound-Data (χ∙ S′) S → Σ (λ i → (U ≤ S [ i ]) holds)
     ‡ (i , q) = i , ♢
      where
       φ : ((S [ i ]) is-an-upper-bound-of S′) holds
       φ j = q (S′ [ j ]) ∣ j , refl ∣

       Ⅰ = c
       Ⅱ = ⋁[ 𝒪 X ]-least ⁅ S [ h j ] ∣ j ∶ J ⁆ (S [ i ] , φ)

       ♢ : (U ≤ S [ i ]) holds
       ♢ = U                                 ≤⟨ Ⅰ ⟩
           ⋁[ 𝒪 X ] ⁅ S [ h j ] ∣ j ∶ J ⁆    ≤⟨ Ⅱ ⟩
           S [ i ]                           ■

     γ : has-upper-bound-in (χ∙ S′) S holds
     γ = directed-families-have-upper-bounds-of-Kuratowski-finite-subfamilies
          S
          δ
          (J , h)
          𝕗

\end{code}

\section{Another alternative definition}

We now provide another variant of the definition `is-compact-open'`, which we
show to be equivalent. This one says exactly that every cover has a
Kuratowski-finite subcover.

\begin{code}

is-compact-open'' : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓦 ⁺)
is-compact-open'' {𝓤} {𝓥} {𝓦} X U =
 Ɐ S ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ ,
  (U ＝ₚ ⋁[ 𝒪 X ] S) ⇒
   (Ǝ (J , h) ꞉ SubFam S , is-Kuratowski-finite J
                         × (U ＝ ⋁[ 𝒪 X ] ⁅  S [ h j ] ∣ j ∶ J ⁆))
    where
     open PosetNotation (poset-of (𝒪 X))
     open Equality carrier-of-[ poset-of (𝒪 X) ]-is-set

module characterization-of-compactness₃ (X : Locale 𝓤 𝓥 𝓦) where

 open PosetNotation (poset-of (𝒪 X))
 open PosetReasoning (poset-of (𝒪 X))
 open some-lemmas-on-directification (𝒪 X)

\end{code}

To see that `is-compact-open'` implies `is-compact-open''`, notice first that
for every open `U : ⟨ 𝒪 X ⟩` and family `S`, we have that `U ≤ ⋁ S` if and
only if `U ＝ ⋁ { U ∧ Sᵢ ∣ i : index S}`.

\begin{code}

 distribute-inside-cover₁ : (U : ⟨ 𝒪 X ⟩) (S : Fam 𝓦 ⟨ 𝒪 X ⟩)
                          → U ＝ ⋁[ 𝒪 X ] ⁅ U ∧[ 𝒪 X ] (S [ i ]) ∣ i ∶ index S ⁆
                          → (U ≤ (⋁[ 𝒪 X ] S)) holds
 distribute-inside-cover₁ U S p = connecting-lemma₂ (𝒪 X) †
  where
   Ⅰ = p

   Ⅱ : ⋁[ 𝒪 X ] ⁅ U ∧[ 𝒪 X ] S [ i ] ∣ i ∶ index S ⁆ ＝ U ∧[ 𝒪 X ] (⋁[ 𝒪 X ] S)
   Ⅱ = distributivity (𝒪 X) U S ⁻¹

   † : U ＝ U ∧[ 𝒪 X ] (⋁[ 𝒪 X ] S)
   † = U                                               ＝⟨ Ⅰ ⟩
       ⋁[ 𝒪 X ] ⁅ U ∧[ 𝒪 X ] S [ i ] ∣ i ∶ index S ⁆   ＝⟨ Ⅱ ⟩
       U ∧[ 𝒪 X ] (⋁[ 𝒪 X ] S)                         ∎

 distribute-inside-cover₂
  : (U : ⟨ 𝒪 X ⟩) (S : Fam 𝓦 ⟨ 𝒪 X ⟩)
  → (U ≤ (⋁[ 𝒪 X ] S)) holds
  → U ＝ ⋁[ 𝒪 X ] ⁅ U ∧[ 𝒪 X ] (S [ i ]) ∣ i ∶ index S ⁆
 distribute-inside-cover₂ U S p =
  U                                                 ＝⟨ Ⅰ ⟩
  U ∧[ 𝒪 X ] (⋁[ 𝒪 X ] S)                           ＝⟨ Ⅱ ⟩
  ⋁[ 𝒪 X ] ⁅ U ∧[ 𝒪 X ] (S [ i ]) ∣ i ∶ index S ⁆   ∎
  where
   Ⅰ = connecting-lemma₁ (𝒪 X) p
   Ⅱ = distributivity (𝒪 X) U S

\end{code}

The backward implication follows easily from these two lemmas.

\begin{code}

 compact-open''-implies-compact-open' : (U : ⟨ 𝒪 X ⟩)
                                      → is-compact-open'' X U holds
                                      → is-compact-open'  X U holds
 compact-open''-implies-compact-open' U κ S p = ∥∥-functor † ♢
  where
   q : U ＝ ⋁[ 𝒪 X ] ⁅ U ∧[ 𝒪 X ] (S [ i ]) ∣ i ∶ index S ⁆
   q = distribute-inside-cover₂ U S p

   ♢ : ∃ (J , h) ꞉ SubFam S , is-Kuratowski-finite J
                            × (U ＝ ⋁[ 𝒪 X ] ⁅ U ∧[ 𝒪 X ] S [ h j ] ∣ j ∶ J ⁆)
   ♢ = κ ⁅ U ∧[ 𝒪 X ] (S [ i ]) ∣ i ∶ index S ⁆ q

   † : Σ (J , h) ꞉ SubFam S , is-Kuratowski-finite J
                            × (U ＝ ⋁[ 𝒪 X ] ⁅ U ∧[ 𝒪 X ] S [ h j ] ∣ j ∶ J ⁆)
     → Σ (J , h) ꞉ SubFam S , is-Kuratowski-finite J
                            × (U ≤ (⋁[ 𝒪 X ] ⁅ S [ h j ] ∣ j ∶ J ⁆)) holds
   † (𝒥@(J , h) , 𝕗 , p) =
    𝒥 , 𝕗 , distribute-inside-cover₁ U ⁅ S [ h j ] ∣ j ∶ J ⁆ p

\end{code}

Now, the forward implication:

\begin{code}

 compact-open'-implies-compact-open'' : (U : ⟨ 𝒪 X ⟩)
                                      → is-compact-open'  X U holds
                                      → is-compact-open'' X U holds
 compact-open'-implies-compact-open'' U κ S p = ∥∥-functor † (κ S c)
  where
   open Joins (λ x y → x ≤ y)
   open PosetNotation (poset-of (𝒪 X)) renaming (_≤_ to _≤∙_)

   c : (U ≤∙ (⋁[ 𝒪 X ] S)) holds
   c = reflexivity+ (poset-of (𝒪 X)) p

   † : (Σ F ꞉ SubFam S ,
         is-Kuratowski-finite (index F)
         × (U ≤∙ (⋁[ 𝒪 X ] ⁅ S [ F [ j ] ] ∣ j ∶ index F ⁆)) holds)
     → Σ F ꞉ SubFam S ,
        is-Kuratowski-finite (index F)
        × (U ＝ ⋁[ 𝒪 X ] ⁅ S [ F [ j ] ] ∣ j ∶ index F ⁆)
   † (F , 𝕗 , q) = F , 𝕗 , r
    where
     ψ : cofinal-in (𝒪 X) ⁅ S [ F [ j ] ] ∣ j ∶ index F ⁆ S holds
     ψ j = ∣ F [ j ] , ≤-is-reflexive (poset-of (𝒪 X)) (S [ F [ j ] ]) ∣

     ♢ : ((⋁[ 𝒪 X ] ⁅ S [ F [ j ] ] ∣ j ∶ index F ⁆) ≤∙ U) holds
     ♢ = ⋁[ 𝒪 X ] ⁅ S [ F [ j ] ] ∣ j ∶ index F ⁆   ≤⟨  Ⅰ ⟩
         ⋁[ 𝒪 X ] S                                 ＝⟨ Ⅱ ⟩ₚ
         U                                          ■
          where
           Ⅰ = cofinal-implies-join-covered (𝒪 X) _ _ ψ
           Ⅱ = p ⁻¹

     r : U ＝ ⋁[ 𝒪 X ] ⁅ S [ F [ j ] ] ∣ j ∶ index F ⁆
     r = ≤-is-antisymmetric (poset-of (𝒪 X)) q ♢

\end{code}

In the above proof, I have implemented a simplification that Tom de Jong
suggested in a code review.

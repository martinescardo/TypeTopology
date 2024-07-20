Ayberk Tosun, 19 August 2023

The module contains the definitions of

  (1) a compact open of a locale, and
  (2) a compact locale.

These used to live in the `CompactRegular` module which is now deprecated and
will be broken down into smaller modules.

\begin{code}[hide]

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan hiding (J)
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import UF.SubtypeClassifier

module Locales.Compactness (pt : propositional-truncations-exist)
                           (fe : Fun-Ext)                          where

open import Fin.Kuratowski pt
open import Fin.Type
open import Locales.Frame     pt fe
open import Locales.WayBelowRelation.Definition  pt fe
open import MLTT.List using (member; []; _∷_; List; in-head; in-tail; length)
open import Slice.Family
open import Taboos.FiniteSubsetTaboo pt fe
open import UF.ImageAndSurjection pt
open import UF.Logic
open import UF.Powerset-MultiUniverse
open import UF.Powerset-Fin pt hiding (⟨_⟩)
open import UF.Sets-Properties
open import UF.Equiv hiding (_■)
open import UF.EquivalenceExamples

open PropositionalTruncation pt
open AllCombinators pt fe

open Locale

\end{code}

An open `U : 𝒪(X)` of a locale `X` is called compact if it is way below itself.

\begin{code}

is-compact-open : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact-open X U = U ≪[ 𝒪 X ] U

\end{code}

A locale `X` is called compact if its top element `𝟏` is compact.

\begin{code}

is-compact : Locale 𝓤 𝓥 𝓦 → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact X = is-compact-open X 𝟏[ 𝒪 X ]

\end{code}

We also define the type `𝒦 X` expressing the type of compact opens of a locale
`X`.

\begin{code}

𝒦 : Locale 𝓤 𝓥 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺  ̇
𝒦 X = Σ U ꞉ ⟨ 𝒪 X ⟩ , is-compact-open X U holds

𝒦-is-set : (X : Locale 𝓤 𝓥 𝓦) → is-set (𝒦 X)
𝒦-is-set X {(K₁ , κ₁)} {(K₂ , κ₂)} =
 Σ-is-set
  carrier-of-[ poset-of (𝒪 X) ]-is-set
  (λ U → props-are-sets (holds-is-prop (is-compact-open X U)))

to-𝒦-＝ : (X : Locale 𝓤 𝓥 𝓦) {K₁ K₂ : ⟨ 𝒪 X ⟩}
        → (κ₁ : is-compact-open X K₁ holds)
        → (κ₂ : is-compact-open X K₂ holds)
        → K₁ ＝ K₂
        → (K₁ , κ₁) ＝ (K₂ , κ₂)
to-𝒦-＝ X κ₁ κ₂ = to-subtype-＝ (holds-is-prop ∘ is-compact-open X)

\end{code}

Using this, we could define a family giving the compact opens of a locale `X`:

\begin{code}

ℬ-compact : (X : Locale 𝓤 𝓥 𝓦) → Fam (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺) ⟨ 𝒪 X ⟩
ℬ-compact X = 𝒦 X , pr₁

\end{code}

but the index of this family lives in `𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺`. This is to say that, if one
starts with a large and locally small locale, the resulting family would live in
`𝓤 ⁺` which means it would be *too big*.

\begin{code}

ℬ-compact₀ : (X : Locale (𝓤 ⁺) 𝓤 𝓤) → Fam (𝓤 ⁺) ⟨ 𝒪 X ⟩
ℬ-compact₀ = ℬ-compact

\end{code}

\section{Properties of compactness}

\begin{code}

𝟎-is-compact : (X : Locale 𝓤 𝓥 𝓦) → is-compact-open X 𝟎[ 𝒪 X ] holds
𝟎-is-compact X S (∣i∣ , _) p = ∥∥-rec ∃-is-prop † ∣i∣
 where
  † : index S → ∃ i ꞉ index S , (𝟎[ 𝒪 X ] ≤[ poset-of (𝒪 X) ] S [ i ]) holds
  † i = ∣ i , 𝟎-is-bottom (𝒪 X) (S [ i ]) ∣

𝟎ₖ[_] : (X : Locale 𝓤 𝓥 𝓦) → 𝒦 X
𝟎ₖ[_] X = 𝟎[ 𝒪 X ] , 𝟎-is-compact X

\end{code}

The binary join of two compact opens is compact.

\begin{code}

compact-opens-are-closed-under-∨ : (X : Locale 𝓤 𝓥 𝓦) (K₁ K₂ : ⟨ 𝒪 X ⟩)
                                 → is-compact-open X K₁ holds
                                 → is-compact-open X K₂ holds
                                 → is-compact-open X (K₁ ∨[ 𝒪 X ] K₂) holds
compact-opens-are-closed-under-∨ X U V κ₁ κ₂ S δ p =
 ∥∥-rec₂ ∃-is-prop † (κ₁ S δ φ) (κ₂ S δ ψ)
  where
   open PosetNotation  (poset-of (𝒪 X)) using (_≤_)
   open PosetReasoning (poset-of (𝒪 X))

   † : Σ i₁ ꞉ index S , (U ≤[ poset-of (𝒪 X) ] S [ i₁ ]) holds
     → Σ i₂ ꞉ index S , (V ≤[ poset-of (𝒪 X) ] S [ i₂ ]) holds
     → ∃ i₃ ꞉ index S  , ((U ∨[ 𝒪 X ] V) ≤ S [ i₃ ]) holds
   † (i₁ , p₁) (i₂ , p₂) = ∥∥-rec ∃-is-prop ‡ (pr₂ δ i₁ i₂)
    where
     ‡ : Σ i₃ ꞉ index S , (S [ i₁ ] ≤ S [ i₃ ]) holds
                        × (S [ i₂ ] ≤ S [ i₃ ]) holds
       → ∃ i₃ ꞉ index S  , ((U ∨[ 𝒪 X ] V) ≤ S [ i₃ ]) holds
     ‡ (i₃ , q , r) = ∣ i₃ , ∨[ 𝒪 X ]-least ♠ ♣ ∣
      where
       ♠ : (U ≤[ poset-of (𝒪 X) ] (S [ i₃ ])) holds
       ♠ = U ≤⟨ p₁ ⟩ S [ i₁ ] ≤⟨ q ⟩ S [ i₃ ] ■

       ♣ : (V ≤[ poset-of (𝒪 X) ] (S [ i₃ ])) holds
       ♣ = V ≤⟨ p₂ ⟩ S [ i₂ ] ≤⟨ r ⟩ S [ i₃ ] ■

   φ : (U ≤ (⋁[ 𝒪 X ] S)) holds
   φ = U ≤⟨ ∨[ 𝒪 X ]-upper₁ U V ⟩ U ∨[ 𝒪 X ] V ≤⟨ p ⟩ ⋁[ 𝒪 X ] S ■

   ψ : (V ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] S)) holds
   ψ = V ≤⟨ ∨[ 𝒪 X ]-upper₂ U V ⟩ U ∨[ 𝒪 X ] V ≤⟨ p ⟩ ⋁[ 𝒪 X ] S ■

\end{code}

Added on 2024-07-17.

\begin{code}

is-compact-open' : (X : Locale 𝓤 𝓥 𝓦) → ⟨ 𝒪 X ⟩ → Ω (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺)
is-compact-open' {𝓤} {𝓥} {𝓦} X U =
 Ɐ S ꞉ Fam 𝓦 ⟨ 𝒪 X ⟩ ,
  U ≤[ Xₚ ] (⋁[ 𝒪 X ] S) ⇒
   (Ǝ J ꞉ (𝓦  ̇) ,
     (Σ h ꞉ (J → index S) ,
      is-Kuratowski-finite J
      × (U ≤[ Xₚ ] (⋁[ 𝒪 X ] (J , S [_] ∘ h))) holds))
  where
   Xₚ = poset-of (𝒪 X)

\end{code}

\begin{code}

family-of-lists : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 (Fam 𝓦 ⟨ F ⟩)
family-of-lists {𝓤} {𝓥} {𝓦} F S = List (index S) , h
 where
  h : List (index S) → Fam 𝓦 ⟨ F ⟩
  h is = (Σ i ꞉ index S , member i is) , S [_] ∘ pr₁

directify₂ : (F : Frame 𝓤 𝓥 𝓦) → Fam 𝓦 ⟨ F ⟩ → Fam 𝓦 ⟨ F ⟩
directify₂ F S = List (index S) , (λ is → ⋁[ F ] (family-of-lists F S [ is ]))

helper-lemma : (X : Locale 𝓤 𝓥 𝓦) (U : ⟨ 𝒪 X ⟩) (S : Fam 𝓦 ⟨ 𝒪 X ⟩)
             → (is : List (index S))
             → directify (𝒪 X) S [ is ] ＝ directify₂ (𝒪 X) S [ is ]
helper-lemma X U S []       = directify (𝒪 X) S [ [] ]   ＝⟨ refl ⟩
                              𝟎[ 𝒪 X ]                   ＝⟨ † ⟩
                              join-of (𝒪 X) (Sigma (index S) (λ i → member i []) , _[_] S ∘ (λ r → pr₁ r))                       ∎
                               where
                                † : 𝟎[ 𝒪 X ] ＝ join-of (𝒪 X) (Sigma (index S) (λ i → member i []) , (λ x → S [ pr₁ x ]))
                                † = only-𝟎-is-below-𝟎 (𝒪 X) _ (⋁[ 𝒪 X ]-least _ (_ , (λ ()))) ⁻¹
helper-lemma X U S (i ∷ is) =
 directify (𝒪 X) S [ i ∷ is ]               ＝⟨ refl ⟩
 S [ i ] ∨[ 𝒪 X ] directify (𝒪 X) S [ is ] ＝⟨ Ⅱ ⟩
 S [ i ] ∨[ 𝒪 X ] directify₂ (𝒪 X) S [ is ] ＝⟨ Ⅰ ⟩
 directify₂ (𝒪 X) S [ i ∷ is ] ∎
  where
   open PosetReasoning (poset-of (𝒪 X))

   ‡ : rel-syntax (poset-of (𝒪 X)) (directify₂ (𝒪 X) S [ is ]) (join-of (𝒪 X) (family-of-lists (𝒪 X) S [ i ∷ is ])) holds
   ‡ = ⋁[ 𝒪 X ]-least (family-of-lists (𝒪 X) S [ is ]) (_ , λ { (j , p) → ⋁[ 𝒪 X ]-upper (family-of-lists (𝒪 X) S [ i ∷ is ]) (j , in-tail p) })

   † : ((S [ i ] ∨[ 𝒪 X ] directify₂ (𝒪 X) S [ is ]) ≤[ poset-of (𝒪 X) ] (directify₂ (𝒪 X) S [ i ∷ is ])) holds
   † = ∨[ 𝒪 X ]-least (⋁[ 𝒪 X ]-upper (family-of-lists (𝒪 X) S [ i ∷ is ]) (i , in-head)) ‡

   ‡₁ : (rel-syntax (poset-of (𝒪 X)) Joins.is-an-upper-bound-of binary-join (𝒪 X) (S [ i ]) (directify₂ (𝒪 X) S [ is ])) (family-of-lists (𝒪 X) S [ i ∷ is ]) holds
   ‡₁ (j , in-head) = ∨[ 𝒪 X ]-upper₁ (S [ j ]) (directify₂ (𝒪 X) S [ is ])
   ‡₁ (j , in-tail p) =
    family-of-lists (𝒪 X) S [ i ∷ is ] [ j , in-tail p ]    ＝⟨ refl ⟩ₚ
    S [ j ]                                                 ≤⟨ foo ⟩
    directify₂ (𝒪 X) S [ is ]                               ≤⟨ ∨[ 𝒪 X ]-upper₂ (S [ i ]) (directify₂ (𝒪 X) S [ is ]) ⟩
    binary-join (𝒪 X) (S [ i ]) (directify₂ (𝒪 X) S [ is ]) ■
     where
      foo : (S [ j ] ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] (family-of-lists (𝒪 X) S [ is ]))) holds
      foo = ⋁[ 𝒪 X ]-upper (family-of-lists (𝒪 X) S [ is ]) (j , p)

   †₁ : (directify₂ (𝒪 X) S [ i ∷ is ] ≤[ poset-of (𝒪 X) ] (S [ i ] ∨[ 𝒪 X ] directify₂ (𝒪 X) S [ is ])) holds
   †₁ = ⋁[ 𝒪 X ]-least (family-of-lists (𝒪 X) S [ i ∷ is ]) (_ , ‡₁)

   Ⅰ = ≤-is-antisymmetric (poset-of (𝒪 X)) † †₁

   Ⅱ = ap (λ - → S [ i ] ∨[ 𝒪 X ] -) (helper-lemma X U S is)

nth : {X : 𝓤  ̇} → (xs : List X) → (i : Fin (length xs)) → X
nth (x ∷ xs) (inr ⋆) = x
nth (x ∷ xs) (inl n) = nth xs n

kfin-lemma : {A : 𝓤  ̇} (xs : List A) → is-Kuratowski-finite (Σ x ꞉ A , member x xs)
kfin-lemma {𝓤} {A} xs = {!!}
 where
  h : Fin (length xs) → Σ x ꞉ A , member x xs
  h n = nth xs n , {!!}

main-lemma : (X : Locale 𝓤 𝓥 𝓦) (U : ⟨ 𝒪 X ⟩) (S : Fam 𝓦 ⟨ 𝒪 X ⟩)
           → let
              S↑ = directify (𝒪 X) S
             in
             (is : List (index S))
           → (U ≤[ poset-of (𝒪 X) ] S↑ [ is ]) holds
           → Σ J ꞉ (𝓦  ̇) ,
              Σ h ꞉ (J → index S) ,
               is-Kuratowski-finite J × ((U ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] (J , S [_] ∘ h))) holds)
main-lemma {_} {_} {𝓦} X U S is p = (Σ i ꞉ index S , member i is) , pr₁ , kfin-lemma is , †
 where
  open PosetReasoning (poset-of (𝒪 X))

  † : rel-syntax (poset-of (𝒪 X)) U (join-of (𝒪 X) (Sigma (index S) (λ i → member i is) , _[_] S ∘ (λ r → pr₁ r))) holds
  † = U ≤⟨ p ⟩ directify (𝒪 X) S [ is ] ＝⟨ helper-lemma X U S is ⟩ₚ join-of (𝒪 X) (Sigma (index S) (λ i → member i is) , _[_] S ∘ (λ r → pr₁ r)) ■

compact-open-implies-compact-open' : (X : Locale 𝓤 𝓥 𝓦)
                                   → (U : ⟨ 𝒪 X ⟩)
                                   → is-compact-open  X U holds
                                   → is-compact-open' X U holds
compact-open-implies-compact-open' {_} {_} {𝓦} X U κ S q =
 ∥∥-functor † (κ S↑ δ p)
 where
  open PosetReasoning (poset-of (𝒪 X))

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

  † : (Σ is ꞉ index S↑ , (U ≤[ Xₚ ] (S↑ [ is ])) holds)
    → Σ J ꞉ 𝓦  ̇ ,
       Σ h ꞉ (J → index S) ,
        is-Kuratowski-finite J × (U ≤[ Xₚ ] (⋁[ 𝒪 X ] (J , S [_] ∘ h))) holds
  † (is , r) = main-lemma X U S is r

\end{code}

\begin{code}

hauptsatz : (X : Locale 𝓤 𝓥 𝓦)
          → let open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)  in
          (S : 𝓟 {𝓤 ⁺} ⟨ 𝒪 X ⟩)
          → is-Kuratowski-finite-subset S
          → ∃ U ꞉ ⟨ 𝒪 X ⟩ ,
             ((V : ⟨ 𝒪 X ⟩) →
               (S V) holds →
                (U ≤[ poset-of (𝒪 X ) ] V) holds)
hauptsatz X S 𝒻 = {!!}
 where
  P : 𝓚 ⟨ 𝒪 X ⟩ → {!!}
  P (T , f) = {!!}

directed-family-lemma : (X : Locale 𝓤 𝓥 𝓦)
                      →
                        let open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)  in
                        (S : Fam 𝓦 ⟨ 𝒪 X ⟩)
                      → is-Kuratowski-finite (index S)
                      → (∃ i ꞉ index S , (((S [ i ]) is-an-upper-bound-of S) holds))
directed-family-lemma X S 𝒻 = {!!}

\end{code}

\begin{code}

-- foobar-lemma : {!!}
-- foobar-lemma = {!!}

-- another-lemma : (X : Locale 𝓤 𝓥 𝓦)
--                       →
--                         let open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)  in
--                         (S : Fam 𝓦 ⟨ 𝒪 X ⟩)
--                       → is-directed (𝒪 X) S holds
--                       → (J : 𝓦  ̇)
--                       → (h : J → index S)
--                       → (n : ℕ)
--                       → Fin n ↠ J
--                       → (∃ i ꞉ index S , (((S [ i ]) is-an-upper-bound-of (J , S [_] ∘ h)) holds))
-- another-lemma X S (ι , _) J h zero     (e , ψ) = ∥∥-rec ∃-is-prop (λ i → ∣ i , (λ j → 𝟘-elim (having-empty-enumeration-entails-emptiness J e ψ j)) ∣) ι
-- another-lemma X S δ@(_ , υ) J h (succ n) (e , ψ) = {!!}
--  where
--   foo : Exists (index S)
--          (λ i →
--             (rel-syntax (poset-of (𝒪 X)) Joins.is-an-upper-bound-of (S [ i ]))
--             (J , _[_] S ∘ h)
--             holds)
--   foo = another-lemma X S δ J h n (pr₁ (⌜ +→ {X = Fin n} {Y = 𝟙} fe ⌝ e) , {!!})

--   j₂ : J
--   j₂ = e (inr ⋆)

--   p : {!!} ＝ {!!}
--   p = {!!}

-- directedness-lemma : (F : Frame 𝓤 𝓥 𝓦)
--                    → (S : Fam 𝓦 ⟨ F ⟩)
--                    → (xs : List ⟨ F ⟩)
--                    → ((x : ⟨ F ⟩) → member x xs → x ∈image (S [_]))
--                    → ∃ i ꞉ index S , ((x : ⟨ F ⟩) → member x xs → (x ≤[ poset-of F ] (S [ i ])) holds)
-- directedness-lemma F S [] φ = {!!}
-- directedness-lemma F S (x ∷ xs) φ = {!!}



\end{code}

\begin{code}

{--
compact-open'-implies-compact-open : (X : Locale 𝓤 𝓥 𝓦)
                                   → (U : ⟨ 𝒪 X ⟩)
                                   → is-compact-open' X U holds
                                   → is-compact-open  X U holds
compact-open'-implies-compact-open {𝓤} {𝓥} {𝓦} X U κ S δ p = ∥∥-rec ∃-is-prop † (κ S p)
 where
  open Joins (λ x y → x ≤[ poset-of (𝒪 X) ] y)
  open PosetReasoning (poset-of (𝒪 X))

  † : (Σ J ꞉ 𝓦  ̇ , Σ h ꞉ (J → index S) , is-Kuratowski-finite J × ((U ≤[ poset-of (𝒪 X) ] (⋁[ 𝒪 X ] (J , (λ x → S [ h x ])))) holds))
    → (Ǝ k ꞉ index S , ((U ≤[ poset-of (𝒪 X) ] S [ k ]) holds)) holds
  † (J , h , κ , q) = ∥∥-rec ∃-is-prop ‡ {!!}
   where
    ‡ : (Σ j ꞉ J , (((S [ h j ]) is-an-upper-bound-of (J , (S [_] ∘ h))) holds))
      → ∃ (λ k → rel-syntax (poset-of (𝒪 X)) U (S [ k ]) holds)
    ‡ (j , υ) = ∣ h j , {!!} ∣
     where
      ♢ : (U ≤[ poset-of (𝒪 X) ] S [ h j ]) holds
      ♢ = U ≤⟨ q ⟩ ⋁[ 𝒪 X ] (J , (λ x → S [ h x ])) ≤⟨ ⋁[ 𝒪 X ]-least (J , (λ x → S [ h x ])) ((S [ h j ]) , υ) ⟩ S [ h j ] ■
--}

\end{code}

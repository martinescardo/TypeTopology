Ayberk Tosun, 17 August 2023.

\begin{code}

{-# OPTIONS --safe --without-K --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.PropTrunc
open import UF.FunExt
open import UF.FunExt
open import MLTT.List hiding ([_])
open import Slice.Family
open import UF.SubtypeClassifier
open import UF.Size

module Locales.Spectrality.BasisDirectification
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (sr : Set-Replacement pt) where

open import Locales.Frame pt fe
open import Locales.Compactness pt fe
open import Locales.SmallBasis pt fe sr

open import UF.Logic
open AllCombinators pt fe

open PropositionalTruncation pt

open Locale

\end{code}

Given a basis closed under binary meets, the directification of that basis using
the `directify` function is also closed under binary meets. The reason is that
the meets of joins can be turned into joins of meets. In this section, we prove
this fact.

To define CNF transformation, we need the following function
`conjunct-with-list` which takes some `x` and some list `y₁ , … , yₙ` and
computes `(x ∧ y₁) , … , (x ∧ yₙ)`.

\begin{code}

conjunct-with-list : (F : Frame 𝓤 𝓥 𝓦)
                   → ⟨ F ⟩ → List ⟨ F ⟩ → List ⟨ F ⟩
conjunct-with-list F x = map (λ - → x ∧[ F ] -)

cnf-transform : (F : Frame 𝓤 𝓥 𝓦)
              → List ⟨ F ⟩ → List ⟨ F ⟩ → ⟨ F ⟩
cnf-transform F []       ys = 𝟎[ F ]
cnf-transform F (x ∷ xs) ys =
 (⋁ₗ[ F ] conjunct-with-list F x ys) ∨[ F ] cnf-transform F xs ys

\end{code}

Given some `x : ⟨ F ⟩` and a list `(y₁ , … , yₙ) : List ⟨ F ⟩`,
`x ∧ (y₁ ∨ … ∨ yₙ) ＝ (x ∧ y₁) ∨ … ∨ (x ∧ yₙ)`, which is of course just an
instance of the distributivity law. We prove this fact next.

\begin{code}

distributivity-list : (F : Frame 𝓤 𝓥 𝓦) (x : ⟨ F ⟩) (ys : List ⟨ F ⟩)
                    → x ∧[ F ] (⋁ₗ[ F ] ys) ＝ ⋁ₗ[ F ] (conjunct-with-list F x ys)
distributivity-list F x []       = 𝟎-right-annihilator-for-∧ F x
distributivity-list F x (y ∷ ys) =
 x ∧[ F ] (y ∨[ F ] (⋁ₗ[ F ] ys))                         ＝⟨ Ⅰ    ⟩
 (x ∧[ F ] y) ∨[ F ] (x ∧[ F ] (⋁ₗ[ F ] ys))              ＝⟨ Ⅱ    ⟩
 (x ∧[ F ] y) ∨[ F ] (⋁ₗ[ F ] conjunct-with-list F x ys)  ＝⟨ refl ⟩
 ⋁ₗ[ F ] (conjunct-with-list F x (y ∷ ys))                ∎
  where
   Ⅰ = binary-distributivity F x y (join-list F ys)
   Ⅱ = ap (λ - → (x ∧[ F ] y) ∨[ F ] -) (distributivity-list F x ys)

\end{code}

With `distributivity-list` in hand, we are ready to prove the correctness of the
CNF transformation procedure.

\begin{code}

cnf-transform-correct : (F : Frame 𝓤 𝓥 𝓦) (xs ys : List ⟨ F ⟩)
                      → (⋁ₗ[ F ] xs) ∧[ F ] (⋁ₗ[ F ] ys) ＝ cnf-transform F xs ys
cnf-transform-correct F []       ys = 𝟎-left-annihilator-for-∧ F ((⋁ₗ[ F ] ys))
cnf-transform-correct F (x ∷ xs) ys =
 (x ∨[ F ] (⋁ₗ[ F ] xs)) ∧[ F ] (⋁ₗ[ F ] ys)                       ＝⟨ Ⅰ    ⟩
 (x ∧[ F ] (⋁ₗ[ F ] ys)) ∨[ F ] ((⋁ₗ[ F ] xs) ∧[ F ] (⋁ₗ[ F ] ys)) ＝⟨ Ⅱ    ⟩
 (x ∧[ F ] (⋁ₗ[ F ] ys)) ∨[ F ] cnf-transform F xs ys              ＝⟨ Ⅲ    ⟩
 (⋁ₗ[ F ] conjunct-with-list F x ys) ∨[ F ] cnf-transform F xs ys  ＝⟨ refl ⟩
 cnf-transform F (x ∷ xs) ys                                       ∎
  where
   Ⅰ = binary-distributivity-right F
   Ⅱ = ap
        (λ - → (x ∧[ F ] (⋁ₗ[ F ] ys)) ∨[ F ] -)
        (cnf-transform-correct F xs ys)
   Ⅲ = ap (λ - → - ∨[ F ] cnf-transform F xs ys) (distributivity-list F x ys)

\end{code}

We now start proving, making use of `cnf-transform-correct`, that the CNF
transformation of two basic opens is itself basic.

We first prove the analogous fact that the `conjunct-with-list` function:

\begin{code}

conjunct-with-list-is-basic : (F : Frame 𝓤 𝓥 𝓦) (ℬ : Fam 𝓦 ⟨ F ⟩)
                            → (β : is-basis-for F ℬ)
                            → closed-under-binary-meets F ℬ holds
                            → let
                               ℬ↑ = directify F ℬ
                               β↑ = directified-basis-is-basis F ℬ β
                              in
                               (i : index ℬ) (is : index ℬ↑) →
                                ∃ ks ꞉ index ℬ↑ ,
                                  ℬ↑ [ ks ]
                                  ＝ ⋁ₗ[ F ] (conjunct-with-list F (ℬ [ i ]) ((ℬ [_]) <$> is))
conjunct-with-list-is-basic F ℬ β p i []       = ∣ [] , refl ∣
conjunct-with-list-is-basic F ℬ β p i (j ∷ js) = ∥∥-rec ∃-is-prop γ μ
 where
  open Meets (λ x y → x ≤[ poset-of F ] y)

  ℬ↑ = directify F ℬ

\end{code}

We know by the closure of `ℬ` under binary meets that the meet of `ℬ[ i ]` and
`ℬ[ j ]` is in the basis, given by some index `k`.

\begin{code}

  μ : ∃ k ꞉ index ℬ , ((ℬ [ k ]) is-glb-of (ℬ [ i ] , ℬ [ j ])) holds
  μ = p i j

\end{code}

We unpack this truncated sigma inside `γ`:

\begin{code}

  γ : Σ k ꞉ index ℬ , ((ℬ [ k ]) is-glb-of (ℬ [ i ] , ℬ [ j ])) holds
    → ∃ ks ꞉ index ℬ↑ ,
       ℬ↑ [ ks ] ＝ ⋁ₗ[ F ] (conjunct-with-list F (ℬ [ i ]) ((ℬ [_]) <$> (j ∷ js)))
  γ (k , q) = ∥∥-rec ∃-is-prop δ IH
   where

\end{code}

Now, by the I.H. on `ℬ[ i ]`, we also get some `ks` corresponding to the index
of conjuncting `ℬ[ i ]` with each `ℬ[ j ]` given by `js.`

\begin{code}

    IH : ∃ ks ꞉ index ℬ↑ ,
          ℬ↑ [ ks ] ＝ ⋁ₗ[ F ] (conjunct-with-list F (ℬ [ i ]) ((ℬ [_]) <$> js))
    IH = conjunct-with-list-is-basic F ℬ β p i js

\end{code}

Once again, we unpack this truncated sigma inside `δ`:

\begin{code}

    δ : Σ ks ꞉ index ℬ↑ ,
         ℬ↑ [ ks ] ＝ ⋁ₗ[ F ] (conjunct-with-list F (ℬ [ i ]) ((ℬ [_]) <$> js))
      → ∃ ls ꞉ index ℬ↑ ,
         ℬ↑ [ ls ] ＝ ⋁ₗ[ F ] (conjunct-with-list F (ℬ [ i ]) ((ℬ [_]) <$> (j ∷ js)))
    δ (ks , r) = ∣ (k ∷ ks) , † ∣
     where

\end{code}

The list of indices that we need for the desired result is then simply `k ∷ ks`.
The proof that this satisfies the desired property is given in `†` below.

\begin{code}

      w = ⋁ₗ[ F ] (conjunct-with-list F (ℬ [ i ]) ((ℬ [_]) <$> js))

      † : ℬ↑ [ k ∷ ks ]
          ＝ ⋁ₗ[ F ] (conjunct-with-list F (ℬ [ i ]) ((ℬ [_]) <$> (j ∷ js)))
      † =
       ℬ [ k ] ∨[ F ] ℬ↑ [ ks ]                                        ＝⟨ Ⅰ    ⟩
       ℬ [ k ] ∨[ F ] w                                                ＝⟨ Ⅱ    ⟩
       (ℬ [ i ] ∧[ F ] ℬ [ j ]) ∨[ F ] w                               ＝⟨ refl ⟩
       ⋁ₗ[ F ] (conjunct-with-list F (ℬ [ i ]) ((ℬ [_]) <$> (j ∷ js))) ∎
        where
         Ⅰ = ap (λ - → ℬ [ k ] ∨[ F ] -) r
         Ⅱ = ap (λ - → - ∨[ F ] w) (∧[ F ]-unique q)

\end{code}

We are now ready to prove the desired result: that the meet of two basic opens
is basic.

\begin{code}

cnf-transform-is-basic : (F : Frame 𝓤 𝓥 𝓦) (ℬ : Fam 𝓦 ⟨ F ⟩)
                       → (β : is-basis-for F ℬ)
                       → closed-under-binary-meets F ℬ holds
                       → let
                          ℬ↑ = directify F ℬ
                          β↑ = directified-basis-is-basis F ℬ β
                         in
                          (is js : index ℬ↑) →
                           ∃ ks ꞉ index ℬ↑ ,
                            ℬ↑ [ ks ] ＝ (ℬ↑ [ is ]) ∧[ F ] (ℬ↑ [ js ])
cnf-transform-is-basic F ℬ β p [] js =
 ∣ [] , (𝟎-left-annihilator-for-∧ F (directify F ℬ [ js ]) ⁻¹) ∣
cnf-transform-is-basic F ℬ β p (i ∷ is) js =
 ∥∥-rec ∥∥-is-prop γ (cnf-transform-is-basic F ℬ β p is js)
  where
   ℬ↑ = directify F ℬ

\end{code}

We first record the following trivial `lemma`:

\begin{code}

   lemma : (is js : index ℬ↑)
         → ℬ↑ [ is ] ∧[ F ] ℬ↑ [ js ]
           ＝ join-in-frame′ F ℬ is ∧[ F ] join-in-frame′ F ℬ js
   lemma is js =
    let
      Ⅰ = ap
           (λ - → - ∧[ F ] ℬ↑ [ js ])
           (join-in-frame-equality F ℬ is)
      Ⅱ = ap
           (λ - → (⋁ₗ[ F ] ((ℬ [_]) <$> is)) ∧[ F ] -)
           (join-in-frame-equality F ℬ js)
    in
     ℬ↑ [ is ] ∧[ F ] ℬ↑ [ js ]                                   ＝⟨ Ⅰ ⟩
     (⋁ₗ[ F ] ((ℬ [_]) <$> is)) ∧[ F ] ℬ↑ [ js ]                  ＝⟨ Ⅱ ⟩
     (⋁ₗ[ F ] ((ℬ [_]) <$> is)) ∧[ F ] (⋁ₗ[ F ] ((ℬ [_]) <$> js)) ∎

\end{code}

In `γ`, we unpack the truncated sigma given by the I.H.:

\begin{code}

   γ : Σ ks ꞉ index ℬ↑ , ℬ↑ [ ks ] ＝ ℬ↑ [ is ] ∧[ F ] ℬ↑ [ js ]
     → ∃ ks ꞉ index ℬ↑ , ℬ↑ [ ks ] ＝ (ℬ [ i ] ∨[ F ] ℬ↑ [ is ]) ∧[ F ] ℬ↑ [ js ]
   γ (ks , q) =
    let

\end{code}

We know by `conjunct-with-list-is-basic` that there is a basis index
corresponding to `conjunct-with-list (ℬ [ i ]) ((ℬ [_]) <$> js)`. We refer to
this as `ls`.

\begin{code}

     † : ∃ ls ꞉ index ℬ↑ ,
          ℬ↑ [ ls ] ＝ ⋁ₗ[ F ] (conjunct-with-list F (ℬ [ i ]) ((ℬ [_]) <$> js))
     † = conjunct-with-list-is-basic F ℬ β p i js

    in

\end{code}

We proceed by truncation recursion on this truncated sigma, with the contents
unpacked in the function `δ`.

\begin{code}

     ∥∥-rec ∃-is-prop δ †
      where

\end{code}

As we will have to refer to `(ℬ [_]) <$> is` and `(ℬ [_]) <$> js` frequently,
we introduce abbrevations for them:

\begin{code}

       ℬ-is = (ℬ [_]) <$> is
       ℬ-js = (ℬ [_]) <$> js

\end{code}

Combining `lemma` and the correctness of `cnf-transform`, we have that `ℬ↑[ ks
]` is the CNF transformation of the meet of the joins of `is` and `js`.

\begin{code}

       ♣ : ℬ↑ [ ks ] ＝ cnf-transform F ((ℬ [_]) <$> is) ((ℬ [_]) <$> js)
       ♣ =
        ℬ↑ [ ks ]                                           ＝⟨ Ⅰ ⟩
        ℬ↑ [ is ] ∧[ F ] ℬ↑ [ js ]                          ＝⟨ Ⅱ ⟩
        (⋁ₗ[ F ] ℬ-is) ∧[ F ] (⋁ₗ[ F ] ((ℬ [_]) <$> js))    ＝⟨ Ⅲ ⟩
        cnf-transform F ℬ-is ((ℬ [_]) <$> js)               ∎
         where
          Ⅰ = q
          Ⅱ = lemma is js
          Ⅲ = cnf-transform-correct F ℬ-is ℬ-js

\end{code}

As `⋁ₗ[ F ] (conjunct-with-list F (ℬ [ i ]) ((ℬ [_]) <$> js))` is mentioned
quite frequently, we introduce the abbreviation `w` for it:

\begin{code}

       w = ⋁ₗ[ F ] (conjunct-with-list F (ℬ [ i ]) ((ℬ [_]) <$> js))

\end{code}

The desired list of indices is just `ls ++ ks`:

\begin{code}

       δ : (Σ ls ꞉ index ℬ↑ , ℬ↑ [ ls ] ＝ w)
         → ∃ ms ꞉ index ℬ↑ ,
            ℬ↑ [ ms ] ＝ (ℬ [ i ] ∨[ F ] ℬ↑ [ is ]) ∧[ F ] ℬ↑ [ js ]
       δ (ls , r) = ∣ (ls ++ ks) , ‡ ∣
        where

\end{code}

\begin{code}

        ‡ : ℬ↑ [ ls ++ ks ] ＝ (ℬ [ i ] ∨[ F ] ℬ↑ [ is ]) ∧[ F ] ℬ↑ [ js ]
        ‡ =
         ℬ↑ [ ls ++ ks ]                                        ＝⟨ Ⅰ    ⟩
         ℬ↑ [ ls ] ∨[ F ] ℬ↑ [ ks ]                             ＝⟨ Ⅱ    ⟩
         w ∨[ F ] ℬ↑ [ ks ]                                     ＝⟨ Ⅲ    ⟩
         w ∨[ F ] (cnf-transform F ℬ-is ℬ-js)                   ＝⟨ refl ⟩
         cnf-transform F ((ℬ [_]) <$> (i ∷ is)) ℬ-js            ＝⟨ Ⅳ    ⟩
         (⋁ₗ[ F ] ((ℬ [_]) <$> (i ∷ is))) ∧[ F ] (⋁ₗ[ F ] ℬ-js) ＝⟨ Ⅴ    ⟩
         (ℬ↑ [ i ∷ is ]) ∧[ F ] join-list F ℬ-js                ＝⟨ Ⅵ    ⟩
         (ℬ↑ [ i ∷ is ]) ∧[ F ] (ℬ↑ [ js ])                     ＝⟨ refl ⟩
         (ℬ [ i ] ∨[ F ] ℬ↑ [ is ]) ∧[ F ] (ℬ↑ [ js ])          ∎
          where
           Ⅰ = directify-functorial F ℬ ls ks
           Ⅱ = ap (λ - → - ∨[ F ] ℬ↑ [ ks ]) r
           Ⅲ = ap (λ - → w ∨[ F ] -) ♣
           Ⅳ = cnf-transform-correct F ((ℬ [_]) <$> (i ∷ is)) ℬ-js ⁻¹
           Ⅴ = ap
                (λ - → - ∧[ F ] (⋁ₗ[ F ] ℬ-js))
                (join-in-frame-equality F ℬ (i ∷ is) ⁻¹)
           Ⅵ = ap
                (λ - → (ℬ↑ [ i ∷ is ]) ∧[ F ] -)
                (join-in-frame-equality F ℬ js ⁻¹)

\end{code}

This is the result that we wanted: directification of a basis preserves its
closure under binary meets. In the following definition, we make this a bit more
explicit:

\begin{code}

directify-preserves-closure-under-∧ : (F : Frame 𝓤 𝓥 𝓦)
                                    → (ℬ : Fam 𝓦 ⟨ F ⟩)
                                    → (β : is-basis-for F ℬ)
                                    → closed-under-binary-meets F ℬ holds
                                    → let
                                       ℬ↑ = directify F ℬ
                                       β↑ = directified-basis-is-basis F ℬ β
                                      in
                                       closed-under-binary-meets F ℬ↑ holds
directify-preserves-closure-under-∧ F ℬ β ϑ is js =
 ∥∥-rec ∃-is-prop γ (cnf-transform-is-basic F ℬ β ϑ is js)
  where
   open Meets (λ x y → x ≤[ poset-of F ] y)

   ℬ↑ = directify F ℬ
   x  = ℬ↑ [ is ]
   y  = ℬ↑ [ js ]

   γ : Σ ks ꞉ (index ℬ↑) , ℬ↑ [ ks ] ＝ ℬ↑ [ is ] ∧[ F ] ℬ↑ [ js ]
     → ∃ ks ꞉ index ℬ↑ , (((ℬ↑ [ ks ]) is-glb-of (x , y)) holds)
   γ (ks , p) =
    let
     † : ((x ∧[ F ] y) is-glb-of (x , y)) holds
     † = (∧[ F ]-lower₁ x y  , ∧[ F ]-lower₂ x y)
       , λ (z , p) → uncurry (∧[ F ]-greatest x y z) p
    in
     ∣ ks , transport (λ - → (- is-glb-of (x , y)) holds) (p ⁻¹) † ∣

\end{code}

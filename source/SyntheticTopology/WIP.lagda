\begin{code}

{-# OPTIONS --safe --without-K --exact-split --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier

module SyntheticTopology.WIP
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist) where

open import Dominance.Definition
open import UF.Classifiers
open import UF.Embeddings
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.Logic
open import UF.Subsingletons-FunExt
open import UF.Univalence

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

problem with universes : can't define overtness of a subset of X : overt-subset
: { (X : 𝓤 ̇ ) → (U : X → Ω 𝓤) → is-overt U } fails as U lives in 𝓤 ⁺ ̇

The following is work in progress.

\begin{code}

 -- overt-charac : (X : 𝓤 ̇) → is-overt X → (Y : 𝓤 ̇) → (U : X × Y → Ω 𝓤)
 --                     → is-intrinsically-open U holds → {!!}
 -- overt-charac = {!!} --unfinished def for now

\end{code}

Dominance ≃ Sierpinski satisfying dominance

\begin{code}
{-
dominant-sierpinski : 𝓤 ⁺ ̇
dominant-sierpinski = Σ Si ꞉ Sierpinski-Object , (Sierpinski-notations.is-synthetic-dominance Si)

dom-equiv : dominant-sierpinski ≃ Dominance {𝓤 } {𝓤 ⁺}
dom-equiv = f , pf

  where

    f : dominant-sierpinski → Dominance
    f (Si , isdom) = d , d2 , d3 , d4 , d5
      where
        open Sierpinski-notations (Si)

        d : 𝓤 ̇ → 𝓤 ⁺  ̇
        d X = Σ p ꞉ is-prop X ,  is-affirmable (X , p) holds

        d2 : D2 d
        d2 X = Σ-is-prop (being-prop-is-prop fe) λ _ → ∃-is-prop -- see "being-subingleton-is-subsingleton" lemma using fe in HoTT-UF-Agda

        d3 : D3 d
        d3 X dx = pr₁ dx

        d4 : d 𝟙
        d4 = 𝟙-is-prop ,  (pr₁ isdom)

        d5' : D5' d
        d5' P Q' dP P-to-dQ' = (×-is-prop (d3 P dP) {!!}) , {!!}

        d5 :  D5 d
        d5 = D3-and-D5'-give-D5 pe d d3 d5'

    pf : is-equiv f
    pf = {!!}
-}

-- --}
-- --}

\end{code}



[1]: https://ncatlab.org/nlab/show/analytic+versus+synthetic

We

 is-compact : 𝓤 ̇  → 𝓤 ⁺ ̇
 is-compact X = (P : X → Ω 𝓤)
                         → is-intrinsically-open′ P holds
                         → is-affirmable (Ɐ x ꞉ X , (P x)) holds

 𝟙-is-compact : is-compact 𝟙
 𝟙-is-compact P = ∥∥-rec (holds-is-prop ( is-affirmable (Ɐ x ꞉ 𝟙 , (P x)))) †
   where
     † :  (Σ h ꞉ (𝟙 → S) , ((x : 𝟙) → P x holds ↔ ι (h x) holds))
             → is-affirmable (Ɐ x ꞉ 𝟙 , (P x)) holds
     † (h , φ) = ∣ h ⋆ , r  ∣

      where
       p : ((Ɐ x ꞉ 𝟙 , P x) ⇔ P ⋆) holds
       p =  (λ f → f ⋆) , (λ pstar  x → pstar)

       q : ((ι (h ⋆)) ⇔ (Ɐ x ꞉ 𝟙 , P x)) holds
       q = ↔-sym (↔-trans p (φ ⋆))

       r : ι (h ⋆) ＝ (Ɐ x ꞉ 𝟙 , P x)
       r =  ⇔-gives-＝ pe (ι (h ⋆))  (Ɐ x ꞉ 𝟙 , P x)
                      (holds-gives-equal-⊤ pe fe ((ι (h ⋆)) ⇔(Ɐ x ꞉ 𝟙 , P x)) q)


{-  Commented : annoying to have a hole while working
 ×-is-compact : {X Y : 𝓤 ̇ }
                            → is-compact X
                            → is-compact Y
                            → is-compact ( X × Y )

 ×-is-compact {X} {Y}  kX kY P =  ∥∥-rec (holds-is-prop ( is-affirmable (Ɐ z ꞉ (X × Y) , P z))) t
   where
    t : Σ h ꞉ (X × Y → S) , ((z : (X × Y)) → P z holds ↔ ι (h z) holds) →
          is-affirmable (Ɐ z ꞉ (X × Y) ,  P z) holds
    t (h , φ) = transport (_holds ∘ is-affirmable) (q ⁻¹) †

      where
       p : ((Ɐ z ꞉ (X × Y) , P z) ⇔ (Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y)))) holds
       p = (λ Qz x' y' → Qz (x' , y') ) , λ Qxy z → Qxy (pr₁ z) (pr₂ z)

       q : (Ɐ z ꞉ (X × Y) , P z) ＝ (Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y)))
       q = ⇔-gives-＝ pe  (Ɐ z ꞉ (X × Y) , P z) (Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y)))
                     (holds-gives-equal-⊤ pe fe ( ((Ɐ z ꞉ (X × Y) , P z) ⇔ (Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y))))) p)

       † : is-affirmable (Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y)))  holds
       † = kX (λ x → (Ɐ y ꞉ Y , P (x , y))) {!!}  -- stuck here :  we cannot extract the witness from "try x"

        where
         try : (x : X) → is-affirmable (Ɐ y ꞉ Y , P (x , y)) holds
         try x = kY (λ y → P (x , y)) ∣ (λ y → h (x , y)) , (λ y → φ (x , y))  ∣
-}

\end{code}

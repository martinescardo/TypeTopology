-------------------------------------------------------------------------------
authors:      ["Ayberk Tosun", "Martin Trucchi"]
date-started: 2024-05-02
--------------------------------------------------------------------------------

\begin{code}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.SubtypeClassifier


module SyntheticTopology.SierpinskiObject
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

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)


\end{code}

What is a Sierpiński object? In Definition 2.4 of Davorin Lesnik's thesis, it is
defined simply as a subobject of the subobject classifier.

\begin{code}

Sierpinski-Object : 𝓤 ⁺  ̇
Sierpinski-Object = Subtypes' 𝓤  (Ω 𝓤)

Sierpinski-Object′ : 𝓤 ⁺  ̇
Sierpinski-Object′ = Ω 𝓤 → Ω 𝓤

index : Sierpinski-Object → 𝓤  ̇
index (I , α , _) = I

sierpinski-fun : (𝕊 : Sierpinski-Object) → index 𝕊 → Ω 𝓤
sierpinski-fun (_ , α , _) = α

\end{code}

In the module below, we assume the existence of a Sierpiński object `𝕊` and
define some notions _synthetically_. The meaning of "synthetic" here can be
understood through its contradiction with the analytic [1]. Instead of analyzing
topological notions, we synthesize them: we formulate them in terms of the
Sierpiński object.

\begin{code}

module Sierpinski-notations (𝕊 : Sierpinski-Object) where

 ι : index 𝕊 → Ω 𝓤
 ι = sierpinski-fun 𝕊

 S : 𝓤  ̇
 S = index 𝕊

\end{code}

The propositions in `Ω` that fall in the subset delineated by the Sierpiński
object are called _affirmable.

\begin{code}

 is-affirmable : Ω 𝓤 → Ω (𝓤 ⁺)
 is-affirmable P = P ∈image ι , ∃-is-prop

\end{code}

\begin{code}

 is-intrinsically-open′ : {X : 𝓤  ̇} → (X → Ω 𝓤) → Ω (𝓤 ⁺)
 is-intrinsically-open′ {X} P = Ɐ x ꞉ X , is-affirmable (P x)

\end{code}

\begin{code}

 is-intrinsically-open : {X : 𝓤  ̇} → (X → Ω 𝓤) → Ω 𝓤
 is-intrinsically-open {X} P =
  Ǝₚ h ꞉ (X → S) , (Ɐ x ꞉ X , P x ⇔ ι (h x))

\end{code}

\begin{code}

 open-implies-open′ : {X : 𝓤  ̇} → (P : X → Ω 𝓤)
                    → (is-intrinsically-open  P ⇒ is-intrinsically-open′ P) holds
 open-implies-open′ {X} P = ∥∥-rec (holds-is-prop (is-intrinsically-open′ P)) †
  where
   † : (Σ h ꞉ (X → S) , ((x : X) → P x holds ↔ ι (h x) holds))
     → is-intrinsically-open′ P holds
   † (h , φ) x = transport (_holds ∘ is-affirmable) (q ⁻¹) ∣ (h x) , refl ∣
    where
     p : (P x ⇔ ι (h x)) holds
     p = φ x

     q : P x ＝ ι (h x)
     q = ⇔-gives-＝ pe (P x) (ι (h x)) (holds-gives-equal-⊤ pe fe (P x ⇔ ι (h x)) p)

\end{code}

Question: are these two definitions equivalent?


Dominance axiom and Phoa's principle :

\begin{code}

 openness-is-transitive : (𝓤 ⁺) ̇
 openness-is-transitive = (u : Ω 𝓤) → (is-affirmable u) holds → (p : Ω 𝓤) → (u holds → (is-affirmable p) holds) → (is-affirmable (u ∧ p) ) holds

 contains-top : Ω (𝓤 ⁺)
 contains-top = is-affirmable ⊤

 is-synthetic-dominance : (𝓤 ⁺) ̇
 is-synthetic-dominance = contains-top holds × openness-is-transitive

 phoa-condition : Ω (𝓤 ⁺)
 phoa-condition =
  Ɐ f ꞉ (Ω 𝓤 → Ω 𝓤) , Ɐ U ꞉ Ω 𝓤 , is-affirmable U ⇒ f U ⇔ (f ⊥ ∨  U) ∧ f ⊤

\end{code}

Compactness :

\begin{code}

 is-compact : 𝓤 ̇  → 𝓤 ⁺ ̇
 is-compact X = (P : X → Ω 𝓤)
                         → is-intrinsically-open P holds
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
       † = kX (λ x → (Ɐ y ꞉ Y , P (x , y))) {!!} -- stuck here :  we cannot extract the witness from "try x"

        where
         try : (x : X) → is-affirmable (Ɐ y ꞉ Y , P (x , y)) holds
         try x = kY (λ y → P (x , y)) ∣ (λ y → h (x , y)) , (λ y → φ (x , y))  ∣ 

\end{code}

Compact : prime-version

\begin{code}

 is-compact' : 𝓤 ̇  → 𝓤 ⁺ ̇
 is-compact' X = (P : X → Ω 𝓤)
                         → is-intrinsically-open′ P holds
                         → is-affirmable (Ɐ x ꞉ X , (P x)) holds

 𝟙-is-compact' : is-compact' 𝟙
 𝟙-is-compact' P iP = transport (_holds ∘ is-affirmable) (r ⁻¹) (iP ⋆)
   where
     p : ((Ɐ x ꞉ 𝟙 , P x) ⇔ P ⋆) holds
     p =  (λ f → f ⋆) , (λ pstar  x → pstar)

     r :  (Ɐ x ꞉ 𝟙 , P x) ＝ (P ⋆)
     r =  ⇔-gives-＝ pe (Ɐ x ꞉ 𝟙 , P x) (P ⋆) (holds-gives-equal-⊤ pe fe ((Ɐ x ꞉ 𝟙 , P x) ⇔ P ⋆)  p)

 ×-is-compact' : {X Y : 𝓤 ̇ }
                            → is-compact' X
                            → is-compact' Y
                            → is-compact' ( X × Y )

 ×-is-compact' {X} {Y} kX kY P iP = transport (_holds ∘ is-affirmable) (q ⁻¹) †

   where
    p : ((Ɐ z ꞉ (X × Y) , P z) ⇔ (Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y)))) holds
    p = (λ Qz x' y' → Qz (x' , y') ) , λ Qxy z → Qxy (pr₁ z) (pr₂ z)

    q : (Ɐ z ꞉ (X × Y) , P z) ＝ (Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y))) 
    q = ⇔-gives-＝ pe  (Ɐ z ꞉ (X × Y) , P z) (Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y)))
                    (holds-gives-equal-⊤ pe fe ( ((Ɐ z ꞉ (X × Y) , P z) ⇔ (Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y))))) p)

    † : is-affirmable (Ɐ x ꞉ X , (Ɐ y ꞉ Y ,  P (x , y)))  holds
    † = kX (λ x → (Ɐ y ꞉ Y , (P (x , y)))) (λ x → (kY (λ y → (P (x , y))) (λ y → iP ((x , y))))) 

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

\end{code}



[1]: https://ncatlab.org/nlab/show/analytic+versus+synthetic

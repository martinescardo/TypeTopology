-------------------------------------------------------------------------------
authors:      [Ayberk Tosun]
date-started: 2024-05-02
--------------------------------------------------------------------------------
c
\begin{code}

open import MLTT.Spartan
open import UF.Embeddings
open import UF.SubtypeClassifier
open import UF.FunExt
open import UF.PropTrunc
open import UF.Classifiers
open import UF.Subsingletons
open import UF.Equiv
open import Dominance.Definition


module SyntheticTopology.SierpinskiObject
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist) where

open import UF.Logic
open import UF.ImageAndSurjection pt


open AllCombinators pt fe
open PropositionalTruncation pt


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

 contains-top : (𝓤 ⁺) ̇ 
 contains-top = is-affirmable ⊤ holds

 is-synthetic-dominance : (𝓤 ⁺) ̇
 is-synthetic-dominance = contains-top × openness-is-transitive
 
 phoa-condition : (𝓤 ⁺) ̇ 
 phoa-condition =  (f : Ω 𝓤 → Ω 𝓤) (u : Ω 𝓤) → (is-affirmable u) holds → f u ＝ ((Disjunction._∨_ pt (f ⊥)  u) ∧ f ⊤)

\end{code}

Compactness : 

\begin{code}
{-
 is-compact : (X : 𝓤 ̇ ) → 𝓤 ⁺ ̇ 
 is-compact X = (P : X → Ω 𝓤) → is-intrinsically-open P holds →  (is-affirmable (Ɐ x ꞉ X , (P x)) holds)

 𝟙-is-compact : is-compact 𝟙
 𝟙-is-compact P h = t
   where
     to-star : (Ɐ x ꞉ 𝟙 ,  (P x ⇔ P ⋆)) holds -- useful ?
     to-star = λ x → transport (λ z → (P z ⇔ P ⋆) holds ) refl  (id , id )

     t : (Ɐ x ꞉ 𝟙 , (P x)) ∈image ι 
     t = {!!}  -- What does index 𝕊 looks like ?
-}
\end{code}

Dominance ≃ Sierpinski satisfying dominance

\begin{code}

dominant-sierpinski : 𝓤 ⁺ ̇
dominant-sierpinski = Σ Si ꞉ Sierpinski-Object , (Sierpinski-notations.is-synthetic-dominance Si)

dom-equiv : dominant-sierpinski ≃ Dominance {𝓤 } {𝓤 ⁺}
dom-equiv = f , pf

  where
  
    f : dominant-sierpinski → Dominance
    f (Si , isdom) = d , d2 , d3 , d4 , d5
      where
        open Sierpinski-notations (Si)
        
        d : (𝓤 ) ̇ → (𝓤 ⁺) ̇
        d X = Σ p ꞉ is-prop X ,  is-affirmable (X , p) holds

        d2 : D2 d
        d2 X = Σ-is-prop {!!} λ _ → ∃-is-prop -- see "being-subingleton-is-subsingleton" lemma using fe in HoTT-UF-Agda 
         
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

   
\end{code}



[1]: https://ncatlab.org/nlab/show/analytic+versus+synthetic



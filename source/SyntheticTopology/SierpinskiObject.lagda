-------------------------------------------------------------------------------
authors:      ["Ayberk Tosun", "Martin Trucchi"]
date-started: 2024-05-02
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --safe --without-K --exact-split --auto-inline #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
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

Useful lemmas , which shorten proofs (maybe move it elsewhere at some point)

\begin{code}

 ⇔-transport : {P Q : Ω 𝓤} → (𝓟 : Ω 𝓤 → 𝓤 ⁺ ̇) → ((P ⇔ Q) holds) → (𝓟 P) → (𝓟 Q)
 ⇔-transport {P} {Q} (𝓟) P-iff-Q Prop-P = transport 𝓟 q Prop-P
   where
    q : P ＝ Q
    q = ⇔-gives-＝ pe P Q (holds-gives-equal-⊤ pe fe (P ⇔ Q) P-iff-Q)

 ⇔-affirmable : {P Q : Ω 𝓤} → ((P ⇔ Q) holds) → (is-affirmable P holds) → (is-affirmable Q holds)
 ⇔-affirmable = ⇔-transport (_holds ∘ is-affirmable)

\end{code}

\begin{code}

 open-implies-open′ : {X : 𝓤  ̇} → (P : X → Ω 𝓤)
                    → (is-intrinsically-open  P ⇒ is-intrinsically-open′ P) holds
 open-implies-open′ {X} P = ∥∥-rec (holds-is-prop (is-intrinsically-open′ P)) †
  where
   † : (Σ h ꞉ (X → S) , ((x : X) → P x holds ↔ ι (h x) holds))
     → is-intrinsically-open′ P holds
   † (h , φ) x = ⇔-affirmable p ∣ (h x) , refl ∣
    where
     p : (ι (h x) holds) ↔ (P x holds)
     p = ↔-sym (φ x)

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

Compact : prime-version

\begin{code}

 is-compact' : 𝓤 ̇  → 𝓤 ⁺ ̇
 is-compact' X = (P : X → Ω 𝓤)
                         → is-intrinsically-open′ P holds
                         → is-affirmable (Ɐ x ꞉ X , (P x)) holds

 𝟙-is-compact' : is-compact' 𝟙
 𝟙-is-compact' P iP = ⇔-affirmable  p (iP ⋆)
   where
     p : (P ⋆ ⇔ (Ɐ x ꞉ 𝟙 , P x)) holds
     p = (λ pstar  x → pstar) , (λ f → f ⋆)


 ×-is-compact' : {X Y : 𝓤 ̇ }
                            → is-compact' X
                            → is-compact' Y
                            → is-compact' ( X × Y )

 ×-is-compact' {X} {Y} kX kY P iP = ⇔-affirmable p † 

   where
    p : ((Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y))) ⇔ (Ɐ z ꞉ (X × Y) , P z) ) holds
    p =  (λ Qxy z → Qxy (pr₁ z) (pr₂ z)) , (λ Qz x' y' → Qz (x' , y') )

    † : is-affirmable (Ɐ x ꞉ X , (Ɐ y ꞉ Y ,  P (x , y)))  holds
    † = kX (λ x → (Ɐ y ꞉ Y , (P (x , y)))) (λ x → (kY (λ y → (P (x , y))) (λ y → iP ((x , y))))) 

 image-of-compact' : {X Y : 𝓤 ̇ }
                                    → (f : X → Y)
                                    → is-surjection f
                                    → is-compact' X
                                    → is-compact' Y

 image-of-compact' {X} {Y} f surf kX P iP = ⇔-affirmable p † 

   where
    p : ((Ɐ x ꞉ X , P (f x)) ⇔ (Ɐ y ꞉ Y , P y)) holds
    p = (λ pX y → surjection-induction f surf (_holds ∘ P) (λ y → holds-is-prop (P y)) pX y) , (λ pY x → pY (f x))
    
    † : is-affirmable (Ɐ x ꞉ X , P (f x)) holds
    † = kX (λ x → P (f x)) (λ x → iP (f x))

\end{code}

Discrete spaces

\begin{code}

 is-discrete-trunc : 𝓤 ̇ → 𝓤 ⁺ ̇
 is-discrete-trunc X = is-intrinsically-open′ (λ ((x , y) : X × X) → (∥ x ＝ y ∥ , ∥∥-is-prop )) holds -- Or should we directly  require X to be a set ? Truncation inside an → : nightmare
 
 is-discrete-set : (X : 𝓤 ̇) → is-set X → 𝓤 ⁺ ̇
 is-discrete-set X setX =  is-intrinsically-open′ (λ ((x , y) : X × X) → ((x ＝ y) , setX  )) holds -- Works better for proving that compact product of discrete is discrete

 -- In Lesnik's thesis, everything is mentionned as "sets".
 -- But discussion right before  prop 2.8 suggests that "_＝_" should be an "open predicate", which implies that "x ＝ y" lies in Ω 𝓤 (⁺)

 𝟙-is-discrete-trunc : contains-top holds →  is-discrete-trunc 𝟙
 𝟙-is-discrete-trunc ct  = λ (⋆ , ⋆) → ∥∥-rec (holds-is-prop (is-affirmable (∥ ⋆ ＝ ⋆ ∥ , ∥∥-is-prop ))) † ct
   where
     † : Σ (λ x → ι x ＝ ⊤) → is-affirmable (∥ ⋆ ＝ ⋆ ∥ , ∥∥-is-prop) holds
     † (⊤⁻¹ , φ) = ∣ ⊤⁻¹ , ⇔-gives-＝ pe (ι ⊤⁻¹) (∥ ⋆ ＝ ⋆ ∥ , ∥∥-is-prop) (holds-gives-equal-⊤ pe fe ( ι ⊤⁻¹ ⇔ ∥ ⋆ ＝ ⋆ ∥ , ∥∥-is-prop)  p)  ∣

      where
       p : (ι ⊤⁻¹ ⇔ ∥ ⋆ ＝ ⋆ ∥ , ∥∥-is-prop) holds
       p = (λ _ → ∣ refl  ∣ ) , λ _ → transport _holds (φ ⁻¹) ⊤-holds 


 compact-Π-discrete-set : (K : 𝓤 ̇) → (X : K → 𝓤 ̇)
                                                        → is-compact' K
                                                        → (set-certificate : ((k : K) → is-set (X k)))
                                                        → ((k : K) → is-discrete-set (X k) (set-certificate k) )
                                                        → is-discrete-set (Π X) (Π-is-set fe set-certificate)
                                                        
 compact-Π-discrete-set K X kK set-certificate dX (x₁ , x₂) = ⇔-affirmable p †
 
   where
    p :  ((k : K) →  ( (x₁ k) ＝ (x₂ k) ) ) ↔ (x₁ ＝ x₂)
    p = (dfunext fe)
           ,  ( λ x₁-equal-x₂ → transport (λ - → ((k : K) → (( x₁ k ) ＝( - k) ))) x₁-equal-x₂ (λ _ → refl))
           -- there is certainly some magic function in funext's family doing the job but I have not found it

    † : is-affirmable ((Ɐ k ꞉ K , ( ( (x₁ k) ＝ (x₂ k) ) , set-certificate k ))) holds
    † = kK (λ k → (x₁ k ＝ x₂ k) , set-certificate k) (λ k → dX k (x₁ k , x₂ k)) 

\end{code}

Overtness :

\begin{code}

 is-overt : 𝓤 ̇  → 𝓤 ⁺ ̇  
 is-overt X = (P : X → Ω 𝓤)
                         → is-intrinsically-open′ P holds
                         → is-affirmable (Ǝₚ x ꞉ X , (P x) ) holds

-- problem with universes : can't define overtness of a subset of X :
-- overt-subset : { (X : 𝓤 ̇ ) → (U : X → Ω 𝓤) → is-overt U } fails as U lives in 𝓤 ⁺ ̇ 

 overt-charac : (X : 𝓤 ̇) → is-overt X → (Y : 𝓤 ̇) → (U : X × Y → Ω 𝓤)
                     → is-intrinsically-open′ U holds → {!!}
 overt-charac = {!!} --unfinished def for now

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

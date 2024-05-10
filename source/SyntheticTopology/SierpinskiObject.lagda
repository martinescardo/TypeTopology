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
open import UF.Univalence

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)

\end{code}

What is a Sierpiński object? In Definition 2.4 of Davorin Lesnik's thesis, it is
defined simply as a subobject of the subobject classifier (in some topos). This
idea goes back to Martín Escardó’s Barbados Notes.

In the setting of type theory, we define it as a subtype over `Ω_{𝓤}` (for some
universe 𝓤).

\begin{code}

Sierpinski-Object : 𝓤 ⁺  ̇
Sierpinski-Object = Subtypes' 𝓤  (Ω 𝓤)

\end{code}

We define some notation to refer to components of a Sierpiński object.

\begin{code}

index : Sierpinski-Object → 𝓤  ̇
index (I , α , _) = I

sierpinski-fun : (𝕊 : Sierpinski-Object) → index 𝕊 → Ω 𝓤
sierpinski-fun (_ , α , _) = α

\end{code}

In the module below, we assume the existence of a Sierpiński object `𝕊` and
define some notions _synthetically_, following the work of Martín Escardó (and
Davorin Lešnik).

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

A subset of a type is said to be intrinsically open if it is a predicate defined
by affirmable propositions.

\begin{code}

 is-intrinsically-open : {X : 𝓤  ̇} → (X → Ω 𝓤) → Ω (𝓤 ⁺)
 is-intrinsically-open {X} P = Ɐ x ꞉ X , is-affirmable (P x)

\end{code}

Another way to define this notion, which is equivalent assuming choice, is the
following:

\begin{code}

 is-intrinsically-open′ : {X : 𝓤  ̇} → (X → Ω 𝓤) → Ω 𝓤
 is-intrinsically-open′ {X} P =
  Ǝₚ h ꞉ (X → S) , (Ɐ x ꞉ X , P x ⇔ ι (h x))

\end{code}

The former definition turns out to more useful in our case.

Useful lemmas, which shorten proofs (maybe move it elsewhere at some point)

\begin{code}

 ⇔-transport : {P Q : Ω 𝓤} → (𝓟 : Ω 𝓤 → 𝓤 ⁺ ̇) → ((P ⇔ Q) holds) → (𝓟 P) → (𝓟 Q)
 ⇔-transport {P} {Q} (𝓟) P-iff-Q Prop-P = transport 𝓟 q Prop-P
   where
    q : P ＝ Q
    q = ⇔-gives-＝ pe P Q (holds-gives-equal-⊤ pe fe (P ⇔ Q) P-iff-Q)

 ⇔-affirmable : {P Q : Ω 𝓤}
              → ((P ⇔ Q) ⇒ is-affirmable P ⇒ is-affirmable Q) holds
 ⇔-affirmable = ⇔-transport (_holds ∘ is-affirmable)

\end{code}

The definition `is-intrinsically-open′` is stronger than is-intrinsically-open.

\begin{code}

 open-implies-open′ : {X : 𝓤  ̇} → (P : X → Ω 𝓤)
                    → (is-intrinsically-open′  P ⇒ is-intrinsically-open P) holds
 open-implies-open′ {X} P = ∥∥-rec (holds-is-prop (is-intrinsically-open P)) †
  where
   † : (Σ h ꞉ (X → S) , ((x : X) → P x holds ↔ ι (h x) holds))
     → is-intrinsically-open P holds
   † (h , φ) x = ⇔-affirmable p ∣ (h x) , refl ∣
    where
     p : (ι (h x) holds) ↔ (P x holds)
     p = ↔-sym (φ x)

\end{code}

We are now ready to write down the Dominance Axiom and Phoa’s Principle.

First, the Dominance Axiom:

\begin{code}

 openness-is-transitive : (𝓤 ⁺) ̇
 openness-is-transitive = (u : Ω 𝓤) → (is-affirmable u) holds → (p : Ω 𝓤) → (u holds → (is-affirmable p) holds) → (is-affirmable (u ∧ p) ) holds

 contains-top : Ω (𝓤 ⁺)
 contains-top = is-affirmable ⊤

 is-synthetic-dominance : (𝓤 ⁺) ̇
 is-synthetic-dominance = contains-top holds × openness-is-transitive

\end{code}

Phoa’s Principle:

\begin{code}

 phoa’s-principle : Ω (𝓤 ⁺)
 phoa’s-principle =
  Ɐ f ꞉ (Ω 𝓤 → Ω 𝓤) , Ɐ U ꞉ Ω 𝓤 , is-affirmable U ⇒ f U ⇔ (f ⊥ ∨  U) ∧ f ⊤

\end{code}

\section{Compactness}

We now start to investigate some notions of compactness.

A type `X` is called compact if its universal quantification on intrinsically
open predicates is affirmable.

\begin{code}

 is-compact' : 𝓤 ̇  → Ω (𝓤 ⁺)
 is-compact' X =
  Ɐ P ꞉ (X → Ω 𝓤) , is-intrinsically-open P ⇒ is-affirmable (Ɐ x ꞉ X , (P x))

\end{code}

The type `𝟙` is compact i.e. the empty product is compact.

\begin{code}

 𝟙-is-compact : is-compact' 𝟙 holds
 𝟙-is-compact P φ = ⇔-affirmable p (φ ⋆)
  where
   p : (P ⋆ ⇔ (Ɐ x ꞉ 𝟙 , P x)) holds
   p = (λ pstar  x → pstar) , (λ f → f ⋆)

\end{code}

Binary products of compact types are compact.

\begin{code}

 ×-is-compact' : {X Y : 𝓤 ̇ }
               → is-compact' X holds
               → is-compact' Y holds
               → is-compact'(X × Y) holds
 ×-is-compact' {X} {Y} kX kY P iP = ⇔-affirmable p †
  where
   p : ((Ɐ x ꞉ X , (Ɐ y ꞉ Y , P (x , y))) ⇔ (Ɐ z ꞉ (X × Y) , P z) ) holds
   p =  (λ Qxy z → Qxy (pr₁ z) (pr₂ z)) , (λ Qz x' y' → Qz (x' , y') )

   † : is-affirmable (Ɐ x ꞉ X , (Ɐ y ꞉ Y ,  P (x , y)))  holds
   † = kX (λ x → (Ɐ y ꞉ Y , (P (x , y)))) (λ x → (kY (λ y → (P (x , y))) (λ y → iP ((x , y)))))

\end{code}

Images of compact types are compact.

\begin{code}

 image-of-compact' : {X Y : 𝓤 ̇ }
                   → (f : X → Y)
                   → is-surjection f
                   → is-compact' X holds
                   → is-compact' Y holds
 image-of-compact' {X} {Y} f surf kX P iP = ⇔-affirmable p †
  where
   p : ((Ɐ x ꞉ X , P (f x)) ⇔ (Ɐ y ꞉ Y , P y)) holds
   p = (λ pX y → surjection-induction f surf (_holds ∘ P) (λ y → holds-is-prop (P y)) pX y)
     , (λ pY x → pY (f x))

   † : is-affirmable (Ɐ x ꞉ X , P (f x)) holds
   † = kX (P ∘ f) (iP ∘ f)

\end{code}

\section{Discrete spaces}

\begin{code}

 is-discrete-trunc : 𝓤 ̇ → 𝓤 ⁺ ̇
 is-discrete-trunc X = is-intrinsically-open (λ ((x , y) : X × X) → (∥ x ＝ y ∥ , ∥∥-is-prop )) holds

\end{code}

Question: in the definition above, should we directly require X to be a set?

Truncation inside an → : nightmare

\begin{code}

 is-discrete-set : (X : 𝓤 ̇) → is-set X → 𝓤 ⁺ ̇
 is-discrete-set X setX =
  is-intrinsically-open
   (λ ((x , y) : X × X) → ((x ＝ y) , setX))
    holds

\end{code}

Works better for proving that compact product of discrete is discrete.

In Lesnik's thesis, everything is mentionned as "sets". But discussion right
before prop 2.8 suggests that "_＝_" should be an "open predicate", which
implies that "x ＝ y" lies in Ω 𝓤 (⁺)

\begin{code}

 𝟙-is-discrete-trunc : contains-top holds →  is-discrete-trunc 𝟙
 𝟙-is-discrete-trunc ct =
  λ (⋆ , ⋆) → ∥∥-rec (holds-is-prop (is-affirmable (∥ ⋆ ＝ ⋆ ∥ , ∥∥-is-prop ))) † ct
   where
     † : Σ (λ x → ι x ＝ ⊤)
       → is-affirmable (∥ ⋆ ＝ ⋆ ∥ , ∥∥-is-prop) holds
     † (⊤⁻¹ , φ) =
      ∣ ⊤⁻¹ , ⇔-gives-＝ pe (ι ⊤⁻¹) (∥ ⋆ ＝ ⋆ ∥ , ∥∥-is-prop) (holds-gives-equal-⊤ pe fe ( ι ⊤⁻¹ ⇔ ∥ ⋆ ＝ ⋆ ∥ , ∥∥-is-prop)  p)  ∣
       where
        p : (ι ⊤⁻¹ ⇔ ∥ ⋆ ＝ ⋆ ∥ , ∥∥-is-prop) holds
        p = (λ _ → ∣ refl  ∣ ) , λ _ → transport _holds (φ ⁻¹) ⊤-holds

\end{code}

\begin{code}

 compact-Π-discrete-set : (K : 𝓤 ̇) → (X : K → 𝓤 ̇)
                        → is-compact' K holds
                        → (set-certificate : ((k : K) → is-set (X k)))
                        → ((k : K) → is-discrete-set (X k) (set-certificate k) )
                        → is-discrete-set (Π X) (Π-is-set fe set-certificate)
 compact-Π-discrete-set K X kK 𝓈 dX (x₁ , x₂) = ⇔-affirmable p †

   where
    p :  ((k : K) →  ( (x₁ k) ＝ (x₂ k) ) ) ↔ (x₁ ＝ x₂)
    p = dfunext fe
      , (λ x₁-equal-x₂ → transport (λ - → ((k : K) → (( x₁ k ) ＝( - k) ))) x₁-equal-x₂ (λ _ → refl))
   -- there is certainly some magic function in funext's family doing the job but I have not found it

    † : is-affirmable (Ɐ k ꞉ K , ((x₁ k ＝ x₂ k) , 𝓈 k)) holds
    † = kK (λ k → (x₁ k ＝ x₂ k) , 𝓈 k) (λ k → dX k (x₁ k , x₂ k))

\end{code}

Overtness:

\begin{code}

 is-overt : 𝓤  ̇ → Ω (𝓤 ⁺)
 is-overt X =
  Ɐ P ꞉ (X → Ω 𝓤) , is-intrinsically-open P ⇒ is-affirmable (Ǝₚ x ꞉ X , P x)

\end{code}

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
open import UF.UniverseEmbedding

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


⇔-transport : {𝓥 𝓦 : Universe} {P Q : Ω 𝓥} → (𝓟 : Ω 𝓥 → 𝓦 ̇) → ((P ⇔ Q) holds) → (𝓟 P) → (𝓟 Q)
⇔-transport {𝓥} {𝓦} {P} {Q} (𝓟) P-iff-Q Prop-P = transport 𝓟 q Prop-P
  where
   q : P ＝ Q
   q = ⇔-gives-＝ pe P Q (holds-gives-equal-⊤ pe fe (P ⇔ Q) P-iff-Q)


\end{code}

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
 openness-is-transitive = (u : Ω 𝓤)
                                         → (is-affirmable u) holds
                                         → (p : Ω 𝓤)
                                         → (u holds → (is-affirmable p) holds)
                                         → (is-affirmable (u ∧ p) ) holds

 contains-top : Ω (𝓤 ⁺)
 contains-top = is-affirmable (⊤ {𝓤})

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

 countable-are-overt : (is-overt (Lift 𝓤 ℕ) holds) → (is-overt (𝟘 {𝓤}) holds) → (X : 𝓤 ̇) → (f : ( (Lift 𝓤 ℕ) → (𝟙 {𝓤} ) + X)) → (is-surjection f) → (is-overt X holds) 
 countable-are-overt overt-ℕ overt-𝟘 X f surf = λ P open-P → ⇔-affirmable (eq P) († P open-P)

  where
  
   lemma₁ : is-overt (𝟙 {𝓤} + X) holds
   lemma₁ = λ Q open-Q → ∥∥-rec (holds-is-prop (is-affirmable (Ǝₚ x ꞉ (𝟙 {𝓤} + X) , Q x))) (†' Q) (overt-ℕ (λ n → Q (f n)) (λ n → open-Q (f n)))

     where
      †' : (Q : 𝟙 + X → Ω 𝓤) → Σ (λ x → ι x ＝ (Ǝₚ n ꞉ (Lift 𝓤 ℕ) , Q (f n))) → is-affirmable ((Ǝₚ x ꞉ (𝟙 + X) ,  Q x)) holds
      †' Q (h , φ) = ∣ h , (φ ∙ q Q)  ∣

       where 
        p :  (Q : 𝟙 + X → Ω 𝓤) → (Ǝₚ n ꞉ (Lift 𝓤 ℕ) , Q (f n) ⇔ Ǝₚ x ꞉ (𝟙 + X) , Q x)  holds
        p Q = ( λ ex-ℕ → ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ (𝟙 + X) , Q x)) (λ (n , pn) → ∣ f n , pn  ∣) ex-ℕ  ) ,
                λ ex-X → ∥∥-rec (holds-is-prop (Ǝₚ n ꞉ (Lift 𝓤 ℕ) , Q (f n))) ((λ (x , px) → ∥∥-rec (holds-is-prop (Ǝₚ n ꞉ (Lift 𝓤 ℕ) , Q (f n))) ((λ (n , fnx) → ∣ n , transport (λ v → pr₁ (Q v)) (fnx ⁻¹) px  ∣)) (surf x))) ex-X

        q : (Q : 𝟙 + X → Ω 𝓤) →  (Ǝₚ n ꞉ (Lift 𝓤 ℕ) , Q (f n)) ＝ (Ǝₚ x ꞉ (𝟙 + X) ,  Q x)
        q Q = ⇔-gives-＝ pe (Ǝₚ n ꞉ (Lift 𝓤 ℕ) , Q (f n)) (Ǝₚ x ꞉ (𝟙 + X) , Q x)
                    (holds-gives-equal-⊤ pe fe (Ǝₚ n ꞉ (Lift 𝓤 ℕ) , Q (f n) ⇔ Ǝₚ x ꞉ (𝟙 + X) , Q x) (p Q))

   extend : (X → Ω 𝓤) → (𝟙 {𝓤} + X) → Ω 𝓤
   extend _ (inl ⋆) = ⊥ {𝓤}
   extend P (inr x) = P x

   eq : (P : X → Ω 𝓤) → ( (Ǝₚ x' ꞉ (𝟙 + X) , (extend P) x') ⇔ Ǝₚ x ꞉ X , P x) holds
   eq P = (λ extended → ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , P x))
                                              (uncurry (λ x' → dep-cases {𝓤} {𝓤} {𝓤} {𝟙} {X} {λ z → extend P z holds → (Ǝₚ x ꞉ X , P x) holds}  (λ ⋆ es → 𝟘-elim es) (λ x ex → ∣ x , ex ∣) x'))
                                             extended ) ,
               λ base → ∥∥-rec (holds-is-prop (Ǝₚ x' ꞉ (𝟙 + X) , (extend P) x')) (λ (x , Px) → ∣ (inr x) , Px  ∣) base

   𝟘-iff : ((Ǝₚ z ꞉ (𝟘 {𝓤})  , ⊥ ) ⇔ ⊥ {𝓤}) holds 
   𝟘-iff = (λ hyp → ∥∥-rec (holds-is-prop (⊥ {𝓤})) (λ z → 𝟘-elim (pr₁ z)) hyp) , λ zero → 𝟘-elim zero

   † : (P : X → Ω 𝓤) → is-intrinsically-open P holds →  is-affirmable (Ǝₚ x ꞉ (𝟙 + X) , extend P x) holds
   † P open-P = lemma₁ (extend P) λ x' → dep-cases {𝓤} {𝓤} {𝓤 ⁺} {𝟙 {𝓤}} {X} { λ z → is-affirmable (extend P z) holds } (λ ⋆ → ⇔-affirmable 𝟘-iff (overt-𝟘 (λ _ → ⊥) (λ z → 𝟘-elim z))) (λ x → open-P x) x'
   
\end{code}

Sub-ness (subcompact, subovert ... )

\begin{code}

 is-subcompact : (Y : 𝓤 ̇) → (X : Y → Ω 𝓤) → 𝓤 ⁺ ̇   -- X ⊆ Y with Lesnik's notations of 2.15
 is-subcompact Y X = (U : Y → Ω 𝓤) → is-intrinsically-open U holds → (is-affirmable (Ɐ x ꞉ Y , (X x ⇒ U x))) holds

 is-subovert : (Y : 𝓤 ̇) → (X : Y → Ω 𝓤) → 𝓤 ⁺ ̇   -- same as above
 is-subovert Y X = (U : Y → Ω 𝓤) → is-intrinsically-open U holds → (is-affirmable (Ǝₚ x ꞉ Y , (X x ∧ U x))) holds


 subovert-of-discrete-is-open : {Y : 𝓤 ̇} → (X : Y → Ω 𝓤) → is-subovert Y X → (setY : is-set Y) →  (is-discrete-set Y setY) → is-intrinsically-open X holds
 subovert-of-discrete-is-open {Y} X subovert-X setY discrete-Y y = ⇔-affirmable X-iff †
  where
   X-iff : ((Ǝₚ y' ꞉ Y , (X y' ∧ ((y ＝ y') , setY))) ⇔ X y) holds
   X-iff = (λ exequal → ∥∥-rec (holds-is-prop (X y)) (λ (y' , Xy' , y-equals-y') → transport (λ i → pr₁ (X i)) (y-equals-y' ⁻¹)  Xy') exequal)  ,
               λ Xy → ∣ y , Xy , refl  ∣
   
   † : is-affirmable (Ǝₚ y' ꞉ Y , (X y' ∧ ((y ＝ y') , setY))) holds
   † = subovert-X (λ z → (y ＝ z) , setY) (λ z → discrete-Y (y , z) )

\end{code}

Density

\begin{code}

 is-dense : {X : 𝓤 ̇} → (D : X → Ω 𝓤) → 𝓤 ⁺ ̇  -- should be read : "D is dense in X"
 is-dense {X} D = (P : X → Ω 𝓤) → is-intrinsically-open P holds → (Ǝₚ x ꞉ X , P x) holds → (Ǝₚ x ꞉ X , ((P x) ∧ (D x))) holds

 self-is-dense-in-self : {X : 𝓤 ̇} → is-dense {X} (λ x → ⊤)
 self-is-dense-in-self  P open-P inhabited-P = ∥∥-rec (holds-is-prop (Ǝₚ x' ꞉ X , ((P x') ∧ (D x')))) † inhabited-P
   where
    X : 𝓤 ̇
    X = domain P
    
    D : X → Ω 𝓤
    D x = ⊤
    
    † : Σ x ꞉ X , P x holds → (Ǝₚ x' ꞉ X , ((P x') ∧ (D x'))) holds
    † (x , Px) = ∣ x , ∧-Intro (P x) (D x)  Px ⊤-holds  ∣


\end{code}

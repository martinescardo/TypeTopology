\begin{code}

{-# OPTIONS --safe --without-K --exact-split --auto-inline --lossy-unification #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import SyntheticTopology.SierpinskiObject 

module SyntheticTopology.SubProperties
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Sierpinski-Object 𝓤 fe pe pt)
        where

open import SyntheticTopology.Compactness 𝓤 fe pe pt 𝕊
open import SyntheticTopology.Discreteness 𝓤 fe pe pt 𝕊
open import SyntheticTopology.Dominance 𝓤 fe pe pt 𝕊
open import SyntheticTopology.Overtness 𝓤 fe pe pt 𝕊
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations 𝓤 fe pe pt 𝕊

\end{code}


Sub-ness (subcompact, subovert ... )

In our settings, how can we define a proper notion of maps of subobjects ?
For example see "image-of-subovert". We want, given (X Y : 𝓤 ̇)  ;  (f : X → Y)  and A ⊆ X represented by (A : X → Ω 𝓤),
a definition of "f (A)". The choice made in image-of-subovert was to define f (A) : Y → Ω 𝓤 with f (A) = λ y → Ǝₚ x ꞉ X , (A x ∧ (f x ＝ y))

Maybe other choices are possible.

We should try to come up with a generic definition of "image-of" in order to wrap it up and avoid defining things in proofs explicitely

\begin{code}

is-subcompact : ((Y , sY) : hSet 𝓤) → (X : Y → Ω 𝓤) → Ω (𝓤 ⁺)   -- X ⊆ Y with Lesnik's notations of 2.15
is-subcompact (Y , sY) X = (Ɐ (U , open-U) ꞉ 𝓞 (Y , sY) , is-affirmable (Ɐ x ꞉ Y , (X x ⇒ U x)))

is-subovert : ((Y , sY) : hSet 𝓤) → (X : Y → Ω 𝓤) → Ω (𝓤 ⁺)  -- same as above
is-subovert (Y , sY) X = (Ɐ (U , open-U) ꞉ 𝓞 (Y , sY) , is-affirmable (Ǝₚ x ꞉ Y , (X x ∧ U x)))


subovert-of-discrete-is-open : {(Y , sY) : hSet 𝓤} → (X : Y → Ω 𝓤) → is-subovert (Y , sY) X holds → (is-discrete (Y , sY) holds) → is-intrinsically-open {Y , sY} X holds
subovert-of-discrete-is-open {Y , sY} X subovert-X discrete-Y y = ⇔-affirmable X-iff †
  where
   X-iff : (Ǝₚ y' ꞉ Y , ((X y' ∧ (y ＝ y') , sY)) ⇔ X y) holds
   X-iff = (λ exequal → ∥∥-rec (holds-is-prop (X y)) (λ (y' , Xy' , y-equals-y') → transport (λ i → pr₁ (X i)) (y-equals-y' ⁻¹)  Xy') exequal)  ,
               λ Xy → ∣ y , Xy , refl  ∣

   † : is-affirmable (Ǝₚ y' ꞉ Y , (X y' ∧ ((y ＝ y') , sY))) holds
   † = subovert-X ((λ z → (y ＝ z) , sY) , (λ z → discrete-Y (y , z)))



subovert-inter-open-subovert : closed-under-binary-meets holds
                                                            → {(X , sX) : hSet 𝓤}
                                                            → (Ɐ A ꞉ (X → Ω 𝓤) , Ɐ (U , _) ꞉ 𝓞 (X , sX) , is-subovert (X , sX) A ⇒ is-subovert (X , sX) (λ x → (A x ∧ U x))) holds
subovert-inter-open-subovert cl-∧ {X , sX} A (U , open-U) subovert-A (V , open-V) = ⇔-affirmable inter-iff †
   where
    P : X → Ω 𝓤   -- P = U ∧ V
    P x = U x ∧ V x

    inter-iff : (Ǝₚ x ꞉ X , (A x ∧ (U x ∧ V x)) ⇔ (Ǝₚ x ꞉ X , ((A x ∧ U x) ∧ V x))) holds
    inter-iff = (λ right → ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , ((A x ∧ U x) ∧ V x))) (λ (x , Ax , Ux , Vx) → ∣ x , (Ax , Ux) , Vx ∣) right) ,
                      λ left → ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , (A x ∧ (U x ∧ V x)))) (λ (x , (Ax , Ux) , Vx) → ∣ x , Ax , Ux , Vx  ∣) left
    
    † : is-affirmable (Ǝₚ x ꞉ X , (A x ∧ (U x ∧ V x))) holds
    † = subovert-A (P , (λ x → cl-∧ (U x) (V x) ( open-U x , open-V x )))


open-subset-overt-is-overt : closed-under-binary-meets holds →
                                                       {(X , sX) : hSet 𝓤} → (Ɐ (U , _) ꞉ 𝓞 (X , sX) , is-overt (X , sX) ⇒ is-subovert (X , sX) U) holds
open-subset-overt-is-overt cl-∧ {X , sX} (U , open-U) overt-X (V , open-V) = overt-X ((λ x → (U x ∧ V x)) , (λ x → cl-∧ (U x) (V x) ((open-U x , open-V x))))


image-of-subovert : {(X , sX) (Y , sY) : hSet 𝓤 } → (f : X → Y) → (Ɐ A ꞉ (X → Ω 𝓤) , is-subovert (X , sX) A ⇒ is-subovert (Y , sY) (λ y → (Ǝₚ x ꞉ X , (A x ∧ ((f x) ＝ y) , sY)))) holds 
image-of-subovert {X , sX} {Y , sY} f  A subovert-A (P , open-P)  = ⇔-affirmable Y-iff †
  where
   Y-iff : (Ǝₚ x' ꞉ X , (A x' ∧ P (f x')) ⇔ (Ǝₚ y ꞉ Y , (Ǝₚ x ꞉ X , (A x ∧ (f x ＝ y) , sY) ∧ P y))) holds
   Y-iff = (λ x'-hyp → ∥∥-rec (holds-is-prop (Ǝₚ y ꞉ Y , (Ǝₚ x ꞉ X , (A x ∧ (f x ＝ y) , sY) ∧ P y))) (λ (x' , Ax' , Pfx') → ∣ f x' , ∣ x' , Ax' , refl ∣ , Pfx' ∣) x'-hyp ) ,
               λ y-hyp → ∥∥-rec (holds-is-prop (Ǝₚ x' ꞉ X , (A x' ∧ P (f x')))) (λ (y , x-existence , Py)
                                 → ∥∥-rec (holds-is-prop (Ǝₚ x' ꞉ X , (A x' ∧ P (f x')))) (λ (x , Ax , fx-equal-y) → ∣ x , Ax , (transport (_holds ∘ P) (fx-equal-y ⁻¹) Py) ∣) x-existence) y-hyp
   
   † : is-affirmable (Ǝₚ x' ꞉ X , (A x' ∧ P (f x'))) holds
   † = subovert-A ((P ∘ f) , ( λ x → open-P (f x)))

\end{code}


We have some lemmas that states the consistency of "sub" definitions related to "plain" ones.

\begin{code}

compact-iff-subcompact-in-self : {(X , sX) : hSet 𝓤}
                                               → ((is-compact (X , sX)) ⇔(is-subcompact (X , sX) (λ x → ⊤))) holds

compact-iff-subcompact-in-self {(X , sX)} = (λ compact-X (U , open-U) → ⇔-affirmable (p (U , open-U)) (compact-X (U , open-U))) ,
    λ subcompact-X (U , open-U) → ⇔-affirmable (⇔-swap pe (Ɐ x ꞉ X , U x) (Ɐ x ꞉ X , ⊤ ⇒ U x) (p (U , open-U)))  (subcompact-X (U , open-U))
  where
   p : ((U , open-U) : 𝓞 (X , sX)) → ((Ɐ x ꞉ X , U x) ⇔ (Ɐ x ꞉ X , ⊤ ⇒ U x)) holds
   p (U , open-U) = (λ Ux x top → Ux x) , λ top-imp-Ux x → top-imp-Ux x ⊤-holds

overt-iff-subovert-in-self : {(X , sX) : hSet 𝓤}
                                               → ((is-overt (X , sX)) ⇔(is-subovert (X , sX) (λ x → ⊤))) holds

overt-iff-subovert-in-self {(X , sX)} = (λ overt-X (U , open-U) → ⇔-affirmable (p (U , open-U)) (overt-X (U , open-U))) ,
    λ subovert-X (U , open-U) → ⇔-affirmable (⇔-swap pe (Ǝₚ x ꞉ X , U x) (Ǝₚ x ꞉ X , (⊤ ∧ U x)) (p (U , open-U)))  (subovert-X (U , open-U))
  where
   p : ((U , open-U) : 𝓞 (X , sX)) → ((Ǝₚ x ꞉ X , U x) ⇔ (Ǝₚ x ꞉ X , (⊤ ∧ U x))) holds
   p (U , open-U) = (λ ex-x → ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , (⊤ ∧ U x))) (λ (x , Ux) → ∣ x , ⊤-holds , Ux  ∣) ex-x) ,
                                 λ ex-x-top → ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , U x)) (λ (x , top-and-Ux) → ∣ x , ∧-Elim-R ⊤ (U x) top-and-Ux ∣) ex-x-top

\end{code}

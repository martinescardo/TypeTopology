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

module SyntheticTopology.Overtness
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Sierpinski-Object 𝓤 fe pe pt)
        where

open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations 𝓤 fe pe pt 𝕊


\end{code}


Overtness:

\begin{code}

is-overt : hSet 𝓤  → Ω (𝓤 ⁺)
is-overt (X , sX) =
  Ɐ (P , open-P) ꞉ 𝓞 (X , sX) ,  is-affirmable (Ǝₚ x ꞉ X , P x)


image-of-overt :  {(X , sX) (Y , sY) : hSet 𝓤}
                   → (f : X → Y)
                   → is-surjection f
                   → is-overt (X , sX) holds
                   → is-overt (Y , sY) holds
image-of-overt {X , sX} {Y , sY} f surf overt-X (P , open-P) = ⇔-affirmable p †
  where
   p : ((Ǝₚ x ꞉ X , P (f x)) ⇔ (Ǝₚ y ꞉ Y , P y)) holds
   p = (λ pX → ∥∥-rec (holds-is-prop (Ǝₚ y ꞉ Y , P y)) (λ (x , Pxf) → ∣ f x , Pxf  ∣) pX) ,
          λ pY → ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , P (f x)))
                        (λ (y , Py) → ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , P (f x))) (λ (x , x-eq-fy) → ∣ x ,  transport (λ y' → P y' holds) (x-eq-fy ⁻¹) Py ∣) (exists-preimage-of-y y) ) pY

    where
     exists-preimage-of-y : (y : Y) → ((Ǝₚ x ꞉ X , ((f x ＝ y) , sY)) holds)
     exists-preimage-of-y y =
        surjection-induction f surf (λ y → ((Ǝₚ x ꞉ X , ((f x ＝ y) , sY)) holds)) (λ y → holds-is-prop _) (λ x → ∣ x , refl  ∣) y
   
   † : is-affirmable (Ǝₚ x ꞉ X , P (f x)) holds
   † = overt-X ((P ∘ f) , (open-P ∘ f))
{-
 countable-are-overt : (is-overt (Lift 𝓤 ℕ) holds) → (is-overt (𝟘 {𝓤}) holds) → (X : 𝓤 ̇) → (f : ( (Lift 𝓤 ℕ) → (𝟙 {𝓤} ) + X)) → (is-surjection f) → (is-overt X holds)
 countable-are-overt overt-ℕ overt-𝟘 X f surf = λ P open-P → ⇔-affirmable (eq P) († P open-P) -- GENERALIZE INTO IMAGE OF OVERT ARE OVERT AND ℕ IS OVERT

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
-}
\end{code}

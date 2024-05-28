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

module SyntheticTopology.Density
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
open import SyntheticTopology.SubProperties 𝓤 fe pe pt 𝕊
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations 𝓤 fe pe pt 𝕊

\end{code}


Density

A subset D of a set X is dense if D intersects every inhabited open subset of X

\begin{code}

is-dense : {(X , sX) : hSet 𝓤} → (D : X → Ω 𝓤) → Ω (𝓤 ⁺)  -- should be read : "D is dense in X"
is-dense {X , sX} D = (Ɐ (P , open-P) ꞉ 𝓞 (X , sX) , (Ǝₚ x ꞉ X , P x) ⇒ (Ǝₚ x ꞉ X , ((D x) ∧ (P x))))

self-is-dense-in-self : {(X , sX) : hSet 𝓤} → is-dense {X , sX} (λ x → ⊤) holds
self-is-dense-in-self  (P , open-P) inhabited-P = ∥∥-rec (holds-is-prop (Ǝₚ x' ꞉ X , ((D x') ∧ (P x')))) † inhabited-P
   where
    X : 𝓤 ̇
    X = domain P

    D : X → Ω 𝓤
    D x = ⊤

    † : Σ x ꞉ X , P x holds → (Ǝₚ x' ꞉ X , ((D x') ∧ (P x'))) holds
    † (x , Px) = ∣ x , ∧-Intro (D x) (P x) ⊤-holds Px  ∣


subovert-dense-overt : ((X , sX) : hSet 𝓤) → (U : X → Ω 𝓤) → is-subovert (X , sX) U holds → is-dense {X , sX} U holds → is-overt (X , sX) holds
subovert-dense-overt (X , sX) U subovert-U dense-U (P , open-P) = ⇔-affirmable U-iff †
  where
   U-iff : ((Ǝₚ x ꞉ X , (U x ∧ P x)) ⇔ (Ǝₚ x ꞉ X , P x)) holds
   U-iff = (λ U-hyp → ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , P x)) (λ (x-both , px-both) → ∣ x-both , pr₂ px-both ∣) U-hyp) ,
               λ P-hyp → ∥∥-rec (holds-is-prop (Ǝₚ x ꞉ X , (U x ∧ P x))) (λ (x-only , px-only) →  dense-U (P , open-P) ∣ x-only ,  px-only ∣) P-hyp

   † : is-affirmable (Ǝₚ x ꞉ X , (U x ∧ P x)) holds
   † = subovert-U (P , open-P)


\end{code}

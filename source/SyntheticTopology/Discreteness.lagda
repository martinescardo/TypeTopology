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

module SyntheticTopology.Discreteness
        (𝓤  : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Sierpinski-Object 𝓤 fe pe pt)
        where

open import SyntheticTopology.Compactness 𝓤 fe pe pt 𝕊
open import SyntheticTopology.Dominance 𝓤 fe pe pt 𝕊
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations 𝓤 fe pe pt 𝕊

\end{code}


Discrete spaces.

Being discrete means having affirmable equality

\begin{code}

is-discrete : ((X , sX) : hSet 𝓤) → Ω (𝓤 ⁺)
is-discrete (X , sX) = is-intrinsically-open {(X × X) , (×-is-set sX sX)} (λ ((x , y) : X × X) → ((x ＝ y) , sX))


\end{code}

We prove here that 𝟙 is discrete as long as the true truth value lies in the
Sierpinski object's image.

\begin{code}

𝟙-is-discrete : contains-top holds → (𝟙-is-set : is-set 𝟙) → is-discrete (𝟙 , 𝟙-is-set) holds
𝟙-is-discrete ct 𝟙-is-set (⋆ , ⋆) = ⇔-affirmable † ct
  where
   † : (⊤ ⇔ (⋆ ＝ ⋆) , 𝟙-is-set) holds
   † = (λ _ → refl) , (λ _ → ⊤-holds)

\end{code}

Compact indexed product of discrete set is itself discrete (requires functionnal extensionality)

\begin{code}

compact-Π-discrete : ((K , sK) : hSet 𝓤) → (X : K → hSet 𝓤)
                        → is-compact (K , sK) holds
                        → ((k : K) → is-discrete (X k) holds)
                        → is-discrete (Π (λ k → (underlying-set (X k))) , (Π-is-set fe (λ k → (pr₂ (X k))))) holds
compact-Π-discrete (K , sK) X kK dX (x₁ , x₂) = ⇔-affirmable p †
  where
   p :  ((k : K) →  ( (x₁ k) ＝ (x₂ k) ) ) ↔ (x₁ ＝ x₂)
   p = dfunext fe
      , (λ x₁-equal-x₂ → transport (λ - → ((k : K) → (( x₁ k ) ＝( - k) ))) x₁-equal-x₂ (λ _ → refl))
   -- there is certainly some magic function in funext's family doing the job but I have not found it

   † : is-affirmable (Ɐ k ꞉ K , ((x₁ k ＝ x₂ k) , pr₂ (X k))) holds
   † = kK ((λ k → (x₁ k ＝ x₂ k) , pr₂ (X k)) , (λ k → dX k (x₁ k , x₂ k)))

\end{code}

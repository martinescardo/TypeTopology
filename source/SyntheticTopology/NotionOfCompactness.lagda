---
title:                  Investigation of compactness with 𝟚 as the Sierpinski object
author:             Martin Trucchi
date-started:  2024-05-30
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import NotionsOfDecidability.Decidable
open import MLTT.Spartan
open import TypeTopology.CompactTypes hiding (is-compact)
open import UF.Base
open import UF.FunExt
open import UF.Logic
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import  UF.Subsingletons-FunExt
open import UF.SubtypeClassifier

module SyntheticTopology.NotionOfCompactness
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        where


open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open import SyntheticTopology.SierpinskiObject fe pe pt
open import TypeTopology.WeaklyCompactTypes (λ 𝓥 𝓦 → fe {𝓥} {𝓦}) pt


\end{code}


We first define the 𝟚 Sierpinski object. That is, a proposition P is affirmable if
P ∨ (¬ P) holds. 

\begin{code}

𝟚-sierpinski : Generalized-Sierpinski-Object 𝓤₀ 𝓤₀
𝟚-sierpinski P = P ∨ (¬ₚ P)


open import SyntheticTopology.Compactness 𝓤₀ 𝓤₀ fe pe pt 𝟚-sierpinski
open import SyntheticTopology.Overtness 𝓤₀ 𝓤₀ fe pe pt 𝟚-sierpinski
open import SyntheticTopology.SierpinskiAxioms 𝓤₀ 𝓤₀ fe pe pt 𝟚-sierpinski
open Sierpinski-notations 𝟚-sierpinski

\end{code}

We prove that this Sierpinski object is a dominance.
The proof of transitive-openness seems long but it is just saying that

If u is decidable, and u → "p is decidable", then "u and p" is decidable :

 - either u is false, so "u and p" is also false thus decidable
 - either u is true, but now p is decidable so
          - either p is true, so "u and p" is true thus decidable
          - either p is false, so "u and p" is false thus decidable

\begin{code}

𝟚-is-dominance : is-synthetic-dominance
𝟚-is-dominance = ⊤-is-decidable ,  𝟚-has-transitive-openness
 where
  ⊤-is-decidable : (⊤ ∨ (¬ₚ ⊤)) holds
  ⊤-is-decidable = ∣ inl ⊤-holds ∣

  𝟚-has-transitive-openness : openness-is-transitive 
  𝟚-has-transitive-openness u affirmable-u p u-gives-affirmable-p =
   ∥∥-rec (holds-is-prop affirmable-and) † affirmable-u
    where
     affirmable-and : Ω 𝓤₀
     affirmable-and = is-affirmable (u ∧ p)

     u-and-p-gives-affirmable-and : u holds
                                                         → p holds
                                                         → affirmable-and holds
                                                         
     u-and-p-gives-affirmable-and u-holds p-holds =
      ∣ inl (u-holds , p-holds) ∣
      
     
     u-and-not-p-gives-affirmable-and : u holds
                                                                → (¬ₚ p) holds
                                                                → affirmable-and holds
                                                                
     u-and-not-p-gives-affirmable-and u-holds not-p-holds =
      ∣ inr (λ u-and-p → not-p-holds (pr₂ u-and-p) ) ∣


     dec-p-gives-affirmable-and : u holds
                                                    → (p holds) + ((¬ₚ p) holds)
                                                    → affirmable-and holds
                                                    
     dec-p-gives-affirmable-and u-holds dec-p =
      cases (u-and-p-gives-affirmable-and u-holds)
                 (u-and-not-p-gives-affirmable-and u-holds)
                 dec-p


     u-gives-affirmable-and : u holds
                                             → affirmable-and holds
     
     u-gives-affirmable-and u-holds =
      ∥∥-rec (holds-is-prop affirmable-and)
                 (dec-p-gives-affirmable-and u-holds)
                 (u-gives-affirmable-p u-holds)
     
     not-u-gives-affirmable-and : (¬ₚ u) holds
                                                      → affirmable-and holds
                                                      
     not-u-gives-affirmable-and not-u-holds =
      ∣ inr (λ u-and-p → not-u-holds (pr₁ u-and-p)) ∣
     
     † : (u holds) + ((¬ₚ u) holds)
          → affirmable-and holds
     † dec-u = cases u-gives-affirmable-and not-u-gives-affirmable-and dec-u
    

\end{code}


Now that we know that 𝟚-sierpinski is a dominance, we investigate the notion of
compactness it defines and relate it to the one that are defined in
TypeTopology.CompactTypes

To distinguish the ambigous names "is-compact", we explicitely define an alias here.


\begin{code}

is-synthetically-compact : hSet 𝓤₀ → Ω (𝓤₁)
is-synthetically-compact = is-compact

\end{code}


\begin{code}

¬-prop : (A : 𝓤 ̇) → is-prop A → is-prop (¬ A)
¬-prop A prop-A = Π-is-prop fe λ _ → 𝟘-is-prop

gneu : 𝓤₀ ̇
gneu = is-set 𝟚

synthetically-overt-gives-∃-compact : ((X , sX) : hSet 𝓤₀) → gneu →  is-overt (X , sX) holds → is-∃-compact X 
synthetically-overt-gives-∃-compact (X , sX) g overt-X P =
 ∥∥-rec (+-is-prop ∃-is-prop (¬-prop (∃ (λ x → P x ＝ ₀)) ∃-is-prop) ¬¬-intro) id (overt-X (P-propified , †))
 where
  P-propified : X → Ω 𝓤₀
  P-propified x = ((P x) ＝ ₀) , g

  t : 𝟚 → 𝓤₀ ̇
  t ₀ = 𝟙
  t ₁ = 𝟘
  
  † : is-intrinsically-open (X , sX) P-propified holds
  † = λ x → 𝟚-induction {𝓤₀} { λ p → is-affirmable ((p ＝ ₀) , g) holds } ∣ inl refl  ∣ ∣ inr (λ absurd → 𝟘-is-not-𝟙 (ap t absurd)) ∣ (P x)
  
\end{code}


\begin{code}

₀-is-not-₁ : ₀ ≠ ₁
₀-is-not-₁ pr = 𝟘-elim (𝟘-is-not-𝟙 (ap c pr))
 where
  c : 𝟚 → 𝓤₀ ̇
  c ₁ = 𝟙
  c ₀ = 𝟘

lemma-absurd : (P : Ω 𝓤₀) → P holds → (¬ₚ P) holds → 𝟘 {𝓤₀}
lemma-absurd P P-holds neg-P-holds = neg-P-holds P-holds

choice : 𝓤₁ ̇
choice = (X : 𝓤₀ ̇) → (A : X → 𝓤₀ ̇ ) →  ((x : X) → ∥  A x  ∥ ) → ( ∥ ( (x : X) → A x ) ∥ ) 

test : (((X , sX) : hSet 𝓤₀) → is-∃-compact X → choice → is-overt (X , sX) holds) 
test (X , sX) ∃-compact-X choice-X (P , dec-P) =
 ∥∥-rec (holds-is-prop (is-affirmable (Ǝₚ x ꞉ X , P x))) † (choice-X X (λ z → (P z holds) + ((¬ₚ P z) holds)) dec-P)
 where
  
  † : ((x : X) → (P x holds) + ((¬ₚ P x) holds)) → is-affirmable (Ǝₚ x ꞉ X , (P x)) holds
  † oracle = lemmi (∃-compact-X p)
   where
    p : X → 𝟚
    p = pr₁ (indicator oracle)

    p-proof : (x : X) → (p x ＝ ₀ → P x holds) × (p x ＝ ₁ → (¬ₚ P x) holds)
    p-proof = pr₂ (indicator oracle)
    
    dec-p : (x : X) → (p x ＝ ₀) + (p x ＝ ₁)
    dec-p x = 𝟚-induction { 𝓤₀ } { λ z → (z ＝ ₀) + (z ＝ ₁) } (inl refl) (inr refl) (p x)
    
    lemmi : Exists X (λ x → pr₁ (indicator oracle) x ＝ ₀) + ¬ Exists X (λ x → pr₁ (indicator oracle) x ＝ ₀) → is-affirmable (Ǝₚ x ꞉ X , (P x)) holds
    lemmi oui = cases (λ rah → ∥∥-rec (holds-is-prop (is-affirmable (Ǝₚ x ꞉ X , (P x)))) (λ (x , px) → ∣ inl ∣ x , pr₁ (p-proof x) px  ∣  ∣)  rah)
                                     (λ notrah → ∣ inr (λ found-a-bad-x → ∥∥-rec (holds-is-prop (𝟘 , 𝟘-is-prop))
                                                        (λ (x , Px) → notrah ∣ x , cases id (λ px₁ → 𝟘-elim (lemma-absurd (P x) Px ((pr₂ (p-proof x)) px₁)) ) (dec-p x) ∣) found-a-bad-x)  ∣) oui 
  
\end{code}

---
title:        Subobjects in Synthetic Topology
author:       Martin Trucchi
date-started: 2024-05-28
---

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.Sets-Properties
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import SyntheticTopology.SierpinskiObject

module SyntheticTopology.SubObjects
        (𝓤 𝓥 : Universe)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
        (𝕊 : Generalized-Sierpinski-Object fe pe pt 𝓤 𝓥)
        where

open import SyntheticTopology.Compactness 𝓤 𝓥 fe pe pt 𝕊
open import SyntheticTopology.Discreteness 𝓤 𝓥 fe pe pt 𝕊
open import SyntheticTopology.Overtness 𝓤 𝓥 fe pe pt 𝕊
open import SyntheticTopology.SierpinskiAxioms 𝓤 𝓥 fe pe pt 𝕊
open import UF.ImageAndSurjection pt
open import UF.Logic

open AllCombinators pt fe
open PropositionalTruncation pt hiding (_∨_)
open Sierpinski-notations fe pe pt 𝕊

\end{code}


Investigating notions on subobjects? (subcompact, subovert ... )

In our settings, how can we define a proper notion of maps of subobjects ?
For example see "image-of-subset". We want, given (X Y : 𝓤 ̇)  ;  (f : X → Y)
and A ⊆ X represented by (A : X → Ω 𝓤), a definition of "f (A)".

The choice made in image-of-subset was to define
f (A) : Y → Ω 𝓤 with f (A) = λ y → Ǝₚ x ꞉ X , (A x ∧ (f x ＝ y))

Maybe other choices are possible.

\begin{code}

image-of-subset : ((X , sX) (Y , sY) : hSet 𝓤)
                → (f : X → Y)
                → (A : X → Ω 𝓤)
                → (Y → Ω 𝓤)
                
image-of-subset (X , sX) (Y , sY) f A =
 λ y → Ǝₚ x ꞉ X , (A x ∧ (f x ＝ y) , sY)

is-subcompact : ((Y , sY) : hSet 𝓤)
              → (X : Y → Ω 𝓤)
              → Ω ((𝓤 ⁺) ⊔ 𝓥)
              
is-subcompact (Y , sY) X =
 Ɐ (U , open-U) ꞉ 𝓞 (Y , sY) , is-open-proposition (Ɐ x ꞉ Y , (X x ⇒ U x))

is-subovert : ((Y , sY) : hSet 𝓤)
            → (X : Y → Ω 𝓤)
            → Ω ((𝓤 ⁺) ⊔ 𝓥)
is-subovert (Y , sY) X =
 (Ɐ (U , open-U) ꞉ 𝓞 (Y , sY) , is-open-proposition (Ǝₚ x ꞉ Y , (X x ∧ U x)))


subovert-of-discrete-is-open : ((Y , sY) : hSet 𝓤)
                             → (X : Y → Ω 𝓤)
                             → is-subovert (Y , sY) X holds
                             → (is-discrete (Y , sY) holds)
                             → is-intrinsically-open (Y , sY) X holds
                             
subovert-of-discrete-is-open (Y , sY) X subovert-X discrete-Y y =
 ⇔-open (Ǝₚ y' ꞉ Y , ((X y' ∧ (y ＝ y') , sY))) (X y) (p₁ , p₂) †
  where
   p₁ : (Ǝₚ y' ꞉ Y , ((X y' ∧ (y ＝ y') , sY)) ⇒ X y) holds
   p₁ = λ ex-equal → ∥∥-rec (holds-is-prop (X y))
                            (λ (y' , Xy' , y-equals-y')
                                → transport (λ i → pr₁ (X i))
                                            (y-equals-y' ⁻¹)
                                            Xy')
                            ex-equal

   p₂ : (X y ⇒ (Ǝₚ y' ꞉ Y , ((X y' ∧ (y ＝ y') , sY)))) holds
   p₂ = λ Xy → ∣ y , Xy , refl  ∣

   † : is-open-proposition (Ǝₚ y' ꞉ Y , (X y' ∧ ((y ＝ y') , sY))) holds
   † = subovert-X ((λ z → (y ＝ z) , sY) , (λ z → discrete-Y (y , z)))


subovert-inter-open-subovert : closed-under-binary-meets holds
                             → ((X , sX) : hSet 𝓤)
                             → (Ɐ A ꞉ (X → Ω 𝓤) ,
                                 Ɐ (U , _) ꞉ 𝓞 (X , sX) ,
                                  is-subovert (X , sX) A
                                   ⇒ is-subovert (X , sX) (λ x → (A x ∧ U x)))
                                      holds
                                      
subovert-inter-open-subovert cl-∧
                             (X , sX) A (U , open-U) subovert-A (V , open-V) =
 ⇔-open right-par left-par (p₁ , p₂) †
  where
   left-par : Ω 𝓤
   left-par = Ǝₚ x ꞉ X , ((A x ∧ U x) ∧ V x)
   
   right-par : Ω 𝓤
   right-par = Ǝₚ x ꞉ X , (A x ∧ (U x ∧ V x)) 

   P : X → Ω 𝓤   -- P = U ∧ V
   P x = U x ∧ V x

   p₁ : (right-par ⇒ left-par) holds
   p₁ = λ right → ∥∥-rec
                              (holds-is-prop left-par)
                              (λ (x , (Ax , Ux , Vx)) → ∣ x , (Ax , Ux) , Vx ∣)
                              right

   p₂ : (left-par ⇒ right-par) holds
   p₂ = λ left → ∥∥-rec
                            (holds-is-prop right-par)
                            (λ (x , ((Ax , Ux) , Vx)) → ∣ x , Ax , Ux , Vx ∣)
                            left
   
   † : is-open-proposition right-par holds
   † = subovert-A ((λ x → U x ∧ V x) ,
                    λ x → cl-∧ (U x) (V x) ((open-U x) , (open-V x)))


open-subset-of-overt-is-subovert : closed-under-binary-meets holds
                                 → ((X , sX) : hSet 𝓤)
                                 → (Ɐ (U , _) ꞉ 𝓞 (X , sX) ,
                                    is-overt (X , sX)
                                     ⇒ is-subovert (X , sX) U) holds
                                                                        
open-subset-of-overt-is-subovert cl-∧
                                 (X , sX) (U , open-U) overt-X (V , open-V) =
 overt-X ((λ x → (U x ∧ V x)) ,
         (λ x → cl-∧ (U x) (V x) ((open-U x , open-V x))))


image-of-subovert : ((X , sX) (Y , sY) : hSet 𝓤)
                  → (f : X → Y)
                  → (Ɐ A ꞉ (X → Ω 𝓤) ,
                     is-subovert (X , sX) A
                      ⇒ is-subovert (Y , sY)
                                    (image-of-subset (X , sX) (Y , sY) f A))
                                     holds
                                     
image-of-subovert (X , sX) (Y , sY) f  A subovert-A (P , open-P)  =
 ⇔-open x'-exists y-exists (p₁ , p₂) †
  where
  
   x'-exists : Ω 𝓤
   x'-exists = Ǝₚ x' ꞉ X , (A x' ∧ P (f x'))
   
   y-exists : Ω 𝓤
   y-exists = Ǝₚ y ꞉ Y , (Ǝₚ x ꞉ X , (A x ∧ (f x ＝ y) , sY) ∧ P y)
   
   p₁ : (x'-exists ⇒ y-exists) holds
   p₁ = λ x'-hyp → ∥∥-rec (holds-is-prop y-exists)
                          (λ (x' , Ax' , Pfx') →
                           ∣ f x' , ∣ x' , Ax' , refl ∣ , Pfx' ∣)
                          x'-hyp
   
   p₂ : (y-exists ⇒ x'-exists) holds
   p₂ = λ y-hyp → ∥∥-rec (holds-is-prop x'-exists)
                         x-exists-gives-x' 
                         y-hyp

    where
     x-exists-gives-x' :
       (Σ y ꞉ Y , (Ǝₚ x ꞉ X , (A x ∧ (f x ＝ y) , sY) ∧ P y) holds)
      → x'-exists holds
      
     x-exists-gives-x' (y , x-exists , Py) = ∥∥-rec (holds-is-prop x'-exists)
                                                    (λ (x , Ax , fx-eq-y) →
                                                     ∣ x , Ax ,
                                                      (transport (_holds ∘ P)
                                                                 (fx-eq-y ⁻¹)
                                                                 Py)
                                                     ∣)
                                                    x-exists
   
   † : is-open-proposition x'-exists holds
   † = subovert-A ((P ∘ f) , ( λ x → open-P (f x)))

\end{code}


We have some lemmas that states the consistency of "sub" definitions
related to "plain" ones.

\begin{code}

compact-iff-subcompact-in-self : ((X , sX) : hSet 𝓤)
                               → ((is-compact (X , sX)) ⇔
                                   (is-subcompact (X , sX) (λ x → ⊤))) holds

compact-iff-subcompact-in-self (X , sX) =
 compact-gives-subcompact , subcompact-gives-compact
  where
  
   p₁ : ((U , open-U) : 𝓞 (X , sX))
      → ((Ɐ x ꞉ X , U x) ⇒ (Ɐ x ꞉ X , ⊤ ⇒ U x)) holds
      
   p₁ (U , open-U) = (λ Ux x top → Ux x)
   
   p₂ : ((U , open-U) : 𝓞 (X , sX))
      → ((Ɐ x ꞉ X , ⊤ ⇒ U x) ⇒ (Ɐ x ꞉ X , U x)) holds
      
   p₂ (U , open-U) = λ top-imp-Ux x → top-imp-Ux x ⊤-holds
  
   compact-gives-subcompact :
    ( is-compact (X , sX) ⇒ is-subcompact (X , sX) (λ x → ⊤) ) holds
    
   compact-gives-subcompact = λ compact-X (U , open-U) →
    ⇔-open (Ɐ x ꞉ X , U x)
                 (Ɐ x ꞉ X , ⊤ ⇒ U x)
                 (p₁ (U , open-U) , p₂ (U , open-U))
                 (compact-X (U , open-U))

   subcompact-gives-compact :
    ( is-subcompact (X , sX) (λ x → ⊤)  ⇒ is-compact (X , sX) ) holds
    
   subcompact-gives-compact = λ subcompact-X (U , open-U) →
    ⇔-open (Ɐ x ꞉ X , ⊤ ⇒ U x)
                 (Ɐ x ꞉ X , U x)
                 (p₂ (U , open-U) , p₁ (U , open-U))
                 (subcompact-X (U , open-U))



overt-iff-subovert-in-self : ((X , sX) : hSet 𝓤)
                           → ((is-overt (X , sX)) ⇔
                              (is-subovert (X , sX) (λ x → ⊤))) holds

overt-iff-subovert-in-self (X , sX) =
 overt-gives-subovert , subovert-gives-overt

 where
  x-exists : ((U , open-U) : 𝓞 (X , sX)) → Ω 𝓤
  x-exists (U , open-U) = Ǝₚ x ꞉ X , U x
  
  x-⊤-exists : ((U , open-U) : 𝓞 (X , sX)) → Ω 𝓤
  x-⊤-exists (U , open-U) = Ǝₚ x ꞉ X , (⊤ ∧ (U x))
  
  p₁ : ((U , open-U) : 𝓞 (X , sX))
     → (x-exists (U , open-U) ⇒ x-⊤-exists (U , open-U)) holds

  p₁ (U , open-U) = λ ex-x → ∥∥-rec (holds-is-prop (x-⊤-exists (U , open-U)))
                                    (λ (x , Ux) → ∣ x , ⊤-holds , Ux  ∣)
                                    ex-x

  p₂ : ((U , open-U) : 𝓞 (X , sX))
     → (x-⊤-exists (U , open-U) ⇒ x-exists (U , open-U)) holds

  p₂ (U , open-U) = λ ex-x-⊤ → ∥∥-rec (holds-is-prop (x-exists (U , open-U)))
                                      (λ (x , ⊤-Ux) →
                                       ∣ x , ∧-Elim-R ⊤ (U x) ⊤-Ux ∣)
                                      ex-x-⊤

  overt-gives-subovert
   : (is-overt (X , sX) ⇒ (is-subovert (X , sX) (λ x → ⊤))) holds
                         
  overt-gives-subovert = (λ overt-X (U , open-U) →
   ⇔-open (x-exists (U , open-U))
          (x-⊤-exists (U , open-U))
          (p₁ (U , open-U) , p₂ (U , open-U))
          (overt-X (U , open-U)))
  
  subovert-gives-overt
   : (is-subovert (X , sX) (λ x → ⊤) ⇒ (is-overt (X , sX))) holds
  
  subovert-gives-overt = λ subovert-X (U , open-U) →
   ⇔-open (x-⊤-exists (U , open-U))
          (x-exists (U , open-U))
          (p₂ (U , open-U) , p₁ (U , open-U))
          (subovert-X (U , open-U))

\end{code}

Ian Ray, 15th January 2025

Pushouts are defined as higher inductive type (in the form of a record type).
We postulate point and path constructors, an induction principle and
propositional computation rules for each constructor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.Pushouts (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Subsingletons
open import UF.Yoneda

\end{code}

We start by defining cocones and characerizing their identity type.

\begin{code}

cocone : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
         (f : C → A) (g : C → B) (X : 𝓣  ̇)
       → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣  ̇
cocone {𝓤} {𝓥} {𝓦} {𝓣} {A} {B} {C} f g X =
 Σ i ꞉ (A → X) , Σ j ꞉ (B → X) , (i ∘ f ∼ j ∘ g)

cocone-vertical-map : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
                      (f : C → A) (g : C → B) (X : 𝓣  ̇)
                    → cocone f g X
                    → (A → X)
cocone-vertical-map f g X (i , j , K) = i

cocone-horizontal-map : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
                        (f : C → A) (g : C → B) (X : 𝓣  ̇)
                      → cocone f g X
                      → (B → X)
cocone-horizontal-map f g X (i , j , K) = j

cocone-commuting-square : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
                          (f : C → A) (g : C → B) (X : 𝓣  ̇)
                        → ((i , j , K) : cocone f g X)
                        → i ∘ f ∼ j ∘ g
cocone-commuting-square f g X (i , j , K) = K

cocone-family : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
                (f : C → A) (g : C → B) (X : 𝓣  ̇)
              → cocone f g X → cocone f g X → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣  ̇
cocone-family f g X (i , j , H) (i' , j' , H') =
 Σ K ꞉ i ∼ i' , Σ L ꞉ j ∼ j' ,
  ∼-trans (K ∘ f) H' ∼ ∼-trans H (L ∘ g)

canonical-map-from-identity-to-cocone-family
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
   (f : C → A) (g : C → B) (X : 𝓣  ̇)
 → (u u' : cocone f g X)
 → u ＝ u'
 → cocone-family f g X u u'
canonical-map-from-identity-to-cocone-family
 f g X (i , j , H) .(i , j , H) refl =
 (∼-refl , ∼-refl , λ - → refl-left-neutral)

cocone-family-is-identity-system
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
   (f : C → A) (g : C → B) (X : 𝓣  ̇)
 → (x : cocone f g X)
 → is-contr (Σ y ꞉ cocone f g X , cocone-family f g X x y)
cocone-family-is-identity-system {_} {_} {_} {𝓣} {A} {B} {C} f g X (i , j , H) =
 equiv-to-singleton e 𝟙-is-singleton
 where
  e : (Σ y ꞉ cocone f g X , cocone-family f g X (i , j , H) y) ≃ 𝟙 { 𝓣 }
  e = (Σ y ꞉ cocone f g X , cocone-family f g X (i , j , H) y) ≃⟨ I ⟩
      (Σ i' ꞉ (A → X) , Σ j' ꞉ (B → X) ,
        Σ H' ꞉ (i' ∘ f ∼ j' ∘ g) ,
         Σ K ꞉ i ∼ i' , Σ L ꞉ j ∼ j' ,
          ∼-trans (K ∘ f) H' ∼ ∼-trans H (L ∘ g))              ≃⟨ II ⟩
      (Σ i' ꞉ (A → X) , Σ K ꞉ i ∼ i' ,
        Σ j' ꞉ (B → X) , Σ L ꞉ j ∼ j' ,
         Σ H' ꞉ (i' ∘ f ∼ j' ∘ g) ,
          ∼-trans (K ∘ f) H' ∼ ∼-trans H (L ∘ g))              ≃⟨ VII ⟩
      (Σ H' ꞉ (i ∘ f ∼ j ∘ g) , H' ∼ H)                        ≃⟨ IXV ⟩
      𝟙                                                        ■
   where
    I = ≃-comp Σ-assoc (Σ-cong (λ i' → Σ-assoc))
    II = Σ-cong (λ _ → ≃-comp (Σ-cong
          (λ _ → ≃-comp Σ-flip (Σ-cong (λ K → Σ-flip)))) Σ-flip)
    III = (Σ i' ꞉ (A → X) , i ∼ i')  ≃⟨ IV ⟩
          (Σ i' ꞉ (A → X) , i ＝ i') ≃⟨ V ⟩
          𝟙                          ■
     where
      IV = Σ-cong (λ - → ≃-sym (≃-funext fe i -))
      V = singleton-≃-𝟙 (singleton-types-are-singletons i)
    VI = ≃-comp (Σ-cong (λ - → ≃-sym (≃-funext fe j -)))
                (singleton-≃-𝟙 (singleton-types-are-singletons j))
    VII = (Σ i' ꞉ (A → X) , Σ K ꞉ i ∼ i' ,
            Σ j' ꞉ (B → X) , Σ L ꞉ j ∼ j' ,
             Σ H' ꞉ (i' ∘ f ∼ j' ∘ g) ,
              ∼-trans (K ∘ f) H' ∼ ∼-trans H (L ∘ g))           ≃⟨ IIIV ⟩
          (Σ (i' , K) ꞉ (Σ i' ꞉ (A → X) , i ∼ i') ,
            Σ j' ꞉ (B → X) , Σ L ꞉ j ∼ j' ,
             Σ H' ꞉ (i' ∘ f ∼ j' ∘ g) ,
              ∼-trans (K ∘ f) H' ∼ ∼-trans H (L ∘ g))           ≃⟨ IX ⟩
           (Σ j' ꞉ (B → X) , Σ L ꞉ j ∼ j' ,
             Σ H' ꞉ (i ∘ f ∼ j' ∘ g) ,
              ∼-trans (∼-refl ∘ f) H' ∼ ∼-trans H (L ∘ g))      ≃⟨ XI ⟩
           (Σ (j' , L) ꞉ (Σ j' ꞉ (B → X) , j ∼ j') ,
             Σ H' ꞉ (i ∘ f ∼ j' ∘ g) ,
              ∼-trans (∼-refl ∘ f) H' ∼ ∼-trans H (L ∘ g))      ≃⟨ XII ⟩
           (Σ H' ꞉ (i ∘ f ∼ j ∘ g) ,
             ∼-trans (∼-refl ∘ f) H' ∼ ∼-trans H (∼-refl ∘ g))  ≃⟨ XIII ⟩
           (Σ H' ꞉ (i ∘ f ∼ j ∘ g) , H' ∼ H)                    ■
     where
      IIIV = ≃-sym Σ-assoc
      IX = prop-indexed-sum (equiv-to-prop III 𝟙-is-prop) (i , ∼-refl)
      XI = ≃-sym Σ-assoc
      XII = prop-indexed-sum (equiv-to-prop VI 𝟙-is-prop) (j , ∼-refl)
      XIII = Σ-cong (λ H' → Π-cong fe fe (λ c → ＝-cong (refl ∙ H' c)
                    (∼-trans H (λ _ → refl) c) refl-left-neutral
                      (refl-right-neutral (H c) ⁻¹)))
    IXV = ≃-comp (Σ-cong (λ - → ≃-sym (≃-funext fe - H)))
                 (singleton-≃-𝟙 (equiv-to-singleton (Σ-cong (λ - → ＝-flip))
                 (singleton-types-are-singletons H)))

cocone-identity-characterization : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
                                   (f : C → A) (g : C → B) (X : 𝓣  ̇)
                                 → (u u' : cocone f g X)
                                 → (u ＝ u') ≃ (cocone-family f g X u u')
cocone-identity-characterization f g X u u' =
 (canonical-map-from-identity-to-cocone-family f g X u u' ,
   Yoneda-Theorem-forth u (canonical-map-from-identity-to-cocone-family f g X u)
    (cocone-family-is-identity-system f g X u) u')

inverse-cocone-map : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
                     (f : C → A) (g : C → B) (X : 𝓣  ̇)
                   → (u u' : cocone f g X)
                   → cocone-family f g X u u'
                   → u ＝ u'
inverse-cocone-map f g X u u' =
 ⌜ (cocone-identity-characterization f g X u u') ⌝⁻¹

\end{code}

We also introduce the notion of a dependent cocone.

TODO. Characterize the identity type of dependent cocones.

\begin{code}

dependent-cocone : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
                   (f : C → A) (g : C → B) (X : 𝓣  ̇)
                   (t : cocone f g X) (P : X → 𝓣'  ̇)
                 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣'  ̇
dependent-cocone {_} {_} {_} {_} {_} {A} {B} {C} f g X (i , j , H) P =
 Σ i' ꞉ ((a : A) → P (i a)) , Σ j' ꞉ ((b : B) → P (j b)) ,
  ((c : C) → transport P (H c) (i' (f c)) ＝ j' (g c))

\end{code}

Now we will define the universal property, induction principle and propositional
computation rules for pushouts and show they are inter-derivable.

In fact we will only show:
(1) The induction principle and propositional computation rules implies the
  the recursion principle with corresponding computation rules and the uniqueness
  principle.

(2) The recursion principle with corresponding computation rules and the
  uniqueness principle implies the non-dependent universal property.

(3) The universal property implies the induction principle.

\begin{code}

canonical-map-to-cocone
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇) 
   (f : C → A) (g : C → B) (s : cocone f g S) (X : 𝓣  ̇)
 → (S → X) → cocone f g X
canonical-map-to-cocone S f g (i , j , G) X u =
 (u ∘ i , u ∘ j , ∼-ap-∘ u G)

Pushout-Universal-Property
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇) 
   (f : C → A) (g : C → B) (s : cocone f g S) (X : 𝓣  ̇)
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤' ⊔ 𝓣  ̇
Pushout-Universal-Property S f g s X
 = is-equiv (canonical-map-to-cocone S f g s X)

canonical-map-to-dependent-cocone
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇)
   (f : C → A) (g : C → B) (s : cocone f g S) (P : S →  𝓣  ̇)
 → ((x : S) → P x) → dependent-cocone f g S s P
canonical-map-to-dependent-cocone S f g (i , j , G) P d =
 (d ∘ i , d ∘ j , λ c → apd d (G c))

Pushout-Dependent-Universal-Property
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇) 
   (f : C → A) (g : C → B) (s : cocone f g S) (P : S →  𝓣  ̇)
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤' ⊔ 𝓣  ̇
Pushout-Dependent-Universal-Property S f g s P =
 is-equiv (canonical-map-to-dependent-cocone S f g s P)

Pushout-Induction-Principle
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇)
   (f : C → A) (g : C → B) (s : cocone f g S) (P : S → 𝓣  ̇)
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤' ⊔ 𝓣  ̇
Pushout-Induction-Principle {_} {_} {_} {_} {_} {A} {B} {C} S f g (i , j , G) P 
 = (l : (a : A) → P (i a))
 → (r : (b : B) → P (j b))
 → ((c : C) → transport P (G c) (l (f c)) ＝ r (g c))
 → (x : S) → P x

Pushout-Computation-Rule₁
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇) 
   (f : C → A) (g : C → B) (s : cocone f g S) (P : S → 𝓣  ̇)
 → Pushout-Induction-Principle S f g s P
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣  ̇
Pushout-Computation-Rule₁
 {_} {_} {_} {_} {_} {A} {B} {C} S f g (i , j , G) P S-ind
 = (l : (a : A) → P (i a))
 → (r : (b : B) → P (j b))
 → (H : (c : C) → transport P (G c) (l (f c)) ＝ r (g c))
 → (a : A)
 → S-ind l r H (i a) ＝ l a

Pushout-Computation-Rule₂
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇)
   (f : C → A) (g : C → B) (s : cocone f g S) (P : S → 𝓣  ̇)
 → Pushout-Induction-Principle S f g s P
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣  ̇
Pushout-Computation-Rule₂
 {_} {_} {_} {_} {_} {A} {B} {C} S f g (i , j , G) P S-ind
 = (l : (a : A) → P (i a))
 → (r : (b : B) → P (j b))
 → (H : (c : C) → transport P (G c) (l (f c)) ＝ r (g c))
 → (b : B)
 → S-ind l r H (j b) ＝ r b

Pushout-Computation-Rule₃
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇) 
   (f : C → A) (g : C → B) (s : cocone f g S) (P : S → 𝓣  ̇)
   (S-ind : Pushout-Induction-Principle S f g s P)
 → Pushout-Computation-Rule₁ S f g s P S-ind
 → Pushout-Computation-Rule₂ S f g s P S-ind
 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣  ̇
Pushout-Computation-Rule₃
 {_} {_} {_} {_} {_}{A} {B} {C} S f g (i , j , G) P S-ind S-comp₁ S-comp₂
 = (l : (a : A) → P (i a))
 → (r : (b : B) → P (j b))
 → (H : (c : C) → transport P (G c) (l (f c)) ＝ r (g c))
 → (c : C)
 → apd (S-ind l r H) (G c) ∙ S-comp₂ l r H (g c)
 ＝ ap (transport P (G c)) (S-comp₁ l r H (f c)) ∙ H c

\end{code}

Now we will use a record type to give the pushout, point and path constructors,
and the dependent universal property.

begin{code}

record pushouts-exist {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (f : C → A) (g : C → B) : 𝓤ω
 where
 field
  pushout : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
  inll : A → pushout 
  inrr : B → pushout 
  glue : (c : C) → inll (f c) ＝ inrr (g c)
  pushout-induction
   : {P : pushout → 𝓣  ̇}
   → Pushout-Induction-Principle pushout f g (inll , inrr , glue) P
  pushout-ind-comp-inll
   : {P : pushout → 𝓣  ̇}
   → Pushout-Computation-Rule₁ pushout f g (inll , inrr , glue) P
      pushout-induction
  pushout-ind-comp-inrr
   : {P : pushout → 𝓣  ̇}
   → Pushout-Computation-Rule₂ pushout f g (inll , inrr , glue) P
      pushout-induction
  pushout-ind-comp-glue
   : {P : pushout → 𝓣  ̇}
   → Pushout-Computation-Rule₃ pushout f g (inll , inrr , glue) P
      pushout-induction pushout-ind-comp-inll pushout-ind-comp-inrr

end{code}

We will observe that the pushout is a cocone and begin deriving some key
results from the induction principles:
recursion principle (along with corresponding computation rules), the uniqueness
principle and the universal property.

The following are logically equivalent

1) The induction principle with propositional computation rules
2) The recursion principle with propositional computation rules and the
   uniqueness principle
3) The universal property.

begin{code}

 pushout-cocone : cocone f g pushout
 pushout-cocone = (inll , inrr , glue)
   
 pushout-recursion : {D : 𝓣  ̇}
                   → (l : A → D)
                   → (r : B → D)
                   → ((c : C) → l (f c) ＝ r (g c))
                   → pushout → D
 pushout-recursion l r G =
  pushout-induction l r (λ c → (transport-const (glue c) ∙ G c))

 pushout-rec-comp-inll : {D : 𝓣  ̇}
                       → (l : A → D)
                       → (r : B → D)
                       → (G : (c : C) → l (f c) ＝ r (g c))
                       → (a : A)
                       → pushout-recursion l r G (inll a) ＝ l a
 pushout-rec-comp-inll l r G =
  pushout-ind-comp-inll l r (λ c → (transport-const (glue c) ∙ G c))

 pushout-rec-comp-inrr : {D : 𝓣  ̇}
                       → (l : A → D)
                       → (r : B → D)
                       → (G : (c : C) → l (f c) ＝ r (g c))
                       → (b : B)
                       → pushout-recursion l r G (inrr b) ＝ r b
 pushout-rec-comp-inrr l r G =
  pushout-ind-comp-inrr l r (λ c → (transport-const (glue c) ∙ G c))

 pushout-rec-comp-glue
  : {D : 𝓣  ̇}
  → (l : A → D)
  → (r : B → D)
  → (G : (c : C) → l (f c) ＝ r (g c))
  → (c : C)
  → ap (pushout-recursion l r G) (glue c) ∙ pushout-rec-comp-inrr l r G (g c) 
  ＝ pushout-rec-comp-inll l r G (f c) ∙ G c
 pushout-rec-comp-glue {𝓣} {D} l r G c =
  ap (pushout-recursion l r G) (glue c) ∙ pushout-rec-comp-inrr l r G (g c)                                                                 ＝⟨ III ⟩
  transport-const (glue c) ⁻¹ ∙ apd (pushout-recursion l r G) (glue c)
   ∙ pushout-rec-comp-inrr l r G (g c)                      ＝⟨ V ⟩
  transport-const (glue c) ⁻¹
    ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
    ∙ (transport-const (glue c) ∙ G c)                      ＝⟨ VI ⟩
  transport-const (glue c) ⁻¹
    ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
    ∙ transport-const (glue c) ∙ G c                        ＝⟨ IX ⟩
  pushout-rec-comp-inll l r G (f c) ∙ G c                      ∎
  where
   II : ap (pushout-recursion l r G) (glue c)
      ＝ transport-const (glue c) ⁻¹
         ∙ apd (pushout-induction l r (λ - → (transport-const (glue -) ∙ G -)))
               (glue c)
   II = apd-from-ap (pushout-recursion l r G) (glue c)
   III = ap (_∙ pushout-rec-comp-inrr l r G (g c)) II 
   IV : apd (pushout-recursion l r G) (glue c)
       ∙ pushout-rec-comp-inrr l r G (g c)
      ＝ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
       ∙ (transport-const (glue c) ∙ G c)
   IV = pushout-ind-comp-glue l r (λ - → (transport-const (glue -) ∙ G -)) c
   V : transport-const (glue c) ⁻¹ ∙ apd (pushout-recursion l r G) (glue c)
        ∙ pushout-rec-comp-inrr l r G (g c)
     ＝ transport-const (glue c) ⁻¹
        ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
        ∙ (transport-const (glue c) ∙ G c)
   V = ap-on-left-is-assoc (transport-const (glue c) ⁻¹) IV
   VI = ∙assoc (transport-const (glue c) ⁻¹ ∙ ap (transport (λ - → D) (glue c))
               (pushout-rec-comp-inll l r G (f c))) (transport-const (glue c))
               (G c) ⁻¹
   VII : ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
         ∙ transport-const (glue c)
       ＝ transport-const (glue c) ∙ pushout-rec-comp-inll l r G (f c)
   VII = homotopies-are-natural (transport (λ - → D) (glue c)) id
          (λ - → transport-const (glue c)) ⁻¹
   VIII : transport-const (glue c) ⁻¹
        ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
        ∙ transport-const (glue c)
     ＝ pushout-rec-comp-inll l r G (f c)
   VIII = ∙assoc (transport-const (glue c) ⁻¹)
                 (ap (transport (λ - → D) (glue c))
                 (pushout-rec-comp-inll l r G (f c))) (transport-const (glue c))
          ∙ ap-left-inverse (transport-const (glue c)) VII 
   IX = ap (_∙ G c) VIII

 pushout-uniqueness : (X : 𝓣 ̇)
                    → (s s' : pushout → X)
                    → (H : (a : A) → s (inll a) ＝ s' (inll a))
                    → (H' : (b : B) → s (inrr b) ＝ s' (inrr b))
                    → (G : (c : C)
                      → ap s (glue c) ∙ H' (g c) ＝ H (f c) ∙ ap s' (glue c))
                    → (x : pushout) → s x ＝ s' x
 pushout-uniqueness X s s' H H' G =
  pushout-induction H H' I
  where
   I : (c : C)
     → transport (λ - → s - ＝ s' -) (glue c) (H (f c)) ＝ H' (g c)
   I c = transport (λ - → s - ＝ s' -) (glue c) (H (f c)) ＝⟨ II ⟩
         ap s (glue c) ⁻¹ ∙ H (f c) ∙ ap s' (glue c)      ＝⟨ III ⟩
         H' (g c)                                         ∎
    where
     II = transport-after-ap' (glue c) s s' (H (f c))
     III = ap s (glue c) ⁻¹ ∙ H (f c) ∙ ap s' (glue c)   ＝⟨ IV ⟩
           ap s (glue c) ⁻¹ ∙ (H (f c) ∙ ap s' (glue c)) ＝⟨ V ⟩
           H' (g c)                                       ∎
      where
       IV = ∙assoc (ap s (glue c) ⁻¹) (H (f c)) (ap s' (glue c))
       V = ap-left-inverse (ap s (glue c)) (G c ⁻¹)
   
 pushout-universal-property
  : (X : 𝓣 ̇)
  → Pushout-Universal-Property pushout f g (inll , inrr , glue) X
 pushout-universal-property X = ((ψ , ϕ-ψ) , (ψ , ψ-ϕ))
  where
   ϕ : (pushout → X) → cocone f g X
   ϕ u = canonical-map-to-cocone pushout f g (inll , inrr , glue) X u
   ψ : cocone f g X → (pushout → X)
   ψ (l , r , G) = pushout-recursion l r G
   ψ-ϕ : ψ ∘ ϕ ∼ id
   ψ-ϕ u = dfunext fe (pushout-uniqueness X ((ψ ∘ ϕ) u) u
                   (pushout-rec-comp-inll (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
                   (pushout-rec-comp-inrr (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
                   (pushout-rec-comp-glue (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue)))
   ϕ-ψ : ϕ ∘ ψ ∼ id
   ϕ-ψ (l , r , G) =
    inverse-cocone-map f g X ((ϕ ∘ ψ) (l , r , G)) (l , r , G)
     (pushout-rec-comp-inll l r G , pushout-rec-comp-inrr l r G ,
      ∼-sym (pushout-rec-comp-glue l r G))
   
end{code}

We investigate only postulating the (non-dependent) universal property.

\begin{code}

record pushouts-exist' {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (f : C → A) (g : C → B) : 𝓤ω
 where
 field
  pushout : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
  inll : A → pushout 
  inrr : B → pushout 
  glue : (c : C) → inll (f c) ＝ inrr (g c)
  pushout-universal-property
   : {X : 𝓣  ̇}
   → Pushout-Universal-Property pushout f g (inll , inrr , glue) X

 pushout-cocone : cocone f g pushout
 pushout-cocone = (inll , inrr , glue)

\end{code}

We will unpack the equivalence established by the universal property.

\begin{code}

 opaque
  pushout-fiber-is-singleton
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → is-contr (fiber (canonical-map-to-cocone pushout f g pushout-cocone X) s)
  pushout-fiber-is-singleton {_} {X} s
   = equivs-are-vv-equivs (canonical-map-to-cocone pushout f g pushout-cocone X)
    pushout-universal-property s

  pushout-fiber-is-singleton'
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → is-contr (Σ u ꞉ (pushout → X) ,
                 cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s)
  pushout-fiber-is-singleton' {_} {X} s 
   = equiv-to-singleton' (Σ-cong (λ - → cocone-identity-characterization f g X
                          (- ∘ inll , - ∘ inrr , ∼-ap-∘ - glue) s))
                         (pushout-fiber-is-singleton s)

  pushout-fiber-center
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → Σ u ꞉ (pushout → X) ,
      cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s
  pushout-fiber-center s = center (pushout-fiber-is-singleton' s)

  pushout-fiber-centrality
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → is-central (Σ u ꞉ (pushout → X) ,
                   cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s)
                (pushout-fiber-center s)
  pushout-fiber-centrality s = centrality (pushout-fiber-is-singleton' s)

  pushout-unique-map : {X : 𝓣  ̇}
                     → (s : cocone f g X)
                     → Σ u ꞉ (pushout → X) ,
                        cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s
                     → pushout → X
  pushout-unique-map s (u , _) = u

  pushout-inll-homotopy
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → (z : Σ u ꞉ (pushout → X) ,
            cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s)
   → (pushout-unique-map s z) ∘ inll ∼ cocone-vertical-map f g X s
  pushout-inll-homotopy s (u , K , L , M) = K

  pushout-inrr-homotopy
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → (z : Σ u ꞉ (pushout → X) ,
            cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s)
   → (pushout-unique-map s z) ∘ inrr ∼ cocone-horizontal-map f g X s
  pushout-inrr-homotopy s (u , K , L , M) = L

  pushout-glue-homotopy
   : {X : 𝓣  ̇}
   → (s : cocone f g X)
   → (z : Σ u ꞉ (pushout → X) ,
            cocone-family f g X (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue) s)
   → ∼-trans ((pushout-inll-homotopy s z) ∘ f) (cocone-commuting-square f g X s)
   ∼ ∼-trans (∼-ap-∘ (pushout-unique-map s z) glue)
             ((pushout-inrr-homotopy s z) ∘ g)
  pushout-glue-homotopy s (u , K , L , M) = M

\end{code}

Now we can derive the recursion principle, the corresponding propositional
computation rules and the uniqueness principles.

\begin{code}

 pushout-recursion : {D : 𝓣  ̇}
                   → (l : A → D)
                   → (r : B → D)
                   → ((c : C) → l (f c) ＝ r (g c))
                   → pushout → D
 pushout-recursion l r G
  = pushout-unique-map (l , r , G) (pushout-fiber-center (l , r , G))

 pushout-rec-comp-inll : {D : 𝓣  ̇}
                       → (l : A → D)
                       → (r : B → D)
                       → (G : (c : C) → l (f c) ＝ r (g c))
                       → (a : A)
                       → pushout-recursion l r G (inll a) ＝ l a
 pushout-rec-comp-inll l r G 
  = pushout-inll-homotopy (l , r , G) (pushout-fiber-center (l , r , G)) 

 pushout-rec-comp-inrr : {D : 𝓣  ̇}
                       → (l : A → D)
                       → (r : B → D)
                       → (G : (c : C) → l (f c) ＝ r (g c))
                       → (b : B)
                       → pushout-recursion l r G (inrr b) ＝ r b
 pushout-rec-comp-inrr l r G
  = pushout-inrr-homotopy (l , r , G) (pushout-fiber-center (l , r , G))
 
 pushout-rec-comp-glue
  : {D : 𝓣  ̇}
  → (l : A → D)
  → (r : B → D)
  → (G : (c : C) → l (f c) ＝ r (g c))
  → (c : C)
  → ap (pushout-recursion l r G) (glue c) ∙ pushout-rec-comp-inrr l r G (g c) 
  ＝ pushout-rec-comp-inll l r G (f c) ∙ G c
 pushout-rec-comp-glue l r G c
  = pushout-glue-homotopy (l , r , G) (pushout-fiber-center (l , r , G)) c ⁻¹

 pushout-uniqueness : {X : 𝓣 ̇}
                    → (u u' : pushout → X)
                    → (H : (a : A) → u (inll a) ＝ u' (inll a))
                    → (H' : (b : B) → u (inrr b) ＝ u' (inrr b))
                    → (M : (c : C)
                     → ap u (glue c) ∙ H' (g c) ＝ H (f c) ∙ ap u' (glue c))
                    → (x : pushout) → u x ＝ u' x
 pushout-uniqueness {_} {X} u u' H H' M
  = happly (pr₁ (from-Σ-＝ (singletons-are-props
    (pushout-fiber-is-singleton' (u' ∘ inll , u' ∘ inrr , ∼-ap-∘ u' glue))
     (u , H , H' , λ c → M c ⁻¹)
      (u' , ∼-refl , ∼-refl , λ c → refl-left-neutral))))

\end{code}

Finally, we can derive the induction principle and the corresponding propositional
computation rules(?). First we will introduce an auxillary type which we will
call pre-induction. 

\begin{code}

 opaque
  pre-induction
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → ((c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → pushout → Σ x ꞉ pushout , P x
  pre-induction {_} {P} l r G = pushout-recursion l' r' G'
   where
    l' : A → Σ x ꞉ pushout , P x
    l' a = (inll a , l a)
    r' : B → Σ x ꞉ pushout , P x
    r' b = (inrr b , r b)
    G' : (c : C) → l' (f c) ＝ r' (g c)
    G' c = to-Σ-＝ (glue c , G c)

  pre-induction-comp-inll
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (a : A)
   → pre-induction l r G (inll a) ＝ (inll a , l a)
  pre-induction-comp-inll {_} {P} l r G = pushout-rec-comp-inll l' r' G'
   where
    l' : A → Σ x ꞉ pushout , P x
    l' a = (inll a , l a)
    r' : B → Σ x ꞉ pushout , P x
    r' b = (inrr b , r b)
    G' : (c : C) → l' (f c) ＝ r' (g c)
    G' c = to-Σ-＝ (glue c , G c)

  pre-induction-comp-inrr
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (b : B)
   → pre-induction l r G (inrr b) ＝ (inrr b , r b)
  pre-induction-comp-inrr {_} {P} l r G = pushout-rec-comp-inrr l' r' G'
   where
    l' : A → Σ x ꞉ pushout , P x
    l' a = (inll a , l a)
    r' : B → Σ x ꞉ pushout , P x
    r' b = (inrr b , r b)
    G' : (c : C) → l' (f c) ＝ r' (g c)
    G' c = to-Σ-＝ (glue c , G c)

  pre-induction-comp-glue
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (c : C)
   → ap (pre-induction l r G) (glue c) ∙ pre-induction-comp-inrr l r G (g c) 
   ＝ pre-induction-comp-inll l r G (f c) ∙ to-Σ-＝ (glue c , G c)
  pre-induction-comp-glue {_} {P} l r G = pushout-rec-comp-glue l' r' G'
   where
    l' : A → Σ x ꞉ pushout , P x
    l' a = (inll a , l a)
    r' : B → Σ x ꞉ pushout , P x
    r' b = (inrr b , r b)
    G' : (c : C) → l' (f c) ＝ r' (g c)
    G' c = to-Σ-＝ (glue c , G c)

  pre-induction-id
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → ((c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → pushout → pushout
  pre-induction-id l r G = pr₁ ∘ pre-induction l r G

  pre-induction-id-is-id
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (x : pushout) → pre-induction-id l r G x ＝ x
  pre-induction-id-is-id {_} {P} l r G
   = pushout-uniqueness (pre-induction-id l r G) id
      (λ a → ap pr₁ (pre-induction-comp-inll l r G a))
       (λ b → ap pr₁ (pre-induction-comp-inrr l r G b))
        I
   where
    I : (c : C)
      → ap (pre-induction-id l r G) (glue c)
        ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))
      ＝ ap pr₁ (pre-induction-comp-inll l r G (f c)) ∙ ap id (glue c)
    I c = ap (pre-induction-id l r G) (glue c)
          ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))            ＝⟨ II ⟩
          ap pr₁ (ap (pre-induction l r G) (glue c))
          ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))            ＝⟨ III ⟩
          ap pr₁ (ap (pre-induction l r G) (glue c)
          ∙ pre-induction-comp-inrr l r G (g c))                    ＝⟨ IV ⟩
          ap pr₁ (pre-induction-comp-inll l r G (f c)
          ∙ to-Σ-＝ (glue c , G c))                                 ＝⟨ V ⟩
          ap pr₁ (pre-induction-comp-inll l r G (f c))
          ∙ ap pr₁ (to-Σ-＝ (glue c , G c))                         ＝⟨ VII ⟩
          ap pr₁ (pre-induction-comp-inll l r G (f c))
          ∙ ap id (glue c)                                          ∎
     where
      II : ap (pre-induction-id l r G) (glue c)
          ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))
        ＝ ap pr₁ (ap (pre-induction l r G) (glue c))
          ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c)) 
      II = ap (_∙ ap pr₁ (pre-induction-comp-inrr l r G (g c)))
              (ap-ap (pre-induction l r G) pr₁ (glue c) ⁻¹)
      III : ap pr₁ (ap (pre-induction l r G) (glue c))
           ∙ ap pr₁ (pre-induction-comp-inrr l r G (g c))
          ＝ ap pr₁ (ap (pre-induction l r G) (glue c)
           ∙ pre-induction-comp-inrr l r G (g c))
      III = ap-∙ pr₁ (ap (pre-induction l r G) (glue c))
                 (pre-induction-comp-inrr l r G (g c)) ⁻¹
      IV : ap pr₁ (ap (pre-induction l r G) (glue c)
          ∙ pre-induction-comp-inrr l r G (g c))
         ＝ ap pr₁ (pre-induction-comp-inll l r G (f c)
          ∙ to-Σ-＝ (glue c , G c))  
      IV = ap (ap pr₁) (pre-induction-comp-glue l r G c)
      V : ap pr₁ (pre-induction-comp-inll l r G (f c)
          ∙ to-Σ-＝ (glue c , G c))
        ＝ ap pr₁ (pre-induction-comp-inll l r G (f c))
          ∙ ap pr₁ (to-Σ-＝ (glue c , G c)) 
      V = ap-∙ pr₁ (pre-induction-comp-inll l r G (f c)) (to-Σ-＝ (glue c , G c))
      VI : ap pr₁ (to-Σ-＝ (glue c , G c)) ＝ ap id (glue c) 
      VI = ap pr₁ (to-Σ-＝ (glue c , G c)) ＝⟨ ap-pr₁-to-Σ-＝ (glue c , G c) ⟩
           glue c                          ＝⟨ ap-id-is-id' (glue c) ⟩
           ap id (glue c)                  ∎
      VII : ap pr₁ (pre-induction-comp-inll l r G (f c))
           ∙ ap pr₁ (to-Σ-＝ (glue c , G c))
          ＝ ap pr₁ (pre-induction-comp-inll l r G (f c))
           ∙ ap id (glue c)   
      VII = ap (ap pr₁ (pre-induction-comp-inll l r G (f c)) ∙_) VI 

  pre-induction-family
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (x : pushout) → P (pre-induction-id l r G x)
  pre-induction-family l r G = pr₂ ∘ pre-induction l r G

  pre-induction-family-comp-inll
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (a : A)
   → transport P (pre-induction-id-is-id l r G (inll a))
                 (pre-induction-family l r G (inll a))
   ＝ l a
  pre-induction-family-comp-inll l r G a
   = {!!}
   where
    I : (a : A)
      → pre-induction-id-is-id l r G (inll a)
      ＝ ap pr₁ (pre-induction-comp-inll l r G a)
    I a = {!pushout-rec-comp-inll!}

\end{code}

Now we can define the induction principle and computation rules.

\begin{code}

 pushout-induction
  : {P : pushout → 𝓣  ̇}
  → Pushout-Induction-Principle pushout f g (inll , inrr , glue) P
 pushout-induction {_} {P} l r G x
  = transport P (pre-induction-id-is-id l r G x) (pre-induction-family l r G x)

 pushout-induction-comp-inll
  : {P : pushout → 𝓣  ̇}
  → Pushout-Computation-Rule₁ pushout f g (inll , inrr , glue) P pushout-induction 
 pushout-induction-comp-inll l r H a
  = pre-induction-family-comp-inll l r H a

 pushout-induction-comp-inrr
  : {P : pushout → 𝓣  ̇}
  → Pushout-Computation-Rule₂ pushout f g (inll , inrr , glue) P pushout-induction 
 pushout-induction-comp-inrr l r H b = {!!}

 pushout-induction-comp-glue
  : {P : pushout → 𝓣  ̇}
  → Pushout-Computation-Rule₃ pushout f g (inll , inrr , glue) P pushout-induction
     pushout-induction-comp-inll pushout-induction-comp-inrr
 pushout-induction-comp-glue = {!!}

\end{code}


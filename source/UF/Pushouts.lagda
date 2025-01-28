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

\begin{code}

dependent-cocone : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
                   (f : C → A) (g : C → B) (X : 𝓣  ̇)
                   (t : cocone f g X) (P : X → 𝓣'  ̇)
                 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣'  ̇
dependent-cocone {_} {_} {_} {_} {_} {A} {B} {C} f g X (i , j , H) P =
 Σ i' ꞉ ((a : A) → P (i a)) , Σ j' ꞉ ((b : B) → P (j b)) ,
  ((c : C) → transport P (H c) (i' (f c)) ＝ j' (g c))

\end{code}

Now we will define the (dependent) universal property, induction principle and
propositional computation rules for pushouts and show they are inter-derivable*.

*In fact we will only show:
(1)
  The dependent universal propery implies the induction principle and
  propositional computation rules.

(2)
  The induction principle and propositional computationrules implies the
  (non-dependeny) universal property.

We will not show
(3)
  The (non-dependent) universal property implies the dependent universal
  property.

(3) Is shown in the Agda Unimath library (*link*). It involves something called
the pullback property of pushouts which we wish to avoid exploring for now.*

In general, we know that the universal property of (higher) inductive types is
equivalent to the induction principle with propositional computation rules.

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

Pushout-Dependent-Universal-Property-implies-Induction
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇) 
   (f : C → A) (g : C → B) (s : cocone f g S)
 → ((P : S → 𝓣  ̇) → Pushout-Dependent-Universal-Property S f g s P)
 → ((P : S → 𝓣  ̇) → Pushout-Induction-Principle S f g s P)
Pushout-Dependent-Universal-Property-implies-Induction
 S f g s dep-UP P l r G = inv (l , r , G)
 where
  inv : dependent-cocone f g S s P
      → ((x : S) → P x)
  inv = ⌜ (canonical-map-to-dependent-cocone S f g s P , dep-UP P) ⌝⁻¹

Pushout-Dependent-Universal-Property-implies-Computation-Rule₁
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇) 
   (f : C → A) (g : C → B) (s : cocone f g S)
 → (S-UP : (P : S → 𝓣  ̇) → Pushout-Dependent-Universal-Property S f g s P)
 → (P : S → 𝓣  ̇) → Pushout-Computation-Rule₁ S f g s P
    (Pushout-Dependent-Universal-Property-implies-Induction S f g s S-UP P)
Pushout-Dependent-Universal-Property-implies-Computation-Rule₁
 S f g (i , j , G) S-UP P l r H a = {!!}
 where
  H' : is-equiv (canonical-map-to-dependent-cocone S f g (i , j , G) P)
     → is-section (canonical-map-to-dependent-cocone S f g (i , j , G) P)
  H' =
   equivs-are-sections (canonical-map-to-dependent-cocone S f g (i , j , G) P)
  H'-eq : retraction-of
           (canonical-map-to-dependent-cocone S f g (i , j , G) P)
            (pr₂ (S-UP P))
             ∘ canonical-map-to-dependent-cocone S f g (i , j , G) P
        ∼ id
  H'-eq =
   retraction-equation (canonical-map-to-dependent-cocone S f g (i , j , G) P)
                       (H' (S-UP P))
  H'' : is-equiv (canonical-map-to-dependent-cocone S f g (i , j , G) P)
      → has-section (canonical-map-to-dependent-cocone S f g (i , j , G) P)
  H'' =
   equivs-have-sections (canonical-map-to-dependent-cocone S f g (i , j , G) P)
  H''-eq : canonical-map-to-dependent-cocone S f g (i , j , G) P ∘
            section-of (canonical-map-to-dependent-cocone S f g (i , j , G) P)
             (pr₁ (S-UP (λ v → P v)))
         ∼ id
  H''-eq =
   section-equation (canonical-map-to-dependent-cocone S f g (i , j , G) P)
                    (H'' (S-UP P))

Pushout-Induction-and-Computation-implies-Universal-Property
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (S : 𝓤'  ̇)
   (f : C → A) (g : C → B) (s : cocone f g S)
   (S-ind : (P : S → 𝓣  ̇) → Pushout-Induction-Principle S f g s P)
   (S-comp₁ : (P : S → 𝓣  ̇) → Pushout-Computation-Rule₁ S f g s P (S-ind P))
   (S-comp₂ : (P : S → 𝓣  ̇) → Pushout-Computation-Rule₂ S f g s P (S-ind P))
 → ((P : S → 𝓣  ̇)
  → Pushout-Computation-Rule₃ S f g s P (S-ind P) (S-comp₁ P) (S-comp₂ P))
 → ((X : 𝓣  ̇) → Pushout-Universal-Property S f g s X)
Pushout-Induction-and-Computation-implies-Universal-Property = {!!}

\end{code}

Now we will use a record type to give the pushout, point and path constructors,
and the induction principle along with propositional computation rules.

\begin{code}

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
  pushout-ind-comp-l
   : {P : pushout → 𝓣  ̇}
   → Pushout-Computation-Rule₁ pushout f g (inll , inrr , glue) P
      pushout-induction
  pushout-ind-comp-r
   : {P : pushout → 𝓣  ̇}
   → Pushout-Computation-Rule₂ pushout f g (inll , inrr , glue) P
      pushout-induction
  pushout-ind-comp-G
   : {P : pushout → 𝓣  ̇}
   → Pushout-Computation-Rule₃ pushout f g (inll , inrr , glue) P
      pushout-induction pushout-ind-comp-l pushout-ind-comp-r

\end{code}

We will now observe that the pushout is a cocone and begin deriving some key
results from the induction principle:
recursion (along with corresponding computation rules), uniqueness and the
universal property.

\begin{code}

 pushout-cocone : cocone f g pushout
 pushout-cocone = (inll , inrr , glue)
   
 pushout-recursion : {D : 𝓣  ̇}
                   → (l : A → D)
                   → (r : B → D)
                   → ((c : C) → l (f c) ＝ r (g c))
                   → pushout → D
 pushout-recursion l r G =
  pushout-induction l r (λ c → (transport-const (glue c) ∙ G c))

 pushout-rec-comp-l : {D : 𝓣  ̇}
                    → (l : A → D)
                    → (r : B → D)
                    → (G : (c : C) → l (f c) ＝ r (g c))
                    → (a : A)
                    → pushout-recursion l r G (inll a) ＝ l a
 pushout-rec-comp-l l r G =
  pushout-ind-comp-l l r (λ c → (transport-const (glue c) ∙ G c))

 pushout-rec-comp-r : {D : 𝓣  ̇}
                    → (l : A → D)
                    → (r : B → D)
                    → (G : (c : C) → l (f c) ＝ r (g c))
                    → (b : B)
                    → pushout-recursion l r G (inrr b) ＝ r b
 pushout-rec-comp-r l r G =
  pushout-ind-comp-r l r (λ c → (transport-const (glue c) ∙ G c))

 pushout-rec-comp-G
  : {D : 𝓣  ̇}
  → (l : A → D)
  → (r : B → D)
  → (G : (c : C) → l (f c) ＝ r (g c))
  → (c : C)
  → ap (pushout-recursion l r G) (glue c) ∙ pushout-rec-comp-r l r G (g c) 
  ＝ pushout-rec-comp-l l r G (f c) ∙ G c
 pushout-rec-comp-G {𝓣} {D} l r G c =
  ap (pushout-recursion l r G) (glue c) ∙ pushout-rec-comp-r l r G (g c)                                                                    ＝⟨ III ⟩
  transport-const (glue c) ⁻¹ ∙ apd (pushout-recursion l r G) (glue c)
   ∙ pushout-rec-comp-r l r G (g c)                         ＝⟨ V ⟩
  transport-const (glue c) ⁻¹
    ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-l l r G (f c))
    ∙ (transport-const (glue c) ∙ G c)                      ＝⟨ VI ⟩
  transport-const (glue c) ⁻¹
    ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-l l r G (f c))
    ∙ transport-const (glue c) ∙ G c                        ＝⟨ IX ⟩
  pushout-rec-comp-l l r G (f c) ∙ G c                      ∎
  where
   II : ap (pushout-recursion l r G) (glue c)
      ＝ transport-const (glue c) ⁻¹
         ∙ apd (pushout-induction l r (λ - → (transport-const (glue -) ∙ G -)))
               (glue c)
   II = apd-from-ap (pushout-recursion l r G) (glue c)
   III = ap (_∙ pushout-rec-comp-r l r G (g c)) II 
   IV : apd (pushout-recursion l r G) (glue c) ∙ pushout-rec-comp-r l r G (g c)
      ＝ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-l l r G (f c))
       ∙ (transport-const (glue c) ∙ G c)
   IV = pushout-ind-comp-G l r (λ - → (transport-const (glue -) ∙ G -)) c
   V : transport-const (glue c) ⁻¹ ∙ apd (pushout-recursion l r G) (glue c)
        ∙ pushout-rec-comp-r l r G (g c)
     ＝ transport-const (glue c) ⁻¹
        ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-l l r G (f c))
        ∙ (transport-const (glue c) ∙ G c)
   V = ap-on-left-is-assoc (transport-const (glue c) ⁻¹) IV
   VI = ∙assoc (transport-const (glue c) ⁻¹ ∙ ap (transport (λ - → D) (glue c))
               (pushout-rec-comp-l l r G (f c))) (transport-const (glue c))
               (G c) ⁻¹
   VII : ap (transport (λ - → D) (glue c)) (pushout-rec-comp-l l r G (f c))
         ∙ transport-const (glue c)
       ＝ transport-const (glue c) ∙ pushout-rec-comp-l l r G (f c)
   VII = homotopies-are-natural (transport (λ - → D) (glue c)) id
          (λ - → transport-const (glue c)) ⁻¹
   VIII : transport-const (glue c) ⁻¹
        ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-l l r G (f c))
        ∙ transport-const (glue c)
     ＝ pushout-rec-comp-l l r G (f c)
   VIII = ∙assoc (transport-const (glue c) ⁻¹)
                 (ap (transport (λ - → D) (glue c))
                 (pushout-rec-comp-l l r G (f c))) (transport-const (glue c))
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
     III =
      ap s (glue c) ⁻¹ ∙ H (f c) ∙ ap s' (glue c)   ＝⟨ IV ⟩
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
                   (pushout-rec-comp-l (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
                   (pushout-rec-comp-r (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
                   (pushout-rec-comp-G (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue)))
   ϕ-ψ : ϕ ∘ ψ ∼ id
   ϕ-ψ (l , r , G) =
    inverse-cocone-map f g X ((ϕ ∘ ψ) (l , r , G)) (l , r , G)
     (pushout-rec-comp-l l r G , pushout-rec-comp-r l r G ,
      ∼-sym (pushout-rec-comp-G l r G))
   
\end{code}

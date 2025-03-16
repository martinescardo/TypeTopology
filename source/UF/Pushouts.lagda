Ian Ray, 15th January 2025

Editted by Ian Ray on 16th March 2025.

Pushouts are defined as higher inductive type (in the form of a record type). We
postulate point and path constructors as well as the (dependent) universal property.
We will derive other important results like induction and recursion principles along with the corresponding propositional computation rules. Of course, due to Kristina
Sojakova's dissertation (and the following paper on the same topic doi:
https://doi.org/10.1145/2775051.2676983) it is well known that for higher inductive
types with propositional computation rules the following are equivalent:

1) dependent homotopy initiality
2) induction principle with propositional computation rules
3) recursion principle with propositional computation rules and uniqueness
   principle
4) non-dependent homotopy initiality

Sojakova uses the term homotopy initiality for a sort of universality of algebra
morphisms. Here we choose a weaker phrasing of things in terms of the underlying
maps and universal properties of those maps. 

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.Pushouts (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.CoconesofSpans fe
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PropIndexedPiSigma
open import UF.Retracts
open import UF.Subsingletons
open import UF.Yoneda

\end{code}

We will now define the (dependent and non-dependent) universal properties,
induction principle and the corresponding propositional computation rules for
pushouts.

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

The following are logically equivalent (analgously to Sojakova's result):

1) The dependent universal property
2) The induction principle with propositional computation rules
3) The recursion principle with propositional computation rules and the
   uniqueness principle
4) The universal property.

Below we will derive 2), 3) and 4) from the seemingly strongest assumption 1).
In another file we will attempty to derive 1), 2) and 3) from the seemingly weakest
assumption 4) (this is a work in progress.)

\begin{code}

record pushouts-exist {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (f : C → A) (g : C → B) : 𝓤ω
 where
 field
  pushout : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
  inll : A → pushout 
  inrr : B → pushout 
  glue : (c : C) → inll (f c) ＝ inrr (g c)
  pushout-dependent-universal-property
   : {P : pushout → 𝓣  ̇}
   → Pushout-Dependent-Universal-Property pushout f g (inll , inrr , glue) P

\end{code}

We need to unpack all the information from the dependent universal property (i.e.
we extract the fact that the fiber of the canonical map is contractible).

\begin{code}

 pushout-cocone : cocone f g pushout
 pushout-cocone = (inll , inrr , glue)

 pushout-fiber-is-singleton
  : {P : pushout →  𝓣'  ̇}
  → (t : dependent-cocone f g pushout pushout-cocone P)
  → is-contr
     (fiber (canonical-map-to-dependent-cocone pushout f g pushout-cocone P) t)
 pushout-fiber-is-singleton {_} {P} t
  = equivs-are-vv-equivs
     (canonical-map-to-dependent-cocone pushout f g pushout-cocone P)
       pushout-dependent-universal-property t

 pushout-fiber-is-singleton'
  : {P : pushout →  𝓣'  ̇}
  → (t : dependent-cocone f g pushout pushout-cocone P)
  → is-contr
     (Σ d ꞉ ((x : pushout) → P x) ,
       dependent-cocone-family f g pushout pushout-cocone P
        (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t)
 pushout-fiber-is-singleton' {_} {P} t
  = equiv-to-singleton'
     (Σ-cong (λ - → dependent-cocone-identity-characterization f g pushout
              pushout-cocone P (- ∘ inll , - ∘ inrr ,  λ c → apd - (glue c)) t))
     (pushout-fiber-is-singleton t)

 pushout-fiber-center
  : {P : pushout →  𝓣'  ̇}
  → (t : dependent-cocone f g pushout pushout-cocone P)
  → Σ d ꞉ ((x : pushout) → P x) ,
      dependent-cocone-family f g pushout pushout-cocone P
       (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t
 pushout-fiber-center t = center (pushout-fiber-is-singleton' t)

 pushout-fiber-centrality
  : {P : pushout →  𝓣'  ̇}
  → (t : dependent-cocone f g pushout pushout-cocone P)
  → is-central (Σ d ꞉ ((x : pushout) → P x) ,
                 dependent-cocone-family f g pushout pushout-cocone P
                  (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t)
               (pushout-fiber-center t)
 pushout-fiber-centrality t = centrality (pushout-fiber-is-singleton' t)

 pushout-unique-map
  : {P : pushout →  𝓣'  ̇}
  → (t : dependent-cocone f g pushout pushout-cocone P)
  → Σ d ꞉ ((x : pushout) → P x) ,
     dependent-cocone-family f g pushout pushout-cocone P
      (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t
  → (x : pushout) → P x
 pushout-unique-map t (d , _) = d

 pushout-inll-homotopy
  : {P : pushout →  𝓣'  ̇}
  → (t : dependent-cocone f g pushout pushout-cocone P)
  → (z : Σ d ꞉ ((x : pushout) → P x) ,
          dependent-cocone-family f g pushout pushout-cocone P
           (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t)
  → (pushout-unique-map t z) ∘ inll
  ∼ dependent-cocone-vertical-map f g pushout pushout-cocone P t
 pushout-inll-homotopy s (u , K , L , M) = K

 pushout-inrr-homotopy
  : {P : pushout →  𝓣'  ̇}
  → (t : dependent-cocone f g pushout pushout-cocone P)
  → (z : Σ d ꞉ ((x : pushout) → P x) ,
          dependent-cocone-family f g pushout pushout-cocone P
           (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t)
  → (pushout-unique-map t z) ∘ inrr
  ∼ dependent-cocone-horizontal-map f g pushout pushout-cocone P t
 pushout-inrr-homotopy s (u , K , L , M) = L

 pushout-glue-homotopy
  : {P : pushout →  𝓣'  ̇}
  → (t : dependent-cocone f g pushout pushout-cocone P)
  → (z : Σ d ꞉ ((x : pushout) → P x) ,
          dependent-cocone-family f g pushout pushout-cocone P
           (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t)
  → ∼-trans (λ - → ap (transport P (glue -)) ((pushout-inll-homotopy t z ∘ f) -))
            (dependent-cocone-commuting-square f g pushout pushout-cocone P t)
  ∼ ∼-trans (λ - → apd (pushout-unique-map t z) (glue -))
            ((pushout-inrr-homotopy t z) ∘ g)
 pushout-glue-homotopy t (u , K , L , M) = M

\end{code}

Now we can derive the induction and recursion principle along with the corresponding
computation rules, the uniqueness of maps out of the pushout and finally the (non-
dependent) universal property.

\begin{code}

 pushout-induction
  : {P : pushout → 𝓣  ̇}
  → Pushout-Induction-Principle pushout f g (inll , inrr , glue) P
 pushout-induction l r G
  = pushout-unique-map (l , r , G) (pushout-fiber-center (l , r , G))

 pushout-ind-comp-inll
  : {P : pushout → 𝓣  ̇}
  → Pushout-Computation-Rule₁ pushout f g (inll , inrr , glue) P pushout-induction
 pushout-ind-comp-inll l r G
  = pushout-inll-homotopy (l , r , G) (pushout-fiber-center (l , r , G))

 pushout-ind-comp-inrr
  : {P : pushout → 𝓣  ̇}
  → Pushout-Computation-Rule₂ pushout f g (inll , inrr , glue) P pushout-induction
 pushout-ind-comp-inrr l r G
  = pushout-inrr-homotopy (l , r , G) (pushout-fiber-center (l , r , G))

 pushout-ind-comp-glue
  : {P : pushout → 𝓣  ̇}
  → Pushout-Computation-Rule₃ pushout f g (inll , inrr , glue) P
     pushout-induction pushout-ind-comp-inll pushout-ind-comp-inrr
 pushout-ind-comp-glue l r G c
  = pushout-glue-homotopy (l , r , G) (pushout-fiber-center (l , r , G)) c ⁻¹
   
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
   V = ap-on-left-is-assoc {_} {_} {_} {_} {_} {_} {_} (transport-const (glue c) ⁻¹)
        {apd (pushout-recursion l r G) (glue c)}
        {ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))}
        {pushout-rec-comp-inrr l r G (g c)}
        {(transport-const (glue c) ∙ G c)} IV
   VI = ∙assoc (transport-const (glue c) ⁻¹ ∙ ap (transport (λ - → D) (glue c))
               (pushout-rec-comp-inll l r G (f c))) (transport-const (glue c))
               (G c) ⁻¹
   VII' : transport-const (glue c) ∙ ap id (pushout-rec-comp-inll l r G (f c))
        ＝ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
          ∙ transport-const (glue c)
   VII' = homotopies-are-natural (transport (λ - → D) (glue c)) id
           (λ - → transport-const (glue c)) {_} {_}
           {pushout-rec-comp-inll l r G (f c)}
   VII : ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
         ∙ transport-const (glue c)
       ＝ transport-const (glue c) ∙ pushout-rec-comp-inll l r G (f c)
   VII = transport (λ - → transport-const (glue c) ∙ - 
                         ＝ ap (transport (λ - → D) (glue c))
                               (pushout-rec-comp-inll l r G (f c))
                          ∙ transport-const (glue c))
                   (ap-id-is-id (pushout-rec-comp-inll l r G (f c))) VII' ⁻¹
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
   
\end{code}

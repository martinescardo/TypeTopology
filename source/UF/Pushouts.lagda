Ian Ray, 15th January 2025

Pushouts defined as higher inductive type (in the form of records).
We postulate point and path constructors, an induction principle and
computation rules for each constructor.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.Pushouts (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons

\end{code}

We start by defining cocones and characerizing the identity type.

\begin{code}

cocone : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
         (f : C → A) (g : C → B) (X : 𝓣  ̇)
       → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣  ̇
cocone {𝓤} {𝓥} {𝓦} {𝓣} {A} {B} {C} f g X =
 Σ k ꞉ (A → X) , Σ l ꞉ (B → X) , (k ∘ f ∼ l ∘ g)

cocone-family : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
                (f : C → A) (g : C → B) (X : 𝓣  ̇)
              → cocone f g X → cocone f g X → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣  ̇
cocone-family f g X (i , j , H) (i' , j' , H') =
 Σ K ꞉ i ∼ i' , Σ L ꞉ j ∼ j' ,
  ∼-trans (K ∘ f) H' ∼ ∼-trans H (L ∘ g)

cocone-family-is-contractible
 : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
   (f : C → A) (g : C → B) (X : 𝓣  ̇)
 → (x : cocone f g X)
 → is-contr (Σ y ꞉ cocone f g X , cocone-family f g X x y)
cocone-family-is-contractible f g X (i , j , H) = {!!}

record pushouts-exist {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇} (f : C → A) (g : C → B) : 𝓤ω
 where
 field
  pushout : 𝓤 ⊔ 𝓥 ⊔ 𝓦  ̇
  inll : A → pushout 
  inrr : B → pushout 
  glue : (c : C) → inll (f c) ＝ inrr (g c)
  pushout-induction : {P : pushout → 𝓣  ̇}
                    → (l : (a : A) → P (inll a))
                    → (r : (b : B) → P (inrr b))
                    → ((c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
                    → (x : pushout) → P x
  pushout-ind-comp-l
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (a : A)
   → pushout-induction l r G (inll a) ＝ l a 
  pushout-ind-comp-r
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (b : B)
   → pushout-induction l r G (inrr b) ＝ r b
  pushout-ind-comp-G
   : {P : pushout → 𝓣  ̇}
   → (l : (a : A) → P (inll a))
   → (r : (b : B) → P (inrr b))
   → (G : (c : C) → transport P (glue c) (l (f c)) ＝ r (g c))
   → (c : C)
   → apd (pushout-induction l r G) (glue c) ∙ pushout-ind-comp-r l r G (g c)
   ＝ ap (transport P (glue c)) (pushout-ind-comp-l l r G (f c)) ∙ G c

\end{code}

We will now observe that the pushout is a cocone and begin deriving some key
results from the induction principle:
recursion (along with corresponding computation rules), universal properties
and uniqueness.

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
     II : transport (λ - → s - ＝ s' -) (glue c) (H (f c))
        ＝ ap s (glue c) ⁻¹ ∙ H (f c) ∙ ap s' (glue c)
     II = transport-lemma' (glue c) s s' (H (f c))
     III : ap s (glue c) ⁻¹ ∙ H (f c) ∙ ap s' (glue c) ＝ H' (g c)
     III =
      ap s (glue c) ⁻¹ ∙ H (f c) ∙ ap s' (glue c)   ＝⟨ IV ⟩
      ap s (glue c) ⁻¹ ∙ (H (f c) ∙ ap s' (glue c)) ＝⟨ V ⟩
      H' (g c)                                       ∎
      where
       IV = ∙assoc (ap s (glue c) ⁻¹) (H (f c)) (ap s' (glue c))
       V = ap-left-inverse (ap s (glue c)) (G c ⁻¹)
   
 pushout-universal-property : (X : 𝓣 ̇)
                            → (pushout → X) ≃ cocone f g X
 pushout-universal-property X = qinveq ϕ (ψ , ψ-ϕ , ϕ-ψ)
  where
   ϕ : (pushout → X) → cocone f g X
   ϕ u = (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue)
   ψ : cocone f g X → (pushout → X)
   ψ (l , r , G) = pushout-recursion l r G
   ψ-ϕ : ψ ∘ ϕ ∼ id
   ψ-ϕ u = dfunext fe (pushout-uniqueness X ((ψ ∘ ϕ) u) u
                   (pushout-rec-comp-l (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
                   (pushout-rec-comp-r (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
                   (pushout-rec-comp-G (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue)))
   ϕ-ψ : ϕ ∘ ψ ∼ id
   ϕ-ψ (l , r , G) =
    ap ⌜ Σ-assoc ⌝ (to-Σ-＝ (to-×-＝ I II , dfunext fe III))
    where
     I = dfunext fe (pushout-rec-comp-l l r G)
     II = dfunext fe (pushout-rec-comp-r l r G)
     III : (c : C)
         → transport (λ (l' , r') → l' ∘ f ∼ r' ∘ g) (to-×-＝ I II)
                     (∼-ap-∘ (ψ (l , r , G)) glue) c
         ＝ G c
     III c = transport (λ (l' , r') → l' ∘ f ∼ r' ∘ g) (to-×-＝ I II)
                       (∼-ap-∘ (ψ (l , r , G)) glue) c            ＝⟨ V ⟩
             pushout-rec-comp-l l r G (f c) ⁻¹
              ∙ ap (pushout-recursion l r G) (glue c)
               ∙ pushout-rec-comp-r l r G (g c)                   ＝⟨ VI ⟩
             pushout-rec-comp-l l r G (f c) ⁻¹
              ∙ (ap (pushout-recursion l r G) (glue c)
               ∙ pushout-rec-comp-r l r G (g c))                  ＝⟨ VII ⟩
             G c                                                  ∎ 
      where
       IV : ap (pushout-recursion l r G) (glue c)
              ∙ pushout-rec-comp-r l r G (g c)
          ＝ pushout-rec-comp-l l r G (f c)
              ∙ transport (λ (l' , r') → l' ∘ f ∼ r' ∘ g) (to-×-＝ I II)
                          (∼-ap-∘ (ψ (l , r , G)) glue) c
       IV = {!!} ⁻¹
       V : transport (λ (l' , r') → l' ∘ f ∼ r' ∘ g) (to-×-＝ I II)
                     (∼-ap-∘ (ψ (l , r , G)) glue) c
         ＝ pushout-rec-comp-l l r G (f c) ⁻¹
             ∙ ap (pushout-recursion l r G) (glue c)
              ∙ pushout-rec-comp-r l r G (g c)
       V = ap-left-inverse (pushout-rec-comp-l l r G (f c)) IV ⁻¹
            ∙ (∙assoc (pushout-rec-comp-l l r G (f c) ⁻¹)
                      (ap (pushout-recursion l r G) (glue c))
                      (pushout-rec-comp-r l r G (g c))) ⁻¹
       VI = ∙assoc (pushout-rec-comp-l l r G (f c) ⁻¹)
                   (ap (pushout-recursion l r G) (glue c))
                   (pushout-rec-comp-r l r G (g c))
       VII = ap-left-inverse (pushout-rec-comp-l l r G (f c))
                             (pushout-rec-comp-G l r G c)

\end{code}

    dfunext fe (pushout-induction
     (pushout-rec-comp-l (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
     (pushout-rec-comp-r (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
     I)

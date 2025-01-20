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

cocone : {A : 𝓤  ̇} {B : 𝓥  ̇} {C : 𝓦  ̇}
         (f : C → A) (g : C → B)
         (X : 𝓣  ̇)
       → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣  ̇
cocone {𝓤} {𝓥} {𝓦} {𝓣} {A} {B} {C} f g X =
 Σ k ꞉ (A → X) , Σ l ꞉ (B → X) , (k ∘ f ∼ l ∘ g)

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
   
 pushout-universal-property : (X : 𝓣 ̇)
                            → (pushout → X) ≃ cocone f g X
 pushout-universal-property X = qinveq ϕ (ψ , ψ-ϕ , ϕ-ψ)
  where
   ϕ : (pushout → X) → cocone f g X
   ϕ u = (u ∘ inll , u ∘ inrr , ∼-ap-∘ u glue)
   ψ : cocone f g X → (pushout → X)
   ψ (l , r , G) = pushout-recursion l r G
   ψ-ϕ : ψ ∘ ϕ ∼ id
   ψ-ϕ u =
    dfunext fe (pushout-induction
     (pushout-rec-comp-l (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
     (pushout-rec-comp-r (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
     I)
    where
     I : (c : C)
       → transport (λ z → (ψ ∘ ϕ) u z ＝ u z) (glue c)
          (pushout-rec-comp-l (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue) (f c))
       ＝ pushout-rec-comp-r (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue) (g c)
     I c = transport (λ z → (ψ ∘ ϕ) u z ＝ u z) (glue c)
            (pushout-rec-comp-l (u ∘ inll) (u ∘ inrr)
             (∼-ap-∘ u glue) (f c))                      ＝⟨ {!!} ⟩
           pushout-rec-comp-r (u ∘ inll) (u ∘ inrr)
            (∼-ap-∘ u glue) (g c)                        ＝⟨ {!!} ⟩
           {!!}
   ϕ-ψ : ϕ ∘ ψ ∼ id
   ϕ-ψ (l , r , G) =
    ap ⌜ Σ-assoc ⌝ (to-Σ-＝ (to-×-＝ I II , dfunext fe III))
    where
     I = dfunext fe (pushout-rec-comp-l l r G)
     II = dfunext fe (pushout-rec-comp-r l r G)
     III : (c : C)
         → transport (λ z → (λ x → pr₁ z (f x)) ∼ (λ x → pr₂ z (g x)))
                     (to-×-＝ I II)
                     (∼-ap-∘ (ψ (l , r , G)) glue) c
         ＝ G c
     III c = {!!}

\end{code}

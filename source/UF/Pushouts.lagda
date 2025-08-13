Ian Ray, 15th January 2025

Edited by Ian Ray on 16th March 2025 and 19th June 2025.

The pushout is the universal completion of a span

        C --------> B
        |
        |
        |
        v
        A
        
which consists of a pair of maps with homotopy witnessing that the square

        C --------> B
        |           |
        |           |
        |           |
        v           v
        A --------> P

commutes. The pushout also satisfies a universal property, which in the style of
HoTT/UF is stated as an equivalence of a canonical map. For details on pushouts
see section 23 of Introduction to Homotopy Type Theory by Egbert Rijke (HoTTest
summer school version:
https://github.com/martinescardo/HoTTEST-Summer-School/blob/main/HoTT/hott-intro.pdf)
or chapter 6 section 8 of HoTT book (although it is important to note that the
HoTT book utilizes definitional computation rules). In addition to the above
references, this formalization was inspired by the development found in the
agda-unimath library
(https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.pushouts.html).

In the present work pushouts are defined as a higher inductive type (in the form
of a record type). We assume point and path constructors and the (dependent)
universal property. We will derive other important results like induction and
recursion principles along with the corresponding propositional computation
rules.

Of course, due to Kristina Sojakova's dissertation (and the following paper on
the same topic doi: https://doi.org/10.1145/2775051.2676983), it is well known
that for higher inductive types with propositional computation rules the
following are equivalent:

1) dependent homotopy initiality
2) induction principle with propositional computation rules
3) recursion principle with propositional computation rules and uniqueness
   principle
4) non-dependent homotopy initiality

Sojakova uses the term 'homotopy initiality' of 'algebra morphisms' in the more
general setting. The translation from Sojakova's work to the present work is
roughly:
  algebras ---> cocones
  algebra morphisms ---> cocone morphisms
  homotopy intiality of algebra morphisms ---> universality of maps
                                               (that respect cocone structure)

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.Pushouts (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.CoconesofSpans fe
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons

\end{code}

We will now define the (dependent and non-dependent) universal properties,
induction principle and the corresponding propositional computation rules for
pushouts.

\begin{code}

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇}
         (S : 𝓤' ̇) (f : C → A) (g : C → B)
         (s@(i , j , G) : cocone f g S) 
          where

 canonical-map-to-cocone : (X : 𝓣 ̇)
                         → (S → X)
                         → cocone f g X
 canonical-map-to-cocone X u = (u ∘ i , u ∘ j , ∼-ap-∘ u G)

 Pushout-Universal-Property : (X : 𝓣 ̇)
                            → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤' ⊔ 𝓣 ̇
 Pushout-Universal-Property X = is-equiv (canonical-map-to-cocone X) 

 canonical-map-to-dependent-cocone : (P : S → 𝓣 ̇)
                                   → ((x : S) → P x)
                                   → dependent-cocone f g S s P
 canonical-map-to-dependent-cocone P d = (d ∘ i , d ∘ j , λ c → apd d (G c))

 Pushout-Dependent-Universal-Property : (P : S → 𝓣 ̇)
                                      → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤' ⊔ 𝓣 ̇
 Pushout-Dependent-Universal-Property P =
  is-equiv (canonical-map-to-dependent-cocone P)

 Pushout-Induction-Principle : (P : S → 𝓣 ̇)
                             → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓤' ⊔ 𝓣 ̇
 Pushout-Induction-Principle P
  = (l : (a : A) → P (i a))
  → (r : (b : B) → P (j b))
  → ((c : C) → transport P (G c) (l (f c)) ＝ r (g c))
  → (x : S) → P x

 Pushout-Computation-Rule₁ : (P : S → 𝓣 ̇)
                           → Pushout-Induction-Principle P
                           → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 Pushout-Computation-Rule₁ P S-ind
  = (l : (a : A) → P (i a))
  → (r : (b : B) → P (j b))
  → (H : (c : C) → transport P (G c) (l (f c)) ＝ r (g c))
  → (a : A)
  → S-ind l r H (i a) ＝ l a

 Pushout-Computation-Rule₂ : (P : S → 𝓣 ̇)
                           → Pushout-Induction-Principle P
                           → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 Pushout-Computation-Rule₂ P S-ind
  = (l : (a : A) → P (i a))
  → (r : (b : B) → P (j b))
  → (H : (c : C) → transport P (G c) (l (f c)) ＝ r (g c))
  → (b : B)
  → S-ind l r H (j b) ＝ r b

 Pushout-Computation-Rule₃ : (P : S → 𝓣 ̇)
                           → (S-ind : Pushout-Induction-Principle P)
                           → Pushout-Computation-Rule₁ P S-ind
                           → Pushout-Computation-Rule₂ P S-ind
                           → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 Pushout-Computation-Rule₃ P S-ind S-comp₁ S-comp₂
  = (l : (a : A) → P (i a))
  → (r : (b : B) → P (j b))
  → (H : (c : C) → transport P (G c) (l (f c)) ＝ r (g c))
  → (c : C)
  → apd (S-ind l r H) (G c) ∙ S-comp₂ l r H (g c)
  ＝ ap (transport P (G c)) (S-comp₁ l r H (f c)) ∙ H c

\end{code}

The following are logically equivalent (which is an instance of Sojakova's
result):

1) The dependent universal property
2) The induction principle with propositional computation rules
3) The recursion principle with propositional computation rules and the
   uniqueness principle
4) The universal property.

Below we will derive downward from assumption 1).

TODO. Derive upward from 4) to close the loop, as a means to implement the
equivalence known from Sojakova. This is a work in progress.

\begin{code}

record pushout-exists {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : C → A) (g : C → B) : 𝓤ω
 where
 field
  pushout : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  inll : A → pushout 
  inrr : B → pushout 
  glue : (c : C) → inll (f c) ＝ inrr (g c)
  pushout-dependent-universal-property
   : {P : pushout → 𝓣  ̇}
   → Pushout-Dependent-Universal-Property pushout f g (inll , inrr , glue) P

\end{code}

We need to unpack all the information from the dependent universal property
(i.e. we extract the fact that the fiber of the canonical map is contractible).

\begin{code}

 pushout-cocone : cocone f g pushout
 pushout-cocone = (inll , inrr , glue)

 module _ {P : pushout →  𝓣' ̇}
          (t : dependent-cocone f g pushout pushout-cocone P)
           where

  pushout-fiber-is-singleton
   : is-contr
      (fiber (canonical-map-to-dependent-cocone pushout f g pushout-cocone P) t)
  pushout-fiber-is-singleton 
   = equivs-are-vv-equivs
      (canonical-map-to-dependent-cocone pushout f g pushout-cocone P)
       pushout-dependent-universal-property t

  pushout-fiber-is-singleton'
   : is-contr
      (Σ d ꞉ ((x : pushout) → P x) ,
       dependent-cocone-family f g pushout pushout-cocone P
        (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t)
  pushout-fiber-is-singleton' 
   = equiv-to-singleton'
      (Σ-cong (λ - → dependent-cocone-identity-characterization f g pushout
       pushout-cocone P (- ∘ inll , - ∘ inrr ,  λ c → apd - (glue c)) t))
      pushout-fiber-is-singleton

  pushout-fiber-center
   : Σ d ꞉ ((x : pushout) → P x) ,
      dependent-cocone-family f g pushout pushout-cocone P
       (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t
  pushout-fiber-center = center pushout-fiber-is-singleton'

  pushout-fiber-centrality
   : is-central (Σ d ꞉ ((x : pushout) → P x) ,
                 dependent-cocone-family f g pushout pushout-cocone P
                  (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t)
                pushout-fiber-center 
  pushout-fiber-centrality  = centrality pushout-fiber-is-singleton' 

  pushout-unique-map
   : Σ d ꞉ ((x : pushout) → P x) ,
      dependent-cocone-family f g pushout pushout-cocone P
       (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t
   → (x : pushout) → P x
  pushout-unique-map (d , _) = d

  pushout-inll-homotopy
   : (z : Σ d ꞉ ((x : pushout) → P x) ,
           dependent-cocone-family f g pushout pushout-cocone P
            (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t)
   → (pushout-unique-map z) ∘ inll
    ∼ dependent-cocone-vertical-map f g pushout pushout-cocone P t
  pushout-inll-homotopy (u , K , L , M) = K

  pushout-inrr-homotopy
   : (z : Σ d ꞉ ((x : pushout) → P x) ,
           dependent-cocone-family f g pushout pushout-cocone P
            (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t)
   → (pushout-unique-map z) ∘ inrr
    ∼ dependent-cocone-horizontal-map f g pushout pushout-cocone P t
  pushout-inrr-homotopy (u , K , L , M) = L

  pushout-glue-homotopy
   : (z : Σ d ꞉ ((x : pushout) → P x) ,
           dependent-cocone-family f g pushout pushout-cocone P
            (d ∘ inll , d ∘ inrr ,  λ c → apd d (glue c)) t)
   → ∼-trans (λ - → ap (transport P (glue -)) ((pushout-inll-homotopy z ∘ f) -))
      (dependent-cocone-commuting-square f g pushout pushout-cocone P t)
    ∼ ∼-trans (λ - → apd (pushout-unique-map z) (glue -))
       ((pushout-inrr-homotopy z) ∘ g)
  pushout-glue-homotopy (u , K , L , M) = M

\end{code}

Now we can derive the induction and recursion principles along with the
corresponding computation rules, the uniqueness of maps out of the pushout and
the (non-dependent) universal property.

\begin{code}

 module _ {P : pushout → 𝓣 ̇} where

  pushout-induction
   : Pushout-Induction-Principle pushout f g (inll , inrr , glue) P
  pushout-induction l r G
   = pushout-unique-map (l , r , G) (pushout-fiber-center (l , r , G))

  pushout-ind-comp-inll
   : Pushout-Computation-Rule₁ pushout f g (inll , inrr , glue) P
      pushout-induction
  pushout-ind-comp-inll l r G
   = pushout-inll-homotopy (l , r , G) (pushout-fiber-center (l , r , G))

  pushout-ind-comp-inrr
   : Pushout-Computation-Rule₂ pushout f g (inll , inrr , glue) P
      pushout-induction
  pushout-ind-comp-inrr l r G
   = pushout-inrr-homotopy (l , r , G) (pushout-fiber-center (l , r , G))

  pushout-ind-comp-glue
   : Pushout-Computation-Rule₃ pushout f g (inll , inrr , glue) P
      pushout-induction pushout-ind-comp-inll pushout-ind-comp-inrr
  pushout-ind-comp-glue l r G c
   = pushout-glue-homotopy (l , r , G) (pushout-fiber-center (l , r , G)) c ⁻¹
   
 module _ {D : 𝓣 ̇} where

  pushout-recursion : (l : A → D)
                    → (r : B → D)
                    → ((c : C) → l (f c) ＝ r (g c))
                    → pushout → D
  pushout-recursion l r G =
   pushout-induction l r (λ c → (transport-const (glue c) ∙ G c))

  pushout-rec-comp-inll : (l : A → D)
                        → (r : B → D)
                        → (G : (c : C) → l (f c) ＝ r (g c))
                        → (a : A)
                        → pushout-recursion l r G (inll a) ＝ l a
  pushout-rec-comp-inll l r G =
   pushout-ind-comp-inll l r (λ c → (transport-const (glue c) ∙ G c))

  pushout-rec-comp-inrr : (l : A → D)
                        → (r : B → D)
                        → (G : (c : C) → l (f c) ＝ r (g c))
                        → (b : B)
                        → pushout-recursion l r G (inrr b) ＝ r b
  pushout-rec-comp-inrr l r G =
   pushout-ind-comp-inrr l r (λ c → (transport-const (glue c) ∙ G c))

  pushout-rec-comp-glue
   : (l : A → D)
   → (r : B → D)
   → (G : (c : C) → l (f c) ＝ r (g c))
   → (c : C)
   → ap (pushout-recursion l r G) (glue c) ∙ pushout-rec-comp-inrr l r G (g c) 
     ＝ pushout-rec-comp-inll l r G (f c) ∙ G c
  pushout-rec-comp-glue l r G c =
   ap (pushout-recursion l r G) (glue c) ∙ pushout-rec-comp-inrr l r G (g c)
                                                            ＝⟨ III ⟩
   transport-const (glue c) ⁻¹ ∙ apd (pushout-recursion l r G) (glue c)
    ∙ pushout-rec-comp-inrr l r G (g c)
                                                            ＝⟨ V ⟩
   transport-const (glue c) ⁻¹
    ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
    ∙ (transport-const (glue c) ∙ G c)
                                                            ＝⟨ VI ⟩
   transport-const (glue c) ⁻¹
    ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
    ∙ transport-const (glue c) ∙ G c
                                                            ＝⟨ IX ⟩
   pushout-rec-comp-inll l r G (f c) ∙ G c                  ∎
    where
     II : ap (pushout-recursion l r G) (glue c)
         ＝ transport-const (glue c) ⁻¹
          ∙ apd (pushout-induction l r (λ - → (transport-const (glue -) ∙ G -)))
             (glue c)
     II = apd-from-ap (pushout-recursion l r G) (glue c)
     III = ap (_∙ pushout-rec-comp-inrr l r G (g c)) II 
     IV : apd (pushout-recursion l r G) (glue c)
         ∙ pushout-rec-comp-inrr l r G (g c)
         ＝ ap (transport (λ - → D) (glue c))
               (pushout-rec-comp-inll l r G (f c))
         ∙ (transport-const (glue c) ∙ G c)
     IV = pushout-ind-comp-glue l r (λ - → (transport-const (glue -) ∙ G -)) c
     V : transport-const (glue c) ⁻¹ ∙ apd (pushout-recursion l r G) (glue c)
         ∙ pushout-rec-comp-inrr l r G (g c)
        ＝ transport-const (glue c) ⁻¹
         ∙ ap (transport (λ - → D) (glue c)) (pushout-rec-comp-inll l r G (f c))
         ∙ (transport-const (glue c) ∙ G c)
     V = ap-on-left-is-assoc (transport-const (glue c) ⁻¹)
          {apd (pushout-recursion l r G) (glue c)}
          {ap (transport (λ - → D) (glue c))
           (pushout-rec-comp-inll l r G (f c))}
          {pushout-rec-comp-inrr l r G (g c)}
          {(transport-const (glue c) ∙ G c)} IV
     VI = ∙assoc (transport-const (glue c) ⁻¹
          ∙ ap (transport (λ - → D) (glue c))
               (pushout-rec-comp-inll l r G (f c))) (transport-const (glue c))
               (G c) ⁻¹
     VII' : transport-const (glue c) ∙ ap id (pushout-rec-comp-inll l r G (f c))
           ＝ ap (transport (λ - → D) (glue c))
                 (pushout-rec-comp-inll l r G (f c))
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
            ∙ ap (transport (λ - → D) (glue c))
                 (pushout-rec-comp-inll l r G (f c))
            ∙ transport-const (glue c)
           ＝ pushout-rec-comp-inll l r G (f c)
     VIII = ∙assoc (transport-const (glue c) ⁻¹)
             (ap (transport (λ - → D) (glue c))
             (pushout-rec-comp-inll l r G (f c))) (transport-const (glue c))
             ∙ ap-left-inverse (transport-const (glue c)) VII 
     IX = ap (_∙ G c) VIII

 module _ {X : 𝓣 ̇} where

  pushout-uniqueness : (s s' : pushout → X)
                     → (H : (a : A) → s (inll a) ＝ s' (inll a))
                     → (H' : (b : B) → s (inrr b) ＝ s' (inrr b))
                     → (G : (c : C)
                       → ap s (glue c) ∙ H' (g c) ＝ H (f c) ∙ ap s' (glue c))
                     → (x : pushout) → s x ＝ s' x
  pushout-uniqueness s s' H H' G =
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
             H' (g c)                                      ∎
        where
         IV = ∙assoc (ap s (glue c) ⁻¹) (H (f c)) (ap s' (glue c))
         V = ap-left-inverse (ap s (glue c)) (G c ⁻¹)
   
  pushout-universal-property
   : Pushout-Universal-Property pushout f g (inll , inrr , glue) X
  pushout-universal-property = ((ψ , ϕ-ψ) , (ψ , ψ-ϕ))
   where
    ϕ : (pushout → X) → cocone f g X
    ϕ u = canonical-map-to-cocone pushout f g (inll , inrr , glue) X u
    ψ : cocone f g X → (pushout → X)
    ψ (l , r , G) = pushout-recursion l r G
    ψ-ϕ : ψ ∘ ϕ ∼ id
    ψ-ϕ u = dfunext fe (pushout-uniqueness ((ψ ∘ ϕ) u) u
             (pushout-rec-comp-inll (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
             (pushout-rec-comp-inrr (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue))
             (pushout-rec-comp-glue (u ∘ inll) (u ∘ inrr) (∼-ap-∘ u glue)))
    ϕ-ψ : ϕ ∘ ψ ∼ id
    ϕ-ψ (l , r , G) =
     inverse-cocone-map f g X ((ϕ ∘ ψ) (l , r , G)) (l , r , G)
      (pushout-rec-comp-inll l r G , pushout-rec-comp-inrr l r G ,
      ∼-sym (pushout-rec-comp-glue l r G))
   
\end{code}

We now provide a record that allows the existence of pushouts to be assumed polymorphically.

\begin{code}

record pushouts-exist : 𝓤ω
 where
 field
  push-ex : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : C → A) (g : C → B)
          → pushout-exists f g

\end{code}

Ian Ray, 15th January 2025

Edited by Ian Ray, 19th Jun 2025.

We will prove some results about cocones of spans. This formalization was inspired by
section 23 of Introduction to Homotopy Type Theory by Egbert Rijke (HoTTest summer
school version:
https://github.com/martinescardo/HoTTEST-Summer-School/blob/main/HoTT/hott-intro.pdf)
and the development found in the agda-unimath library
(https://unimath.github.io/agda-unimath/synthetic-homotopy-theory.cocones-under-spans.html).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module UF.CoconesofSpans (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.PropIndexedPiSigma
open import UF.Subsingletons
open import UF.Yoneda

\end{code}

A span is a pair of maps 

        C --------> A
        |
        |
        |
        v
        B

It is possible to complete a span with a commuting square

        C --------> A
        |           |
        |           |
        |           |
        v           v
        B --------> X

We call such a completion a cocone over the span.

We start by defining cocones over a span and characterizing their identity
type.

\begin{code}

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : C → A) (g : C → B)
          where

 cocone : 𝓣 ̇ → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 cocone X =
  Σ i ꞉ (A → X) , Σ j ꞉ (B → X) , (i ∘ f ∼ j ∘ g)

 cocone-vertical-map : (X : 𝓣 ̇)
                     → cocone X
                     → (A → X)
 cocone-vertical-map X (i , j , H) = i

 cocone-horizontal-map : (X : 𝓣 ̇)
                       → cocone X
                       → (B → X)
 cocone-horizontal-map X (i , j , H) = j

 cocone-commuting-square : (X : 𝓣 ̇)
                         → ((i , j , H) : cocone X)
                         → i ∘ f ∼ j ∘ g
 cocone-commuting-square X (i , j , H) = H

 cocone-family : (X : 𝓣 ̇)
               → cocone X → cocone X
               → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
 cocone-family X (i , j , H) (i' , j' , H') =
  Σ K ꞉ i ∼ i' , Σ L ꞉ j ∼ j' , ∼-trans (K ∘ f) H' ∼ ∼-trans H (L ∘ g)

 canonical-map-from-identity-to-cocone-family : (X : 𝓣 ̇)
                                              → (u u' : cocone X)
                                              → u ＝ u'
                                              → cocone-family X u u'
 canonical-map-from-identity-to-cocone-family X (i , j , H) .(i , j , H) refl =
  (∼-refl , ∼-refl , λ - → refl-left-neutral)

 cocone-family-is-identity-system
  : (X : 𝓣 ̇)
  → (x : cocone X)
  → is-contr (Σ y ꞉ cocone X , cocone-family X x y)
 cocone-family-is-identity-system {𝓣} X (i , j , H) =
  equiv-to-singleton e 𝟙-is-singleton
   where
    e : (Σ y ꞉ cocone X , cocone-family X (i , j , H) y) ≃ 𝟙 {𝓤 ⊔ 𝓣}
    e = (Σ y ꞉ cocone X , cocone-family X (i , j , H) y)    ≃⟨ I ⟩
        (Σ i' ꞉ (A → X) , Σ j' ꞉ (B → X) ,
         Σ H' ꞉ (i' ∘ f ∼ j' ∘ g) ,
          Σ K ꞉ i ∼ i' , Σ L ꞉ j ∼ j' ,
           ∼-trans (K ∘ f) H' ∼ ∼-trans H (L ∘ g))          ≃⟨ II ⟩
        (Σ i' ꞉ (A → X) , Σ K ꞉ i ∼ i' ,
         Σ j' ꞉ (B → X) , Σ L ꞉ j ∼ j' ,
          Σ H' ꞉ (i' ∘ f ∼ j' ∘ g) ,
           ∼-trans (K ∘ f) H' ∼ ∼-trans H (L ∘ g))          ≃⟨ VII ⟩
        (Σ H' ꞉ (i ∘ f ∼ j ∘ g) , H' ∼ H)                   ≃⟨ XIV ⟩
        𝟙                                                   ■
     where
      I = ≃-comp Σ-assoc (Σ-cong (λ i' → Σ-assoc))
      II = Σ-cong (λ _ → ≃-comp (Σ-cong
           (λ _ → ≃-comp Σ-flip (Σ-cong (λ K → Σ-flip)))) Σ-flip)
      III = (Σ i' ꞉ (A → X) , i ∼ i')  ≃⟨ IV ⟩
            (Σ i' ꞉ (A → X) , i ＝ i') ≃⟨ V ⟩
            𝟙 {𝓤 ⊔ 𝓣}                  ■
       where
        IV = Σ-cong (λ - → ≃-sym (≃-funext fe i -))
        V = singleton-≃-𝟙 {_} {𝓤 ⊔ 𝓣} (singleton-types-are-singletons i)
      VI = ≃-comp {_} {_} {𝓤 ⊔ 𝓣}
            (Σ-cong (λ - → ≃-sym (≃-funext fe j -)))
             (singleton-≃-𝟙 (singleton-types-are-singletons j))
      VII = (Σ i' ꞉ (A → X) , Σ K ꞉ i ∼ i' ,
             Σ j' ꞉ (B → X) , Σ L ꞉ j ∼ j' ,
              Σ H' ꞉ (i' ∘ f ∼ j' ∘ g) ,
               ∼-trans (K ∘ f) H' ∼ ∼-trans H (L ∘ g))           ≃⟨ VIII ⟩
            (Σ (i' , K) ꞉ (Σ i' ꞉ (A → X) , i ∼ i') ,
             Σ j' ꞉ (B → X) , Σ L ꞉ j ∼ j' ,
              Σ H' ꞉ (i' ∘ f ∼ j' ∘ g) ,
               ∼-trans (K ∘ f) H' ∼ ∼-trans H (L ∘ g))           ≃⟨ IX ⟩
            (Σ j' ꞉ (B → X) , Σ L ꞉ j ∼ j' ,
             Σ H' ꞉ (i ∘ f ∼ j' ∘ g) ,
              ∼-trans (∼-refl {_} {_} {_} {_} {i} ∘ f) H'
               ∼ ∼-trans H (L ∘ g))                              ≃⟨ XI ⟩
            (Σ (j' , L) ꞉ (Σ j' ꞉ (B → X) , j ∼ j') ,
             Σ H' ꞉ (i ∘ f ∼ j' ∘ g) ,
              ∼-trans (∼-refl {_} {_} {_} {_} {i} ∘ f) H'
               ∼ ∼-trans H (L ∘ g))                              ≃⟨ XII ⟩
            (Σ H' ꞉ (i ∘ f ∼ j ∘ g) ,
             ∼-trans (∼-refl {_} {_} {_} {_} {i} ∘ f) H'
              ∼ ∼-trans H (∼-refl {_} {_} {_} {_} {j} ∘ g))      ≃⟨ XIII ⟩
            (Σ H' ꞉ (i ∘ f ∼ j ∘ g) , H' ∼ H)                    ■
       where
        VIII = ≃-sym Σ-assoc
        IX = prop-indexed-sum (equiv-to-prop III 𝟙-is-prop) (i , ∼-refl)
        XI = ≃-sym Σ-assoc
        XII = prop-indexed-sum (equiv-to-prop VI 𝟙-is-prop) (j , ∼-refl)
        XIII = Σ-cong (λ H' → Π-cong fe fe (λ c → ＝-cong (refl ∙ H' c)
                (∼-trans H (λ _ → refl) c) refl-left-neutral
                 (refl-right-neutral (H c) ⁻¹)))
      XIV = ≃-comp (Σ-cong (λ - → ≃-sym (≃-funext fe - H)))
             (singleton-≃-𝟙 (equiv-to-singleton (Σ-cong (λ - → ＝-flip))
              (singleton-types-are-singletons H)))

 cocone-identity-characterization : (X : 𝓣 ̇)
                                  → (u u' : cocone X)
                                  → (u ＝ u') ≃ (cocone-family X u u')
 cocone-identity-characterization X u u' =
  (canonical-map-from-identity-to-cocone-family X u u' ,
   Yoneda-Theorem-forth u (canonical-map-from-identity-to-cocone-family X u)
    (cocone-family-is-identity-system X u) u')

 inverse-cocone-map : (X : 𝓣 ̇)
                    → (u u' : cocone X)
                    → cocone-family X u u'
                    → u ＝ u'
 inverse-cocone-map X u u' =
  ⌜ (cocone-identity-characterization X u u') ⌝⁻¹

\end{code}

We also introduce the notion of a dependent cocone and characterize their
identity type.

\begin{code}

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : C → A) (g : C → B) (X : 𝓣  ̇)
          where

 dependent-cocone : (cocone f g X)
                  → (X → 𝓣' ̇)
                  → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣' ̇
 dependent-cocone (l , r , G) P =
  Σ i ꞉ ((a : A) → P (l a)) , Σ j ꞉ ((b : B) → P (r b)) ,
   ((λ - → transport P (G -) ((i ∘ f) -)) ∼ j ∘ g)

 dependent-cocone-vertical-map : (t : cocone f g X) (P : X → 𝓣' ̇)
                               → dependent-cocone t P
                               → (a : A) → P (cocone-vertical-map f g X t a)
 dependent-cocone-vertical-map t P (i , j , H) = i

 dependent-cocone-horizontal-map : (t : cocone f g X) (P : X → 𝓣' ̇)
                                 → dependent-cocone t P
                                 → (b : B) → P (cocone-horizontal-map f g X t b)
 dependent-cocone-horizontal-map t P (i , j , H) = j

 dependent-cocone-commuting-square
  : (t : cocone f g X) (P : X → 𝓣' ̇)
  → ((i , j , H) : dependent-cocone t P)
  → ((λ - → transport P (cocone-commuting-square f g X t -) ((i ∘ f) -))) ∼ j ∘ g
 dependent-cocone-commuting-square t P (i , j , H) = H

 dependent-cocone-family : (t : cocone f g X) (P : X → 𝓣' ̇)
                         → dependent-cocone t P → dependent-cocone t P
                         → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣' ̇
 dependent-cocone-family (l , r , G) P (i , j , H) (i' , j' , H')
  = Σ K ꞉ i ∼ i' , Σ L ꞉ j ∼ j' ,
     ∼-trans (λ - → ap (transport P (G -)) ((K ∘ f) -)) H' ∼ ∼-trans H (L ∘ g)

 canonical-map-from-identity-to-dependent-cocone-family
  : (t : cocone f g X) (P : X → 𝓣' ̇)
  → (u u' : dependent-cocone t P)
  → u ＝ u'
  → dependent-cocone-family t P u u'
 canonical-map-from-identity-to-dependent-cocone-family (l , r , G) P
  (i , j , H) .(i , j , H) refl
  = (∼-refl , ∼-refl , λ c → refl-left-neutral {_} {_} {_} {_} {H c})

 dependent-cocone-family-is-identity-system
  : (t : cocone f g X) (P : X → 𝓣' ̇)
  → (x : dependent-cocone t P)
  → is-contr (Σ y ꞉ dependent-cocone t P , dependent-cocone-family t P x y)
 dependent-cocone-family-is-identity-system {𝓣'} (l , r , G) P (i , j , H)
  = equiv-to-singleton e 𝟙-is-singleton
  where
   e : (Σ y ꞉ dependent-cocone (l , r , G) P ,
        dependent-cocone-family (l , r , G) P (i , j , H) y)
     ≃ 𝟙 {𝓤 ⊔ 𝓣'}
   e = (Σ y ꞉ dependent-cocone (l , r , G) P ,
        dependent-cocone-family (l , r , G) P (i , j , H) y)        ≃⟨ I ⟩
       (Σ i' ꞉ ((a : A) → P (l a)) , Σ j' ꞉ ((b : B) → P (r b)) ,
        Σ H' ꞉ ((λ - → transport P (G -) ((i' ∘ f) -)) ∼ j' ∘ g) ,
         Σ K ꞉ i ∼ i' , Σ L ꞉ j ∼ j' ,
          ∼-trans (λ - → ap (transport P (G -)) ((K ∘ f) -)) H'
           ∼ ∼-trans H (L ∘ g))                                     ≃⟨ II ⟩
       (Σ i' ꞉ ((a : A) → P (l a)) , Σ K ꞉ i ∼ i' ,
        Σ j' ꞉ ((b : B) → P (r b)) , Σ L ꞉ j ∼ j' ,
         Σ H' ꞉ ((λ - → transport P (G -) ((i' ∘ f) -)) ∼ j' ∘ g) ,
          ∼-trans (λ - → ap (transport P (G -)) ((K ∘ f) -)) H'
           ∼ ∼-trans H (L ∘ g))                                     ≃⟨ VII ⟩
       (Σ H' ꞉ ((λ - → transport P (G -) ((i ∘ f) -)) ∼ j ∘ g) ,
        H' ∼ H)                                                     ≃⟨ XIV ⟩
       𝟙                                                            ■
    where
     I = ≃-comp Σ-assoc (Σ-cong (λ i' → Σ-assoc))
     II = Σ-cong (λ _ → ≃-comp (Σ-cong
           (λ _ → ≃-comp Σ-flip (Σ-cong (λ K → Σ-flip)))) Σ-flip)
     III = (Σ i' ꞉ ((a : A) → P (l a)) , i ∼ i')  ≃⟨ IV ⟩
           (Σ i' ꞉ ((a : A) → P (l a)) , i ＝ i') ≃⟨ V ⟩
           𝟙 {𝓤 ⊔ 𝓣'}                             ■
      where
       IV = Σ-cong (λ - → ≃-sym (≃-funext fe i -))
       V = singleton-≃-𝟙 {_} {𝓤 ⊔ 𝓣'} (singleton-types-are-singletons i)
     VI = ≃-comp {_} {_} {𝓤 ⊔ 𝓣'}
           (Σ-cong (λ - → ≃-sym (≃-funext fe j -)))
            (singleton-≃-𝟙 (singleton-types-are-singletons j))
     VII = (Σ i' ꞉ ((a : A) → P (l a)) , Σ K ꞉ i ∼ i' ,
            Σ j' ꞉ ((b : B) → P (r b)) , Σ L ꞉ j ∼ j' ,
             Σ H' ꞉ ((λ - → transport P (G -) ((i' ∘ f) -)) ∼ j' ∘ g) ,
              ∼-trans (λ - → ap (transport P (G -)) ((K ∘ f) -)) H'
               ∼ ∼-trans H (L ∘ g))                             ≃⟨ VIII ⟩
           (Σ (i' , K) ꞉ (Σ i' ꞉ ((a : A) → P (l a)) , i ∼ i') ,
            Σ j' ꞉ ((b : B) → P (r b)) , Σ L ꞉ j ∼ j' ,
             Σ H' ꞉ ((λ - → transport P (G -) ((i' ∘ f) -)) ∼ j' ∘ g) ,
              ∼-trans (λ - → ap (transport P (G -)) ((K ∘ f) -)) H'
               ∼ ∼-trans H (L ∘ g))                             ≃⟨ IX ⟩
           (Σ j' ꞉ ((b : B) → P (r b)) , Σ L ꞉ j ∼ j' ,
            Σ H' ꞉ ((λ - → transport P (G -) ((i ∘ f) -)) ∼ j' ∘ g) ,
             ∼-trans (λ - → ap (transport P (G -)) refl) H'
              ∼ ∼-trans H (L ∘ g))                              ≃⟨ XI ⟩
           (Σ (j' , L) ꞉ (Σ j' ꞉ ((b : B) → P (r b)) , j ∼ j') ,
            Σ H' ꞉ ((λ - → transport P (G -) ((i ∘ f) -)) ∼ j' ∘ g) ,
             ∼-trans (λ - → ap (transport P (G -)) refl) H'
              ∼ ∼-trans H (L ∘ g))                              ≃⟨ XII ⟩
           (Σ H' ꞉ ((λ - → transport P (G -) ((i ∘ f) -)) ∼ j ∘ g) ,
            ∼-trans (λ - → ap (transport P (G -)) refl) H'
             ∼ ∼-trans H (∼-refl {_} {_} {_} {_} {j} ∘ g))      ≃⟨ XIII ⟩
           (Σ H' ꞉ ((λ - → transport P (G -) ((i ∘ f) -)) ∼ j ∘ g) , H' ∼ H)
                                                                ■
      where
       VIII = ≃-sym Σ-assoc
       IX = prop-indexed-sum (equiv-to-prop III 𝟙-is-prop) (i , ∼-refl)
       XI = ≃-sym Σ-assoc
       XII = prop-indexed-sum (equiv-to-prop VI 𝟙-is-prop) (j , ∼-refl)
       XIII = Σ-cong (λ H' → Π-cong fe fe (λ c → ＝-cong (refl ∙ H' c)
               (∼-trans H (λ _ → refl) c) refl-left-neutral
                (refl-right-neutral (H c) ⁻¹))) 
     XIV = ≃-comp (Σ-cong (λ - → ≃-sym (≃-funext fe - H)))
            (singleton-≃-𝟙 (equiv-to-singleton (Σ-cong (λ - → ＝-flip))
             (singleton-types-are-singletons H)))

 dependent-cocone-identity-characterization
  : (t : cocone f g X) (P : X → 𝓣' ̇)
  → (u u' : dependent-cocone t P)
  → (u ＝ u') ≃ (dependent-cocone-family t P u u')
 dependent-cocone-identity-characterization t P u u' =
  (canonical-map-from-identity-to-dependent-cocone-family t P u u' ,
   Yoneda-Theorem-forth u
    (canonical-map-from-identity-to-dependent-cocone-family t P u)
     (dependent-cocone-family-is-identity-system t P u) u')

 inverse-dependent-cocone-map : (t : cocone f g X) (P : X → 𝓣'  ̇)
                              → (u u' : dependent-cocone t P)
                              → dependent-cocone-family t P u u'
                              → u ＝ u'
 inverse-dependent-cocone-map t P u u' =
  ⌜ (dependent-cocone-identity-characterization t P u u') ⌝⁻¹
                 
\end{code}

We now define the type of morphisms between (non-dependent) cocones.
We *should* give a characterization of their identity type but fortunately we
only need a map in the trivial direction for the purposes of defining pushouts.

\begin{code}

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : C → A) (g : C → B) (X : 𝓣 ̇) (P : 𝓣' ̇)
          where

 cocone-morphism : cocone f g P
                 → cocone f g X
                 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓣' ̇
 cocone-morphism (i , j , H) s'
  = Σ u ꞉ (P → X) , cocone-family f g X (u ∘ i , u ∘ j , ∼-ap-∘ u H) s'

 cocone-morphism-map : (s : cocone f g P)
                     → (s' : cocone f g X)
                     → cocone-morphism s s'
                     → P → X
 cocone-morphism-map s s' (u , _) = u

 cocone-morphism-left-coherence
  : ((i , j , H) : cocone f g P)
  → ((i' , j' , H') : cocone f g X)
  → ((u , K , L , M) : cocone-morphism (i , j , H) (i' , j' , H'))
  → u ∘ i ∼ i'
 cocone-morphism-left-coherence s s' (_ , K , _) = K

 cocone-morphism-right-coherence
  : ((i , j , H) : cocone f g P)
  → ((i' , j' , H') : cocone f g X)
  → ((u , K , L , M) : cocone-morphism (i , j , H) (i' , j' , H'))
  → u ∘ j ∼ j'
 cocone-morphism-right-coherence s s' (_ , _ , L , _) = L

 cocone-morphism-homotopy-coherence
  : ((i , j , H) : cocone f g P)
  → ((i' , j' , H') : cocone f g X)
  → ((u , K , L , M) : cocone-morphism (i , j , H) (i' , j' , H'))
  → ∼-trans (K ∘ f) H' ∼ ∼-trans (∼-ap-∘ u H) (L ∘ g)
 cocone-morphism-homotopy-coherence s s' (_ , _ , _ , M) = M

 Alternative-Path : (s : cocone f g P)
                  → (s' : cocone f g X)
                  → cocone-morphism s s'
                  → cocone-morphism s s'
                  → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓣' ̇
 Alternative-Path (i , j , H) (i' , j' , H') (u , K , L , M) (u' , K' , L' , M')
  = (θ : (x : P) → u x ＝ u' x)
    (ϕl : (a : A) → θ (i a) ∙ K' a ＝ K a)
    (ϕr : (b : B) → θ (j b) ∙ L' b ＝ L b)
    (c : C)
  → K (f c) ∙ H' c ＝ ap u (H c) ∙ L (g c)
 
 alt-path : (s : cocone f g P)
          → (s' : cocone f g X)
          → (m : cocone-morphism s s')
          → (m' : cocone-morphism s s')
          → Alternative-Path s s' m m'
 alt-path (i , j , H) (i' , j' , H') (u , K , L , M) (u' , K' , L' , M')
  θ ϕl ϕr c = K (f c) ∙ H' c                         ＝⟨ I ⟩
              (θ (i (f c)) ∙ K' (f c)) ∙ H' c        ＝⟨ II ⟩
              θ (i (f c)) ∙ (K' (f c) ∙ H' c)        ＝⟨ III ⟩
              θ (i (f c)) ∙ (ap u' (H c) ∙ L' (g c)) ＝⟨ IV ⟩
              (θ (i (f c)) ∙ ap u' (H c)) ∙ L' (g c) ＝⟨ V ⟩
              (ap u (H c) ∙ θ (j (g c))) ∙ L' (g c)  ＝⟨ VI ⟩
              ap u (H c) ∙ (θ (j (g c)) ∙ L' (g c))  ＝⟨ VII ⟩
              ap u (H c) ∙ L (g c)                   ∎
  where
   I = ap (_∙ H' c) (ϕl (f c) ⁻¹)
   II = ∙assoc (θ (i (f c))) (K' (f c)) (H' c)
   III = ap (θ (i (f c)) ∙_) (M' c)
   IV = ∙assoc (θ (i (f c))) (ap u' (H c)) (L' (g c)) ⁻¹
   V = ap (_∙ L' (g c)) (homotopies-are-natural u u' θ {_} {_} {H c})
   VI = ∙assoc (ap u (H c)) (θ (j (g c))) (L' (g c))
   VII = ap (ap u (H c) ∙_) (ϕr (g c))

 cocone-morphism-family : (s : cocone f g P)
                        → (s' : cocone f g X)
                        → cocone-morphism s s'
                        → cocone-morphism s s'
                        → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ⊔ 𝓣'  ̇
 cocone-morphism-family (i , j , H) (i' , j' , H')
  (u , K , L , M) (u' , K' , L' , M')
  = Σ θ ꞉ ((x : P) → u x ＝ u' x) , Σ ϕl ꞉ ((a : A) → θ (i a) ∙ K' a ＝ K a) ,
     Σ ϕr ꞉ ((b : B) → θ (j b) ∙ L' b ＝ L b) ,
      ((c : C)
       → M c ＝ alt-path (i , j , H) (i' , j' , H') (u , K , L , M)
                 (u' , K' , L' , M') θ ϕl ϕr c)

 cocone-morphism-family-homotopy
  : (s : cocone f g P)
  → (s' : cocone f g X)
  → ((u , K , L , M) : cocone-morphism s s')
  → ((u' , K' , L' , M') : cocone-morphism s s')
  → cocone-morphism-family s s' (u , K , L , M) (u' , K' , L' , M')
  → u ∼ u'
 cocone-morphism-family-homotopy s s' m m' (θ , _) = θ

 cocone-morphism-family-left-coherence
  : ((i , j , H) : cocone f g P)
  → ((i' , j' , H') : cocone f g X)
  → ((u , K , L , M) : cocone-morphism (i , j , H) (i' , j' , H'))
  → ((u' , K' , L' , M') : cocone-morphism (i , j , H) (i' , j' , H'))
  → ((θ , ϕl , ϕr , γ) : cocone-morphism-family (i , j , H) (i' , j' , H')
                          (u , K , L , M) (u' , K' , L' , M'))
  → (a : A)
  → θ (i a) ∙ K' a ＝ K a
 cocone-morphism-family-left-coherence s s' m m' (_ , ϕl , _) = ϕl

 cocone-morphism-family-right-coherence
  : ((i , j , H) : cocone f g P)
  → ((i' , j' , H') : cocone f g X)
  → ((u , K , L , M) : cocone-morphism (i , j , H) (i' , j' , H'))
  → ((u' , K' , L' , M') : cocone-morphism (i , j , H) (i' , j' , H'))
  → ((θ , ϕl , ϕr , γ) : cocone-morphism-family (i , j , H) (i' , j' , H')
                          (u , K , L , M) (u' , K' , L' , M'))
  → (b : B)
  → θ (j b) ∙ L' b ＝ L b
 cocone-morphism-family-right-coherence s s' m m' (_ , _ , ϕr , _) = ϕr

 cocone-morphism-family-homotopy-coherence
  : ((i , j , H) : cocone f g P)
  → ((i' , j' , H') : cocone f g X)
  → ((u , K , L , M) : cocone-morphism (i , j , H) (i' , j' , H'))
  → ((u' , K' , L' , M') : cocone-morphism (i , j , H) (i' , j' , H'))
  → ((θ , ϕl , ϕr , γ) : cocone-morphism-family (i , j , H) (i' , j' , H')
                          (u , K , L , M) (u' , K' , L' , M'))
  → (c : C)
  → M c ＝ alt-path (i , j , H) (i' , j' , H') (u , K , L , M) (u' , K' , L' , M')
            θ ϕl ϕr c
 cocone-morphism-family-homotopy-coherence s s' m m' (_ , _ , _ , γ) = γ

 canonical-map-to-cocone-morphism-family
  : (s : cocone f g P)
  → (s' : cocone f g X)
  → (m : cocone-morphism s s')
  → (m' : cocone-morphism s s')
  → m ＝ m'
  → cocone-morphism-family s s' m m'
 canonical-map-to-cocone-morphism-family (i , j , H) (i' , j' , H')
  (u , K , L , M) .(u , K , L , M) refl
  = (∼-refl , (λ - → refl-left-neutral) , (λ - → refl-left-neutral) , II)
  where
   I : {Y : 𝓤'  ̇} {Z : 𝓥'  ̇} {x y : Y} {z' z : Z} (f' : Y → Z)
       (p : x ＝ y) (q : f' y ＝ z) (p' : f' x ＝ z') (q' : z' ＝ z)
       (α : p' ∙ q' ＝ (ap f' p) ∙ q)
     → α ＝ ap (_∙ q') (refl-left-neutral {_} {_} {_} {_} {p'} ⁻¹)
            ∙ (∙assoc refl p' q'
            ∙ (ap (refl ∙_) α
            ∙ (∙assoc refl (ap f' p) q ⁻¹
            ∙ (ap (_∙ q) (homotopies-are-natural f' f' ∼-refl {_} {_} {p})
            ∙ (∙assoc (ap f' p) (refl {_} {_} {f' y}) q
            ∙ ap (ap f' p ∙_) (refl-left-neutral {_} {_} {_} {_} {q}))))))
   I f' refl refl p' refl α = IV
    where
     Notice : p' ＝ refl
     Notice = α
     III : {Y : 𝓤'  ̇} {y : Y} (p : y ＝ y) (α : p ＝ refl)
         → α ＝ ap (_∙ refl) (refl-left-neutral ⁻¹)
               ∙ (∙assoc refl p refl ∙ ap (refl ∙_) α)
     III p refl = refl
     IV : α ＝ ap (_∙ refl) (refl-left-neutral ⁻¹)
               ∙ (∙assoc refl p' refl ∙ ap (refl ∙_) α)
     IV = III p' α
   II : (c : C)
      →  M c ＝ alt-path (i , j , H) (i' , j' , H') (u , K , L , M)
                 (u , K , L , M) ∼-refl (λ - → refl-left-neutral)
                  (λ - → refl-left-neutral) c
   II c = I u (H c) (L (g c)) (K (f c)) (H' c) (M c)


\end{code}

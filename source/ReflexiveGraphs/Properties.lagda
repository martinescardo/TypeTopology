Ian Ray. 7th November 2025.

Internal code review and addition by Carlo Angiuli 18th November 2025.

Minor changes and merged into TypeToplogy in June 2026.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import UF.FunExt

module ReflexiveGraphs.Properties (fe : Fun-Ext) where

open import MLTT.Spartan
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.PropIndexedPiSigma
open import ReflexiveGraphs.Constructions
open import ReflexiveGraphs.UnivalentClosureProperties
open import ReflexiveGraphs.Displayed
open import ReflexiveGraphs.DisplayedUnivalent
open import ReflexiveGraphs.Lenses
open import ReflexiveGraphs.Type
open import ReflexiveGraphs.UnbiasedLenses
open import ReflexiveGraphs.Univalent

private
 fe' : FunExt
 fe' 𝓤 𝓥 = fe {𝓤} {𝓥}

\end{code}

In this file we observe that univalence of (displayed) reflexive graphs and the
structure of a lens on a reflexive graph and associated family of reflexive
graphs are properties rather than data. For this we globally assume function
extensionality, and for the latter we assume univalence of the reflexive graphs
in question.

We show that univalence for (displayed) reflexive graphs is a proposition.

\begin{code}

refl-graph-univalence-is-a-property : (𝓐 : Refl-Graph 𝓤 𝓥)
                                    → is-prop (is-univalent-refl-graph 𝓐)
refl-graph-univalence-is-a-property 𝓐
 = Π-is-prop fe (λ - → being-prop-is-prop fe)

displayed-refl-graph-univalence-is-a-property
 : (𝓐 : Refl-Graph 𝓤 𝓥) (𝓑 : Displayed-Refl-Graph 𝓤' 𝓥' 𝓐)
 → is-prop (is-displayed-univalent-refl-graph 𝓐 𝓑)
displayed-refl-graph-univalence-is-a-property 𝓐 𝓑
 = Π-is-prop fe (λ - → refl-graph-univalence-is-a-property ([ 𝓑 ] -))

\end{code}

We show that oplax coravariant lens structure is contracible and in fact a
property.

NOTE: We inline the definitional isomorphism between the record type collecting
the lens structure and the corresponding sigma type. We then proceed with
equivalence reasoning by massaging this sigma type into the form of something
contractible.

\begin{code}

module _ (𝓤' 𝓥' : Universe)
         (𝓐 : Refl-Graph 𝓤 𝓥)
         (𝓑 : ⟨ 𝓐 ⟩ → Refl-Graph 𝓤' 𝓥')
       where

 oplax-lens-structure-is-contr
  : is-univalent-refl-graph 𝓐
  → ((x : ⟨ 𝓐 ⟩) → is-univalent-refl-graph (𝓑 x))
  → is-contr (oplax-covariant-lens-structure 𝓤' 𝓥' 𝓐 𝓑)
 oplax-lens-structure-is-contr is-ua-𝓐 is-ua-𝓑 =
  equiv-to-singleton I
   (Π-is-singleton fe (λ x → equiv-to-singleton (II x) (III x)))
  where
   open oplax-covariant-lens-structure 
   I' : oplax-covariant-lens-structure 𝓤' 𝓥' 𝓐 𝓑 ≃
        (Σ ϕ ꞉ ((x y : ⟨ 𝓐 ⟩) (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 x ⟩ → ⟨ 𝓑 y ⟩)
          , ((x : ⟨ 𝓐 ⟩) → (u : ⟨ 𝓑 x ⟩) → ϕ x x (≈-refl 𝓐 x) u ≈⟨ 𝓑 x ⟩ u))
   I' = qinveq (λ 𝓛 → ((λ x y → push 𝓛) , λ x → push-refl 𝓛))
         ((λ (ϕ , r) → record {push = λ {x y} → ϕ x y; push-refl = λ {x} → r x})
          , ∼-refl , ∼-refl)
   I : oplax-covariant-lens-structure 𝓤' 𝓥' 𝓐 𝓑
     ≃ ((x : ⟨ 𝓐 ⟩)
        → Σ ϕ ꞉ ((y : ⟨ 𝓐 ⟩) (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 x ⟩ → ⟨ 𝓑 y ⟩)
          , ((u : ⟨ 𝓑 x ⟩) → ϕ x (≈-refl 𝓐 x) u ≈⟨ 𝓑 x ⟩ u))
   I = ≃-comp I' (≃-sym ΠΣ-distr-≃)
   II : (x : ⟨ 𝓐 ⟩) → _ ≃ (cofan (⟨ 𝓑 x ⟩ ➙ 𝓑 x) id)
   II x = (Σ ϕ ꞉ ((y : ⟨ 𝓐 ⟩) (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 x ⟩ → ⟨ 𝓑 y ⟩) ,
            ((u : ⟨ 𝓑 x ⟩) → ϕ x (≈-refl 𝓐 x) u ≈⟨ 𝓑 x ⟩ u))
           ≃⟨ Σ-change-of-variable-≃ _ (≃-sym (curry-uncurry fe')) ⟩
          (Σ ϕ ꞉ (((y , p) : fan 𝓐 x) → ⟨ 𝓑 x ⟩ → ⟨ 𝓑 y ⟩) ,
            ((u : ⟨ 𝓑 x ⟩) → ϕ (x , (≈-refl 𝓐 x)) u ≈⟨ 𝓑 x ⟩ u))
           ≃⟨ Σ-change-of-variable-≃ _
               (prop-indexed-product (x , ≈-refl 𝓐 x) fe (is-ua-𝓐 x)) ⟩
          (Σ ϕ ꞉ (⟨ 𝓑 x ⟩ → ⟨ 𝓑 x ⟩) , ((u : ⟨ 𝓑 x ⟩) → ϕ u ≈⟨ 𝓑 x ⟩ u))
           ≃⟨by-definition⟩
          cofan (⟨ 𝓑 x ⟩ ➙ 𝓑 x) id ■
   III : (x : ⟨ 𝓐 ⟩) → is-contr (cofan (⟨ 𝓑 x ⟩ ➙ 𝓑 x) id)
   III x = prop-fan-to-contr-cofan (⟨ 𝓑 x ⟩ ➙ 𝓑 x)
            (univalence-closed-under-cotensor fe _ (𝓑 x) (is-ua-𝓑 x))
            id

 oplax-lens-structure-is-a-property
  : is-univalent-refl-graph 𝓐
  → ((x : ⟨ 𝓐 ⟩) → is-univalent-refl-graph (𝓑 x))
  → is-prop (oplax-covariant-lens-structure 𝓤' 𝓥' 𝓐 𝓑)
 oplax-lens-structure-is-a-property is-ua-𝓐 is-ua-𝓑
  = singletons-are-props (oplax-lens-structure-is-contr is-ua-𝓐 is-ua-𝓑)

\end{code}

Similarly, a lax covariant lens structure is contractible and thus a property.

\begin{code}

 lax-lens-structure-is-contr
  : is-univalent-refl-graph 𝓐
  → ((x : ⟨ 𝓐 ⟩) → is-univalent-refl-graph (𝓑 x))
  → is-contr (lax-contravariant-lens-structure 𝓤' 𝓥' 𝓐 𝓑)
 lax-lens-structure-is-contr is-ua-𝓐 is-ua-𝓑 =
  equiv-to-singleton I
   (Π-is-singleton fe (λ x → equiv-to-singleton (III x) (II x)))
  where
   open lax-contravariant-lens-structure 
   I : lax-contravariant-lens-structure 𝓤' 𝓥' 𝓐 𝓑
     ≃ ((x : ⟨ 𝓐 ⟩)
        → Σ ϕ ꞉ ((y : ⟨ 𝓐 ⟩) (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 y ⟩ → ⟨ 𝓑 x ⟩)
          , ((u : ⟨ 𝓑 x ⟩) → u ≈⟨ 𝓑 x ⟩ ϕ x (≈-refl 𝓐 x) u))
   I = qinveq (λ 𝓛 x → ((λ _ → pull 𝓛) , pull-refl 𝓛))
        ((λ f → record {pull = λ {x y} → (pr₁ (f x)) y
                        ; pull-refl = λ {x} → pr₂ (f x)})
         , ∼-refl , ∼-refl)
   II : (x : ⟨ 𝓐 ⟩) → is-contr (fan (⟨ 𝓑 x ⟩ ➙ 𝓑 x) id)
   II x = prop-fan-to-contr (⟨ 𝓑 x ⟩ ➙ 𝓑 x)
           (univalence-closed-under-cotensor fe _ (𝓑 x) (is-ua-𝓑 x)) id
   III : (x : ⟨ 𝓐 ⟩) → _ ≃ fan (⟨ 𝓑 x ⟩ ➙ 𝓑 x) id
   III x = (Σ ϕ ꞉ ((y : ⟨ 𝓐 ⟩) (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 y ⟩ → ⟨ 𝓑 x ⟩) ,
             ((u : ⟨ 𝓑 x ⟩) → u ≈⟨ 𝓑 x ⟩ ϕ x (≈-refl 𝓐 x) u))
             ≃⟨ Σ-change-of-variable-≃ _ (≃-sym (curry-uncurry fe')) ⟩
           (Σ ϕ ꞉ (((y , p) : fan 𝓐 x) → ⟨ 𝓑 y ⟩ → ⟨ 𝓑 x ⟩) ,
             ((u : ⟨ 𝓑 x ⟩) → u ≈⟨ 𝓑 x ⟩ ϕ (x , (≈-refl 𝓐 x)) u))
             ≃⟨ Σ-change-of-variable-≃ _
                 (prop-indexed-product (x , ≈-refl 𝓐 x) fe (is-ua-𝓐 x)) ⟩
           (Σ ϕ ꞉ (⟨ 𝓑 x ⟩ → ⟨ 𝓑 x ⟩) , ((u : ⟨ 𝓑 x ⟩) → u ≈⟨ 𝓑 x ⟩ ϕ u))
             ≃⟨by-definition⟩
           fan (⟨ 𝓑 x ⟩ ➙ 𝓑 x) id ■

 lax-lens-structure-is-a-property
  : is-univalent-refl-graph 𝓐
  → ((x : ⟨ 𝓐 ⟩) → is-univalent-refl-graph (𝓑 x))
  → is-prop (lax-contravariant-lens-structure 𝓤' 𝓥' 𝓐 𝓑)
 lax-lens-structure-is-a-property is-ua-𝓐 is-ua-𝓑
  = singletons-are-props (lax-lens-structure-is-contr is-ua-𝓐 is-ua-𝓑)

\end{code}

Finally, an unbiased lens structure is contractible and thus a property.

\begin{code}

module _ (𝓤' 𝓥' : Universe)
         (𝓐 : Refl-Graph 𝓤 𝓥)
         (𝓑 : {x y : ⟨ 𝓐 ⟩} → (x ≈⟨ 𝓐 ⟩ y) → Refl-Graph 𝓤' 𝓥')
       where

 unbiased-lens-structure-is-contr
  : is-univalent-refl-graph 𝓐
  → ((x y : ⟨ 𝓐 ⟩) (p : x ≈⟨ 𝓐 ⟩ y) → is-univalent-refl-graph (𝓑 p))
  → is-contr (unbiased-lens-structure 𝓤' 𝓥' 𝓐 𝓑)
 unbiased-lens-structure-is-contr is-ua-𝓐 is-ua-𝓑
  = equiv-to-singleton I
     (Π-is-singleton fe (λ x → equiv-to-singleton (III x) (II x id)))
  where
   open unbiased-lens-structure
   I : unbiased-lens-structure 𝓤' 𝓥' 𝓐 𝓑
     ≃ ((x : ⟨ 𝓐 ⟩)
     → Σ ϕ ꞉ ((y : ⟨ 𝓐 ⟩) (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 (≈-refl 𝓐 x) ⟩ → ⟨ 𝓑 p ⟩)
     , Σ ψ ꞉ ((y : ⟨ 𝓐 ⟩) (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 (≈-refl 𝓐 y) ⟩ → ⟨ 𝓑 p ⟩)
     , ((u : ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
         → ϕ x (≈-refl 𝓐 x) u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ψ x (≈-refl 𝓐 x) u)
     × ((u : ⟨ 𝓑 (≈-refl 𝓐 x) ⟩) → u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ψ x (≈-refl 𝓐 x) u))
   I = qinveq
        (λ 𝓛 x → ((λ _ → lext 𝓛) , (λ _ → rext 𝓛) , ext-refl 𝓛 , rext-refl 𝓛))
        ((λ f → record {lext = λ {x y} → (pr₁ (f x)) y
                        ; rext = λ {x y} → (pr₁ (pr₂ (f x))) y
                        ; ext-refl = λ {x} → pr₁ (pr₂ (pr₂ (f x)))
                        ; rext-refl = λ {x} → pr₂ (pr₂ (pr₂ (f x)))})
         , ∼-refl , ∼-refl)
   II : (x : ⟨ 𝓐 ⟩) (ϕ : ⟨ ⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ➙ 𝓑 (≈-refl 𝓐 x) ⟩)
       → is-contr (fan (⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ➙ 𝓑 (≈-refl 𝓐 x)) ϕ)
   II x ϕ = prop-fan-to-contr (⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ➙ 𝓑 (≈-refl 𝓐 x))
              (univalence-closed-under-cotensor fe _ (𝓑 (≈-refl 𝓐 x))
               (is-ua-𝓑 x x (≈-refl 𝓐 x))) ϕ
   III : (x : ⟨ 𝓐 ⟩) → _ ≃ fan (⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ➙ 𝓑 (≈-refl 𝓐 x)) id
   III x =
    (Σ ϕ ꞉ ((y : ⟨ 𝓐 ⟩) (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 (≈-refl 𝓐 x) ⟩ → ⟨ 𝓑 p ⟩)
    , Σ ψ ꞉ ((y : ⟨ 𝓐 ⟩) (p : x ≈⟨ 𝓐 ⟩ y) → ⟨ 𝓑 (≈-refl 𝓐 y) ⟩ → ⟨ 𝓑 p ⟩)
    , ((u : ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
        → ϕ x (≈-refl 𝓐 x) u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ψ x (≈-refl 𝓐 x) u)
    × ((u : ⟨ 𝓑 (≈-refl 𝓐 x) ⟩) → u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ψ x (≈-refl 𝓐 x) u))
       ≃⟨ Σ-bicong _ _ (≃-sym (curry-uncurry fe'))
           (λ _ → Σ-change-of-variable-≃ _ (≃-sym (curry-uncurry fe'))) ⟩
    (Σ ϕ ꞉ (((y , p) : fan 𝓐 x) → ⟨ 𝓑 (≈-refl 𝓐 x) ⟩ → ⟨ 𝓑 p ⟩)
    , Σ ψ ꞉ (((y , p) : fan 𝓐 x) → ⟨ 𝓑 (≈-refl 𝓐 y) ⟩ → ⟨ 𝓑 p ⟩)
    , ((u : ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
     → ϕ (x , (≈-refl 𝓐 x)) u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ψ (x , (≈-refl 𝓐 x)) u)
    × ((u : ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
     → u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ψ (x , (≈-refl 𝓐 x)) u))
       ≃⟨ Σ-bicong _ _ (prop-indexed-product (x , ≈-refl 𝓐 x) fe (is-ua-𝓐 x))
          (λ _ → Σ-change-of-variable-≃ _
           (prop-indexed-product (x , ≈-refl 𝓐 x) fe (is-ua-𝓐 x))) ⟩
    (Σ ϕ ꞉ (⟨ 𝓑 (≈-refl 𝓐 x) ⟩ → ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
    , Σ ψ ꞉ (⟨ 𝓑 (≈-refl 𝓐 x) ⟩ → ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
    , ((u : ⟨ 𝓑 (≈-refl 𝓐 x) ⟩) → ϕ u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ψ u)
    × ((u : ⟨ 𝓑 (≈-refl 𝓐 x) ⟩) → u ≈⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ψ u))
       ≃⟨by-definition⟩
    (Σ ϕ ꞉ (⟨ 𝓑 (≈-refl 𝓐 x) ⟩ → ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
    , Σ ψ ꞉ (⟨ 𝓑 (≈-refl 𝓐 x) ⟩ → ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
    , (ϕ ≈⟨ ⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ➙ 𝓑 (≈-refl 𝓐 x) ⟩ ψ)
    × (id ≈⟨ ⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ➙ 𝓑 (≈-refl 𝓐 x) ⟩ ψ))
       ≃⟨ Σ-cong (λ _ → ≃-sym Σ-assoc) ⟩
    (Σ ϕ ꞉ (⟨ 𝓑 (≈-refl 𝓐 x) ⟩ → ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
    , Σ (ψ , _) ꞉ fan (⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ➙ 𝓑 (≈-refl 𝓐 x)) ϕ
    , (id ≈⟨ ⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ➙ 𝓑 (≈-refl 𝓐 x) ⟩ ψ))
       ≃⟨ Σ-cong (λ - → prop-indexed-sum (center (II x -))
           (singletons-are-props (II x -))) ⟩
    ((Σ ϕ ꞉ (⟨ 𝓑 (≈-refl 𝓐 x) ⟩ → ⟨ 𝓑 (≈-refl 𝓐 x) ⟩)
    , (id ≈⟨ ⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ➙ 𝓑 (≈-refl 𝓐 x) ⟩ ϕ)))
       ≃⟨by-definition⟩
    fan (⟨ 𝓑 (≈-refl 𝓐 x) ⟩ ➙ 𝓑 (≈-refl 𝓐 x)) id ■

 unbiased-lens-structure-is-a-property
  : is-univalent-refl-graph 𝓐
  → ((x y : ⟨ 𝓐 ⟩) (p : x ≈⟨ 𝓐 ⟩ y) → is-univalent-refl-graph (𝓑 p))
  → is-prop (unbiased-lens-structure 𝓤' 𝓥' 𝓐 𝓑)
 unbiased-lens-structure-is-a-property is-ua-𝓐 is-ua-𝓑
  = singletons-are-props
     (unbiased-lens-structure-is-contr is-ua-𝓐 is-ua-𝓑)

\end{code}

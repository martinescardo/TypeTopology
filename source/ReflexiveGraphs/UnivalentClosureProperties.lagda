Ian Ray. 28th August 2025.

Minor changes and merged into TypeToplogy in March 2026.

We observe the closure properties of univalent (displayed) reflexive graphs
(see index for references to Sterling, Buchholtz, etc.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.UnivalentClosureProperties where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.Powerset-MultiUniverse
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties
open import ReflexiveGraphs.Constructions
open import ReflexiveGraphs.Displayed
open import ReflexiveGraphs.DisplayedUnivalent
open import ReflexiveGraphs.Type
open import ReflexiveGraphs.Univalent

\end{code}

We record closure properties of univalent (displayed) reflexive graphs.

\begin{code}

univalence-closed-under-opposite : (𝓐 : Refl-Graph 𝓤 𝓥)
                                 → is-univalent-refl-graph 𝓐
                                 → is-univalent-refl-graph (𝓐 ᵒᵖ)
univalence-closed-under-opposite 𝓐 𝓐-ua = prop-fan-to-cofan 𝓐 𝓐-ua

univalence-closed-under-opposite' : (𝓐 : Refl-Graph 𝓤 𝓥)
                                  → is-univalent-refl-graph (𝓐 ᵒᵖ)
                                  → is-univalent-refl-graph 𝓐
univalence-closed-under-opposite' 𝓐 = univalence-closed-under-opposite (𝓐 ᵒᵖ)

univalence-closed-under-total
 : (𝓐 : Refl-Graph 𝓤 𝓥) (𝓑 : Displayed-Refl-Graph 𝓣 𝓦 𝓐)
 → is-univalent-refl-graph 𝓐
 → is-displayed-univalent-refl-graph 𝓐 𝓑
 → is-univalent-refl-graph (𝓐 ﹐ 𝓑)
univalence-closed-under-total 𝓐 𝓑 𝓐-ua 𝓑-ua  = III 
 where
  I : {x x' x'' : ⟨ 𝓐 ⟩} {p' : x ≈⟨ 𝓐 ⟩ x'} {p'' : x ≈⟨ 𝓐 ⟩ x''}
      {y : ⟪ 𝓑 ⟫ x} {y' : ⟪ 𝓑 ⟫ x'} {y'' : ⟪ 𝓑 ⟫ x''}
      {q' : y ≈⟨ 𝓑 ⸴ p' ⟩ y'} {q'' : y ≈⟨ 𝓑 ⸴ p'' ⟩ y''}
    → ((x' , p') , y' , q') ＝ ((x'' , p'') , y'' , q'')
    → ((x' , y') , p' , q') ＝ ((x'' , y'') , p'' , q'')
  I refl = refl
  II : {x x' x'' : ⟨ 𝓐 ⟩} {p' : x ≈⟨ 𝓐 ⟩ x'} {p'' : x ≈⟨ 𝓐 ⟩ x''}
       {y : ⟪ 𝓑 ⟫ x} {y' : ⟪ 𝓑 ⟫ x'} {y'' : ⟪ 𝓑 ⟫ x''}
       {q' : y ≈⟨ 𝓑 ⸴ p' ⟩ y'} {q'' : y ≈⟨ 𝓑 ⸴ p'' ⟩ y''}
     → (α : (x' , p') ＝ (x'' , p''))
     → (β : (x , ≈-refl 𝓐 x) ＝ (x' , p'))
     → transport (λ (a , b) → Σ v ꞉ ⟪ 𝓑 ⟫ a , y ≈⟨ 𝓑 ⸴ b ⟩ v) α (y' , q')
      ＝ (y'' , q'')
  II {x} {_} {_} {_} {_} {y} {y'} {y''} {q'} {q''} refl refl
   = 𝓑-ua x y (y' , q') (y'' , q'')
  III : (u : ⟨ 𝓐 ﹐ 𝓑 ⟩) → is-prop (fan (𝓐 ﹐ 𝓑) u)
  III (x , y) ((x' , y') , (p' , q')) ((x'' , y'') , (p'' , q''))
   = I (to-Σ-＝ (𝓐-ua x (x' , p') (x'' , p'') ,
      II (𝓐-ua x (x' , p') (x'' , p'')) (𝓐-ua x (x , ≈-refl 𝓐 x) (x' , p'))))

univalence-closed-under-constant
 : (𝓐 : Refl-Graph 𝓤 𝓥)
 → (𝓑 : Refl-Graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓑 
 → is-displayed-univalent-refl-graph 𝓐 (𝓐 * 𝓑)
univalence-closed-under-constant 𝓐 𝓑 ua-𝓑 x = ua-𝓑
    
univalence-closed-under-binary-product
 : (𝓐 : Refl-Graph 𝓤 𝓥) (𝓐' : Refl-Graph 𝓤' 𝓥')
 → is-univalent-refl-graph 𝓐
 → is-univalent-refl-graph 𝓐'
 → is-univalent-refl-graph (𝓐 ⊗ 𝓐')
univalence-closed-under-binary-product 𝓐 𝓐' 𝓐-ua 𝓐'-ua
 = univalence-closed-under-total 𝓐 (𝓐 * 𝓐') 𝓐-ua
    (univalence-closed-under-constant 𝓐 𝓐' 𝓐'-ua)

univalence-closed-under-product : Fun-Ext
                                → (A : 𝓤' ̇) (𝓑 : A → Refl-Graph 𝓤 𝓥)
                                → ((x : A) → is-univalent-refl-graph (𝓑 x))
                                → is-univalent-refl-graph (∏ x ˸ A , (𝓑 x))
univalence-closed-under-product fe A 𝓑 𝓑-ua = III
 where
  I : (f : ⟨ ∏ x ˸ A , (𝓑 x) ⟩)
    → fan (∏ x ˸ A , (𝓑 x)) f ≃ ((x : A) → fan (𝓑 x) (f x))
  I f = fan (∏ x ˸ A , (𝓑 x)) f                                     ≃⟨refl⟩
        (Σ g ꞉ ⟨ ∏ x ˸ A , (𝓑 x) ⟩ , f ≈⟨ ∏ x ˸ A , (𝓑 x) ⟩ g)      ≃⟨refl⟩
        (Σ g ꞉ ⟨ ∏ x ˸ A , (𝓑 x) ⟩ , ((x : A) → f x ≈⟨ 𝓑 x ⟩ g x))  ≃⟨ II ⟩
        ((x : A) → Σ v ꞉ ⟨ 𝓑 x ⟩ , f x ≈⟨ 𝓑 x ⟩ v)                  ≃⟨refl⟩
        ((x : A) → fan (𝓑 x) (f x))                                 ■
   where
    II = ≃-sym ΠΣ-distr-≃
  III : (f : ⟨ ∏ x ˸ A , (𝓑 x) ⟩) → is-prop (fan (∏ x ˸ A , (𝓑 x)) f)
  III f = equiv-to-prop (I f) (Π-is-prop fe (λ x → 𝓑-ua x (f x)))

univalence-closed-under-cotensor : Fun-Ext
                                 → (A : 𝓤' ̇) (𝓑 : Refl-Graph 𝓤 𝓥)
                                 → is-univalent-refl-graph 𝓑
                                 → is-univalent-refl-graph (A ➙ 𝓑)
univalence-closed-under-cotensor fe A 𝓑 𝓑-ua
 = univalence-closed-under-product fe A (λ - → 𝓑) (λ - → 𝓑-ua)

univalence-closed-under-coproduct : (A : 𝓤' ̇) (𝓑 : A → Refl-Graph 𝓤 𝓥)
                                  → ((x : A) → is-univalent-refl-graph (𝓑 x))
                                  → is-univalent-refl-graph (∐ x ˸ A , (𝓑 x))
univalence-closed-under-coproduct A 𝓑 𝓑-ua (x , y)
 ((.x , y₀) , refl , q₀) ((.x , y₁) , refl , q₁)
 = I y₀ y₁ q₀ q₁ (𝓑-ua x y (y , ≈-refl (𝓑 x) y) (y₀ , q₀))
    (𝓑-ua x y (y , ≈-refl (𝓑 x) y) (y₁ , q₁))
 where
  I : (y' y'' : ⟨ 𝓑 x ⟩)
    → (q' : y ≈⟨ 𝓑 x ⟩ y')
    → (q'' : y ≈⟨ 𝓑 x ⟩ y'')
    → (y , ≈-refl (𝓑 x) y) ＝ (y' , q')
    → (y , ≈-refl (𝓑 x) y) ＝ (y'' , q'')
    → ((x , y') , (refl , q'))
     ＝[ fan (∐ x ˸ A , (𝓑 x)) (x , y) ] ((x , y'') , (refl , q''))
  I y' y'' q' q'' refl refl = refl

univalence-closed-under-tensor : (A : 𝓤' ̇) (𝓑 : Refl-Graph 𝓤 𝓥)
                               → is-univalent-refl-graph 𝓑
                               → is-univalent-refl-graph (∐ _ ˸ A , 𝓑)
univalence-closed-under-tensor A 𝓑 𝓑-ua
 = univalence-closed-under-coproduct A (λ - → 𝓑) (λ - → 𝓑-ua)

discrete-refl-graph-is-univalent
 : (A : 𝓤' ̇)
 → is-univalent-refl-graph (Δ A)
discrete-refl-graph-is-univalent A x
 = singletons-are-props (singleton-types-are-singletons x)

codiscrete-refl-graph-is-univalent-when-prop
 : (A : 𝓤' ̇)
 → is-prop A
 → is-univalent-refl-graph (codiscrete-reflexive-graph A)
codiscrete-refl-graph-is-univalent-when-prop A A-prop x (x' , ⋆) (y' , ⋆)
 = ap (λ - → (- , ⋆)) (A-prop x' y')

codiscrete-refl-graph-is-univalent-implies-prop
 : (A : 𝓤' ̇)
 → is-univalent-refl-graph (codiscrete-reflexive-graph A)
 → is-prop A
codiscrete-refl-graph-is-univalent-implies-prop A codis-A-ua x y
 = ap pr₁ (codis-A-ua x (x , ⋆) (y , ⋆))

univalence-closed-under-subgraph : (𝓐 : Refl-Graph 𝓤 𝓥) 
                                 → (S : 𝓟 {𝓣} ⟨ 𝓐 ⟩)
                                 → is-univalent-refl-graph 𝓐
                                 → is-univalent-refl-graph (x ∶ 𝓐 ∣ S x)
univalence-closed-under-subgraph 𝓐 S 𝓐-ua (x , s) ((x' , r) , p) ((y' , t) , q)
 = I (𝓐-ua x (x , ≈-refl 𝓐 x) (x' , p)) (𝓐-ua x (x , ≈-refl 𝓐 x) (y' , q))
 where
  I : ((x , ≈-refl 𝓐 x) ＝ (x' , p))
    → ((x , ≈-refl 𝓐 x) ＝ (y' , q))
    → ((x' , r) , p) ＝ ((y' , t) , q)
  I refl refl = ap (λ - → ((x , -) , ≈-refl 𝓐 x)) (∈-is-prop S x r t)

\end{code}

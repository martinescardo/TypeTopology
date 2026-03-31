Ian Ray. 28th August 2025.

Minor changes and merged into TypeToplogy in March 2026.

We observe some closure properties of univalent reflexive graphs
(see index for references to Sterling, Buchholtz, etc.)

\begin{code}

{-# OPTIONS --safe --without-K #-}

module ReflexiveGraphs.UnivalentClosureProperties where

open import MLTT.Spartan
open import UF.Base
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.FunExt
open import UF.PropIndexedPiSigma
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

Conceptually, showing that a total reflexive graph is univalent when the base
reflexive graph and the displayed reflexive graph over it are both univalent
is easy enough.

Let (x,y) be a term of ⟨ 𝓐 ﹐ 𝓑 ⟩, that is x : ⟨ 𝓐 ⟩ and y : ⟪ 𝓑 ⟫ x. By the
definition of univalence it suffices to show that any two fans of (x,y) are
equal. If we unpack the definition of a fan of the total reflexive graph 𝓐 ﹐ 𝓑
we get the following data:
terms x₀, x₁ : ⟨ 𝓐 ⟩ with edges p₀ : x ≈⟨ 𝓐 ⟩ x₀ and p₁ : x ≈⟨ 𝓐 ⟩ x₁ and terms
y₀ : ⟪ 𝓑 ⟫ x₀ and y₁ : ⟪ 𝓑 ⟫ x₁ with displayed edges q₀ : y ≈⟨ 𝓑 ⸴ p₀ ⟩ y₀ and
q₁ : y ≈⟨ 𝓑 ⸴ p₁ ⟩ y₁.
So we must show
 ((x₀ , y₀) , (p₀ , q₀)) ＝ ((x₁ , y₁) , (p₁ , q₁)).
As 𝓐 is univalent the edges p₀ and p₁ are contractible and it suffices to show
 ((x , y₀) , (≈-refl , q₀)) ＝ ((x , y₁) , (≈-refl , q₁)).
Now y₀ and y₁ are in the same fiber ⟪ 𝓑 ⟫ x so by univalence of 𝓑 the displayed
edges q₀ and q₁ are contractible and it suffices to show
 ((x , y) , (≈-refl , ≈-disp-refl)) ＝ ((x , y) , (≈-refl , ≈-disp-refl))
which holds by refl.

There are two important steps in this proof where we 'contract away' edges
using the univalence assumption, and the latter step depends on the former.
So we will record these steps in two lemmas. Note the essential use of the
file PropIndexedPiSigma.lagda.

\begin{code}

total-component-fans-prop-lemma
 : (𝓐 : Refl-Graph 𝓤 𝓥) (𝓑 : Displayed-Refl-Graph 𝓣 𝓦 𝓐)
 → is-displayed-univalent-refl-graph 𝓐 𝓑
 → (x : ⟨ 𝓐 ⟩) (y : ⟪ 𝓑 ⟫ x)
 → ((y₀ , q₀) (y₁ , q₁) : fan ([ 𝓑 ] x) y)
 → (((x , y₀) , (_ , q₀)) ＝[ fan (𝓐 ﹐ 𝓑) (x , y) ] ((x , y₁) , (_ , q₁)))
total-component-fans-prop-lemma 𝓐 𝓑 ua-𝓑 x y
 = Π-proj⁻¹ (y , ≈-refl ([ 𝓑 ] x) y) (ua-𝓑 x y)
    (Π-proj⁻¹ (y , ≈-refl ([ 𝓑 ] x) y) (ua-𝓑 x y) refl)

total-fans-prop-lemma
 : (𝓐 : Refl-Graph 𝓤 𝓥) (𝓑 : Displayed-Refl-Graph 𝓣 𝓦 𝓐)
 → is-univalent-refl-graph 𝓐
 → is-displayed-univalent-refl-graph 𝓐 𝓑
 → (x : ⟨ 𝓐 ⟩) (y : ⟪ 𝓑 ⟫ x)
 → ((x₀ , p₀) : fan 𝓐 x) ((x₁ , p₁) : fan 𝓐 x)
 → (y₀ : ⟪ 𝓑 ⟫ x₀) (q₀ : y ≈⟨ 𝓑 ⸴ p₀ ⟩ y₀)
 → (y₁ : ⟪ 𝓑 ⟫ x₁) (q₁ : y ≈⟨ 𝓑 ⸴ p₁ ⟩ y₁)
 → (((x₀ , y₀) , (p₀ , q₀)) ＝[ fan (𝓐 ﹐ 𝓑) (x , y) ] ((x₁ , y₁) , (p₁ , q₁)))
total-fans-prop-lemma 𝓐 𝓑 ua-𝓐 ua-𝓑 x y
 = Π-proj⁻¹ (x , ≈-refl 𝓐 x) (ua-𝓐 x)
    (Π-proj⁻¹ (x , ≈-refl 𝓐 x) (ua-𝓐 x)
     (λ y₀ q₀ y₁ q₁
       → total-component-fans-prop-lemma 𝓐 𝓑 ua-𝓑 x y (y₀ , q₀) (y₁ , q₁)))

univalence-closed-under-total
 : (𝓐 : Refl-Graph 𝓤 𝓥) (𝓑 : Displayed-Refl-Graph 𝓣 𝓦 𝓐)
 → is-univalent-refl-graph 𝓐
 → is-displayed-univalent-refl-graph 𝓐 𝓑
 → is-univalent-refl-graph (𝓐 ﹐ 𝓑)
univalence-closed-under-total 𝓐 𝓑 ua-𝓐 ua-𝓑
 (x , y) ((x₀ , y₀) , (p₀ , q₀)) ((x₁ , y₁) , (p₁ , q₁))
 = total-fans-prop-lemma 𝓐 𝓑 ua-𝓐 ua-𝓑 x y (x₀ , p₀) (x₁ , p₁) y₀ q₀ y₁ q₁

\end{code}

The remaining closure conditions are relatively straightforward.

\begin{code}

univalence-closed-under-opposite : (𝓐 : Refl-Graph 𝓤 𝓥)
                                 → is-univalent-refl-graph 𝓐
                                 → is-univalent-refl-graph (𝓐 ᵒᵖ)
univalence-closed-under-opposite 𝓐 𝓐-ua = prop-fan-to-cofan 𝓐 𝓐-ua

univalence-closed-under-opposite' : (𝓐 : Refl-Graph 𝓤 𝓥)
                                  → is-univalent-refl-graph (𝓐 ᵒᵖ)
                                  → is-univalent-refl-graph 𝓐
univalence-closed-under-opposite' 𝓐 = univalence-closed-under-opposite (𝓐 ᵒᵖ)

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
univalence-closed-under-binary-product 𝓐 𝓐' ua-𝓐 ua-𝓐'
 = univalence-closed-under-total 𝓐 (𝓐 * 𝓐') ua-𝓐
    (univalence-closed-under-constant 𝓐 𝓐' ua-𝓐')

univalence-closed-under-product : Fun-Ext
                                → (A : 𝓤' ̇) (𝓑 : A → Refl-Graph 𝓤 𝓥)
                                → ((x : A) → is-univalent-refl-graph (𝓑 x))
                                → is-univalent-refl-graph (∏ x ˸ A , (𝓑 x))
univalence-closed-under-product fe A 𝓑 ua-𝓑 = III
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
  III f = equiv-to-prop (I f) (Π-is-prop fe (λ x → ua-𝓑 x (f x)))

univalence-closed-under-cotensor : Fun-Ext
                                 → (A : 𝓤' ̇) (𝓑 : Refl-Graph 𝓤 𝓥)
                                 → is-univalent-refl-graph 𝓑
                                 → is-univalent-refl-graph (A ➙ 𝓑)
univalence-closed-under-cotensor fe A 𝓑 ua-𝓑
 = univalence-closed-under-product fe A (λ - → 𝓑) (λ - → ua-𝓑)

univalence-closed-under-coproduct : (A : 𝓤' ̇) (𝓑 : A → Refl-Graph 𝓤 𝓥)
                                  → ((x : A) → is-univalent-refl-graph (𝓑 x))
                                  → is-univalent-refl-graph (∐ x ˸ A , (𝓑 x))
univalence-closed-under-coproduct A 𝓑 ua-𝓑 (x , y)
 ((.x , y₀) , refl , q₀) ((.x , y₁) , refl , q₁)
 = II (y₀ , q₀) (y₁ , q₁)
 where
  I = fan (∐ x ˸ A , (𝓑 x)) (x , y)
  II : ((y' , q') (y'' , q'') : fan (𝓑 x) y)
     → ((x , y') , (refl , q')) ＝[ I ] ((x , y'') , (refl , q''))
  II = Π-proj⁻¹ (y , ≈-refl (𝓑 x) y) (ua-𝓑 x y)
        (Π-proj⁻¹ (y , ≈-refl (𝓑 x) y) (ua-𝓑 x y) refl)

univalence-closed-under-tensor : (A : 𝓤' ̇) (𝓑 : Refl-Graph 𝓤 𝓥)
                               → is-univalent-refl-graph 𝓑
                               → is-univalent-refl-graph (∐ _ ˸ A , 𝓑)
univalence-closed-under-tensor A 𝓑 ua-𝓑
 = univalence-closed-under-coproduct A (λ - → 𝓑) (λ - → ua-𝓑)

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
codiscrete-refl-graph-is-univalent-implies-prop A ua-codis-A x y
 = ap pr₁ (ua-codis-A x (x , ⋆) (y , ⋆))

univalence-closed-under-subgraph : (𝓐 : Refl-Graph 𝓤 𝓥) 
                                 → (S : 𝓟 {𝓣} ⟨ 𝓐 ⟩)
                                 → is-univalent-refl-graph 𝓐
                                 → is-univalent-refl-graph (x ∶ 𝓐 ∣ S x)
univalence-closed-under-subgraph 𝓐 S ua-𝓐 (x , s) ((x' , r) , p) ((y' , t) , q)
 = I (ua-𝓐 x (x , ≈-refl 𝓐 x) (x' , p)) (ua-𝓐 x (x , ≈-refl 𝓐 x) (y' , q))
 where
  I : ((x , ≈-refl 𝓐 x) ＝ (x' , p))
    → ((x , ≈-refl 𝓐 x) ＝ (y' , q))
    → ((x' , r) , p) ＝ ((y' , t) , q)
  I refl refl = ap (λ - → ((x , -) , ≈-refl 𝓐 x)) (∈-is-prop S x r t)

\end{code}
